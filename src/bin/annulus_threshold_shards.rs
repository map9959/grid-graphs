use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

use grid_graphs::exact_centered_square::{StreamingSquare, StreamingSquareState};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

const SHARDS: usize = 256;
const STATE_BYTES: usize = 48;
const RECORD_BYTES: usize = STATE_BYTES + 2;
const FNV_OFFSET: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct Record([u8; RECORD_BYTES]);

impl Record {
    fn new(state: StreamingSquareState, row_u: u16) -> Self {
        let mut bytes = [0; RECORD_BYTES];
        bytes[..STATE_BYTES].copy_from_slice(&state.canonical_bytes());
        bytes[STATE_BYTES..].copy_from_slice(&row_u.to_le_bytes());
        Self(bytes)
    }

    fn state(self) -> StreamingSquareState {
        StreamingSquareState::from_canonical_bytes(self.0[..STATE_BYTES].try_into().unwrap())
    }

    fn row_u(self) -> u16 {
        u16::from_le_bytes(self.0[STATE_BYTES..].try_into().unwrap())
    }

    fn shard(self) -> usize {
        (fnv64(&self.0) & 255) as usize
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct ShardStats {
    shard: usize,
    records: u64,
    bytes: u64,
    fnv1a64: String,
    runs: usize,
}

#[derive(Debug, Deserialize, Serialize)]
struct PhaseManifest {
    schema: String,
    side: usize,
    completed_positions: usize,
    shards: usize,
    source_records: u64,
    emitted_successors: u64,
    unique_records: u64,
    duplicate_records: u64,
    shard_stats: Vec<ShardStats>,
    complete: bool,
}

fn fnv64(bytes: &[u8]) -> u64 {
    bytes.iter().fold(FNV_OFFSET, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(FNV_PRIME)
    })
}

fn read_record(reader: &mut impl Read) -> Result<Option<Record>, String> {
    let mut bytes = [0; RECORD_BYTES];
    let mut read = 0;
    while read < RECORD_BYTES {
        let count = reader
            .read(&mut bytes[read..])
            .map_err(|error| error.to_string())?;
        if count == 0 {
            if read == 0 {
                return Ok(None);
            }
            return Err(format!(
                "truncated fixed record at byte {read}/{RECORD_BYTES}"
            ));
        }
        read += count;
    }
    Ok(Some(Record(bytes)))
}

fn write_records(path: &Path, records: &[Record]) -> Result<(), String> {
    let mut writer = BufWriter::new(File::create(path).map_err(|error| error.to_string())?);
    for record in records {
        writer
            .write_all(&record.0)
            .map_err(|error| error.to_string())?;
    }
    writer.flush().map_err(|error| error.to_string())
}

fn sort_shard(spool: &Path, output: &Path, memory_bytes: usize) -> Result<ShardStats, String> {
    let shard = output
        .file_stem()
        .and_then(|name| name.to_str())
        .and_then(|name| name.strip_prefix("shard-"))
        .and_then(|value| value.parse().ok())
        .ok_or("invalid shard output name")?;
    let run_dir = output.with_extension("runs");
    fs::create_dir_all(&run_dir).map_err(|error| error.to_string())?;
    let chunk_records = (memory_bytes / RECORD_BYTES).max(1);
    let mut reader = BufReader::new(File::open(spool).map_err(|error| error.to_string())?);
    let mut run_paths = Vec::new();
    loop {
        let mut records = Vec::with_capacity(chunk_records);
        while records.len() < chunk_records {
            let Some(record) = read_record(&mut reader)? else {
                break;
            };
            records.push(record);
        }
        if records.is_empty() {
            break;
        }
        records.sort_unstable();
        records.dedup();
        let path = run_dir.join(format!("run-{:05}.bin", run_paths.len()));
        write_records(&path, &records)?;
        run_paths.push(path);
    }

    let mut readers: Vec<_> = run_paths
        .iter()
        .map(|path| File::open(path).map(BufReader::new))
        .collect::<Result<_, _>>()
        .map_err(|error| error.to_string())?;
    let mut heap = BinaryHeap::new();
    for (index, reader) in readers.iter_mut().enumerate() {
        if let Some(record) = read_record(reader)? {
            heap.push((Reverse(record), Reverse(index)));
        }
    }
    let mut writer = BufWriter::new(File::create(output).map_err(|error| error.to_string())?);
    let mut previous = None;
    let mut records = 0u64;
    let mut digest = FNV_OFFSET;
    while let Some((Reverse(record), Reverse(index))) = heap.pop() {
        if previous != Some(record) {
            writer
                .write_all(&record.0)
                .map_err(|error| error.to_string())?;
            for byte in record.0 {
                digest = (digest ^ u64::from(byte)).wrapping_mul(FNV_PRIME);
            }
            previous = Some(record);
            records += 1;
        }
        if let Some(next) = read_record(&mut readers[index])? {
            heap.push((Reverse(next), Reverse(index)));
        }
    }
    writer.flush().map_err(|error| error.to_string())?;
    fs::remove_dir_all(&run_dir).map_err(|error| error.to_string())?;
    Ok(ShardStats {
        shard,
        records,
        bytes: records * RECORD_BYTES as u64,
        fnv1a64: format!("{digest:016x}"),
        runs: run_paths.len(),
    })
}

fn verify_phase(path: &Path, manifest: &PhaseManifest) -> Result<(), String> {
    if !manifest.complete || manifest.shards != SHARDS {
        return Err("phase manifest is incomplete or has the wrong shard count".into());
    }
    let mut total = 0u64;
    for expected in &manifest.shard_stats {
        let shard_path = path.join(format!("shard-{:03}.bin", expected.shard));
        let bytes = fs::read(&shard_path).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != expected.bytes
            || fnv64(&bytes) != u64::from_str_radix(&expected.fnv1a64, 16).unwrap()
        {
            return Err(format!("shard {} size or digest mismatch", expected.shard));
        }
        if bytes.len() % RECORD_BYTES != 0 {
            return Err(format!("shard {} has a partial record", expected.shard));
        }
        let records: Vec<_> = bytes
            .chunks_exact(RECORD_BYTES)
            .map(|chunk| Record(chunk.try_into().unwrap()))
            .collect();
        if !records.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(format!("shard {} is not strictly sorted", expected.shard));
        }
        if records
            .iter()
            .any(|record| record.shard() != expected.shard)
        {
            return Err(format!(
                "shard {} contains a misrouted record",
                expected.shard
            ));
        }
        total += records.len() as u64;
    }
    if total != manifest.unique_records {
        return Err(format!(
            "phase total {total} != {}",
            manifest.unique_records
        ));
    }
    Ok(())
}

fn load_manifest(path: &Path) -> Result<PhaseManifest, String> {
    serde_json::from_reader(BufReader::new(
        File::open(path.join("manifest.json")).map_err(|error| error.to_string())?,
    ))
    .map_err(|error| error.to_string())
}

fn initialize(root: &Path, side: usize) -> Result<(), String> {
    let phase = root.join("phase-00");
    if phase.exists() {
        return verify_phase(&phase, &load_manifest(&phase)?);
    }
    fs::create_dir_all(&phase).map_err(|error| error.to_string())?;
    let stream = StreamingSquare::new(side)?;
    let record = Record::new(stream.initial_state(), 0);
    let mut stats = Vec::with_capacity(SHARDS);
    for shard in 0..SHARDS {
        let path = phase.join(format!("shard-{shard:03}.bin"));
        if shard == record.shard() {
            write_records(&path, &[record])?;
        } else {
            File::create(&path).map_err(|error| error.to_string())?;
        }
        let bytes = fs::read(&path).map_err(|error| error.to_string())?;
        stats.push(ShardStats {
            shard,
            records: u64::from(shard == record.shard()),
            bytes: bytes.len() as u64,
            fnv1a64: format!("{:016x}", fnv64(&bytes)),
            runs: 1,
        });
    }
    let manifest = PhaseManifest {
        schema: "grid_graphs.annulus_external_phase.v1".into(),
        side,
        completed_positions: 0,
        shards: SHARDS,
        source_records: 0,
        emitted_successors: 0,
        unique_records: 1,
        duplicate_records: 0,
        shard_stats: stats,
        complete: true,
    };
    serde_json::to_writer_pretty(
        BufWriter::new(
            File::create(phase.join("manifest.json")).map_err(|error| error.to_string())?,
        ),
        &manifest,
    )
    .map_err(|error| error.to_string())
}

fn advance_phase(
    root: &Path,
    side: usize,
    position: usize,
    memory_mib: usize,
    workers: usize,
) -> Result<(), String> {
    let source_dir = root.join(format!("phase-{position:02}"));
    let source_manifest = load_manifest(&source_dir)?;
    verify_phase(&source_dir, &source_manifest)?;
    let destination_dir = root.join(format!("phase-{:02}", position + 1));
    if destination_dir.exists() {
        return verify_phase(&destination_dir, &load_manifest(&destination_dir)?);
    }
    let temporary = root.join(format!("phase-{:02}.tmp", position + 1));
    if temporary.exists() {
        fs::remove_dir_all(&temporary).map_err(|error| error.to_string())?;
    }
    fs::create_dir_all(&temporary).map_err(|error| error.to_string())?;
    let spool_dir = temporary.join("spool");
    fs::create_dir_all(&spool_dir).map_err(|error| error.to_string())?;
    let mut writers: Vec<_> = (0..SHARDS)
        .map(|shard| {
            OpenOptions::new()
                .create(true)
                .append(true)
                .open(spool_dir.join(format!("shard-{shard:03}.bin")))
                .map(BufWriter::new)
        })
        .collect::<Result<_, _>>()
        .map_err(|error| error.to_string())?;
    let stream = StreamingSquare::new(side)?;
    let col = position % side;
    let mut source_records = 0u64;
    for shard in 0..SHARDS {
        let mut reader = BufReader::new(
            File::open(source_dir.join(format!("shard-{shard:03}.bin")))
                .map_err(|error| error.to_string())?,
        );
        while let Some(record) = read_record(&mut reader)? {
            source_records += 1;
            for chosen in [false, true] {
                let state = stream.advance(record.state(), position, chosen, record.row_u())?;
                let mut row_u = record.row_u();
                if chosen {
                    row_u |= 1 << col;
                } else {
                    row_u &= !(1 << col);
                }
                let successor = Record::new(state, row_u);
                writers[successor.shard()]
                    .write_all(&successor.0)
                    .map_err(|error| error.to_string())?;
            }
        }
    }
    for writer in &mut writers {
        writer.flush().map_err(|error| error.to_string())?;
    }
    drop(writers);

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build()
        .map_err(|error| error.to_string())?;
    let per_worker_bytes = memory_mib * 1024 * 1024 / workers.max(1);
    let results: Vec<_> = pool.install(|| {
        (0..SHARDS)
            .into_par_iter()
            .map(|shard| {
                sort_shard(
                    &spool_dir.join(format!("shard-{shard:03}.bin")),
                    &temporary.join(format!("shard-{shard:03}.bin")),
                    per_worker_bytes,
                )
            })
            .collect()
    });
    let mut stats: Vec<_> = results.into_iter().collect::<Result<_, _>>()?;
    stats.sort_by_key(|item| item.shard);
    fs::remove_dir_all(&spool_dir).map_err(|error| error.to_string())?;
    let unique_records: u64 = stats.iter().map(|item| item.records).sum();
    let emitted_successors = source_records * 2;
    let manifest = PhaseManifest {
        schema: "grid_graphs.annulus_external_phase.v1".into(),
        side,
        completed_positions: position + 1,
        shards: SHARDS,
        source_records,
        emitted_successors,
        unique_records,
        duplicate_records: emitted_successors - unique_records,
        shard_stats: stats,
        complete: true,
    };
    serde_json::to_writer_pretty(
        BufWriter::new(
            File::create(temporary.join("manifest.json")).map_err(|error| error.to_string())?,
        ),
        &manifest,
    )
    .map_err(|error| error.to_string())?;
    verify_phase(&temporary, &manifest)?;
    fs::rename(&temporary, &destination_dir).map_err(|error| error.to_string())?;
    println!(
        "EXTERNAL_PHASE completed={} source={} emitted={} unique={} duplicates={}",
        position + 1,
        source_records,
        emitted_successors,
        unique_records,
        emitted_successors - unique_records
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let mut root = PathBuf::from("analysis/annulus-side7-work");
    let mut side = 7usize;
    let mut through = 49usize;
    let mut memory_mib = 2048usize;
    let mut workers = 8usize;
    let args: Vec<_> = env::args().skip(1).collect();
    let mut at = 0;
    while at < args.len() {
        let value = args.get(at + 1).ok_or("option requires a value")?;
        match args[at].as_str() {
            "--root" => root = PathBuf::from(value),
            "--side" => side = value.parse().map_err(|_| "invalid --side")?,
            "--through" => through = value.parse().map_err(|_| "invalid --through")?,
            "--memory-mib" => memory_mib = value.parse().map_err(|_| "invalid --memory-mib")?,
            "--workers" => workers = value.parse().map_err(|_| "invalid --workers")?,
            option => return Err(format!("unknown option {option:?}")),
        }
        at += 2;
    }
    if through > side * side || workers == 0 || memory_mib < workers {
        return Err("invalid through/memory/workers configuration".into());
    }
    fs::create_dir_all(&root).map_err(|error| error.to_string())?;
    initialize(&root, side)?;
    for position in 0..through {
        advance_phase(&root, side, position, memory_mib, workers)?;
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn external_pipeline_matches_side_three_census_and_resumes() {
        let root =
            env::temp_dir().join(format!("grid-graphs-annulus-shards-{}", std::process::id()));
        if root.exists() {
            fs::remove_dir_all(&root).unwrap();
        }
        initialize(&root, 3).unwrap();
        for position in 0..9 {
            advance_phase(&root, 3, position, 16, 2).unwrap();
        }
        let expected = [1, 2, 4, 8, 14, 25, 43, 78, 133, 220];
        for (position, expected) in expected.into_iter().enumerate() {
            let phase = root.join(format!("phase-{position:02}"));
            let manifest = load_manifest(&phase).unwrap();
            verify_phase(&phase, &manifest).unwrap();
            assert_eq!(manifest.unique_records, expected);
            if position > 0 {
                assert_eq!(manifest.emitted_successors, 2 * manifest.source_records);
                assert_eq!(
                    manifest.emitted_successors,
                    manifest.unique_records + manifest.duplicate_records
                );
            }
        }
        // Existing complete phases are verified rather than regenerated.
        advance_phase(&root, 3, 8, 16, 2).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
}
