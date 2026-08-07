//! Exact connectivity words on perimeters of centered primal squares.

use serde::Serialize;

const STREAM_LABEL_BITS: usize = 6;
const STREAM_EMPTY: u8 = (1 << STREAM_LABEL_BITS) - 1;
const STREAM_MAX_SLOTS: usize = 11;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CompressedRun {
    pub token: String,
    pub length: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct PortWordSummary {
    pub canonical_word: Vec<usize>,
    pub repeated_components: usize,
    pub maximum_cyclic_runs_per_component: usize,
    pub compressed_tokens: Vec<String>,
    pub compressed_runs: Vec<CompressedRun>,
    pub compressed_linear_run_count: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CenteredSquareProfile {
    pub side: usize,
    pub port_word: PortWordSummary,
}

/// A complete square U-pattern, with column zero stored in the low bit of each row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CenteredSquareMonitor {
    n: usize,
    row_masks: Vec<u128>,
}

/// Canonical exact state for a row-major stream through a square of side at most 11.
///
/// `frontier` retains only components incident with an unprocessed local edge. `ports`
/// retains the component label at every encountered perimeter edge, so a component
/// remains represented after its last active face is forgotten.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StreamingSquareState {
    frontier: u128,
    ports: [u128; 2],
}

#[derive(Clone, Copy)]
enum StreamNeighbor {
    Left,
    Up,
}

#[derive(Clone, Copy)]
struct StreamEdge {
    faces: [Option<usize>; 2],
    face_slots: [u8; 2],
    face_count: u8,
    neighbor: StreamNeighbor,
    port: Option<usize>,
}

struct StreamStep {
    col: usize,
    before: Vec<usize>,
    node_count: usize,
    after_indices: Vec<usize>,
    edges: Vec<StreamEdge>,
}

/// Transition table for [`StreamingSquareState`]. Interior face geometry is used only
/// here to construct the fixed schedule; it is never retained in a state key.
pub struct StreamingSquare {
    side: usize,
    steps: Vec<StreamStep>,
}

impl StreamingSquareState {
    pub fn canonical_bytes(self) -> [u8; 48] {
        let mut bytes = [0; 48];
        bytes[..16].copy_from_slice(&self.frontier.to_le_bytes());
        bytes[16..32].copy_from_slice(&self.ports[0].to_le_bytes());
        bytes[32..].copy_from_slice(&self.ports[1].to_le_bytes());
        bytes
    }

    pub fn from_canonical_bytes(bytes: [u8; 48]) -> Self {
        let word = |start| u128::from_le_bytes(bytes[start..start + 16].try_into().unwrap());
        Self {
            frontier: word(0),
            ports: [word(16), word(32)],
        }
    }

    pub fn completed_port_masks(&self, side: usize) -> Vec<u64> {
        let active: Vec<_> = (0..STREAM_MAX_SLOTS)
            .map(|slot| unpack_field(&[self.frontier, 0], slot))
            .filter(|&label| label != STREAM_EMPTY)
            .collect();
        component_port_masks(self, side)
            .into_iter()
            .enumerate()
            .filter_map(|(label, mask)| (!active.contains(&(label as u8))).then_some(mask))
            .filter(|&mask| mask != 0)
            .collect()
    }
}

impl StreamingSquare {
    pub fn new(side: usize) -> Result<Self, String> {
        if !(2..=11).contains(&side) {
            return Err("streaming square side must be in 2..=11".into());
        }
        let face_side = side - 1;
        let face_count = face_side * face_side;
        let face = |row: usize, col: usize| row * face_side + col;
        let mut batches = vec![Vec::new(); side * side];
        for row in 0..side {
            for col in 0..side {
                if col > 0 {
                    let faces = [
                        (row > 0).then(|| face(row - 1, col - 1)),
                        (row + 1 < side).then(|| face(row, col - 1)),
                    ];
                    let port = if row == 0 {
                        Some(col - 1)
                    } else if row + 1 == side {
                        Some(3 * face_side - col)
                    } else {
                        None
                    };
                    batches[row * side + col].push(StreamEdge {
                        faces,
                        face_slots: [0; 2],
                        face_count: 0,
                        neighbor: StreamNeighbor::Left,
                        port,
                    });
                }
                if row > 0 {
                    let faces = [
                        (col > 0).then(|| face(row - 1, col - 1)),
                        (col + 1 < side).then(|| face(row - 1, col)),
                    ];
                    let port = if col + 1 == side {
                        Some(face_side + row - 1)
                    } else if col == 0 {
                        Some(4 * face_side - row)
                    } else {
                        None
                    };
                    batches[row * side + col].push(StreamEdge {
                        faces,
                        face_slots: [0; 2],
                        face_count: 0,
                        neighbor: StreamNeighbor::Up,
                        port,
                    });
                }
            }
        }

        let mut first = vec![usize::MAX; face_count];
        let mut last = vec![0; face_count];
        for (at, edges) in batches.iter().enumerate() {
            for edge in edges {
                for node in edge.faces.into_iter().flatten() {
                    first[node] = first[node].min(at);
                    last[node] = last[node].max(at);
                }
            }
        }
        let mut steps = Vec::with_capacity(side * side);
        for (at, mut edges) in batches.into_iter().enumerate() {
            let before: Vec<_> = (0..face_count)
                .filter(|&node| first[node] < at && last[node] >= at)
                .collect();
            let after: Vec<_> = (0..face_count)
                .filter(|&node| first[node] <= at && last[node] > at)
                .collect();
            let mut nodes = before.clone();
            for edge in &edges {
                for node in edge.faces.into_iter().flatten() {
                    if !nodes.contains(&node) {
                        nodes.push(node);
                    }
                }
            }
            if before.len().max(after.len()) > STREAM_MAX_SLOTS {
                return Err("streaming square frontier exceeds packed capacity".into());
            }
            for edge in &mut edges {
                for (index, face) in edge.faces.into_iter().flatten().enumerate() {
                    edge.face_slots[index] =
                        nodes.iter().position(|&node| node == face).unwrap() as u8;
                    edge.face_count += 1;
                }
            }
            let after_indices = after
                .iter()
                .map(|node| {
                    nodes
                        .iter()
                        .position(|candidate| candidate == node)
                        .unwrap()
                })
                .collect();
            steps.push(StreamStep {
                col: at % side,
                before,
                node_count: nodes.len(),
                after_indices,
                edges,
            });
        }
        Ok(Self { side, steps })
    }

    pub fn initial_state(&self) -> StreamingSquareState {
        StreamingSquareState {
            frontier: u128::MAX,
            ports: [u128::MAX; 2],
        }
    }

    pub fn advance(
        &self,
        state: StreamingSquareState,
        position: usize,
        chosen: bool,
        row_u: u16,
    ) -> Result<StreamingSquareState, String> {
        let step = self
            .steps
            .get(position)
            .ok_or_else(|| format!("stream position {position} is outside the square"))?;
        let mut labels = [STREAM_EMPTY; STREAM_MAX_SLOTS + 2];
        for slot in 0..step.before.len() {
            labels[slot] = unpack_field(&[state.frontier, 0], slot);
        }
        let mut next_label = labels
            .iter()
            .copied()
            .filter(|&label| label != STREAM_EMPTY)
            .chain((0..4 * (self.side - 1)).filter_map(|port| {
                let label = unpack_field(&state.ports, port);
                (label != STREAM_EMPTY).then_some(label)
            }))
            .max()
            .map_or(0, |label| label + 1);
        for slot in step.before.len()..step.node_count {
            labels[slot] = next_label;
            next_label += 1;
        }
        if next_label as usize >= STREAM_EMPTY as usize {
            return Err("streaming square exhausted component labels".into());
        }

        let mut parent: [u8; STREAM_EMPTY as usize] = std::array::from_fn(|index| index as u8);
        let mut ports = state.ports;
        for edge in &step.edges {
            let neighbor_chosen = match edge.neighbor {
                StreamNeighbor::Left => row_u & (1 << (step.col - 1)) != 0,
                StreamNeighbor::Up => row_u & (1 << step.col) != 0,
            };
            if !chosen || !neighbor_chosen {
                continue;
            }
            if let Some(port) = edge.port {
                debug_assert_eq!(edge.face_count, 1);
                pack_field(&mut ports, port, labels[edge.face_slots[0] as usize]);
            } else {
                debug_assert_eq!(edge.face_count, 2);
                union_labels(
                    &mut parent,
                    labels[edge.face_slots[0] as usize],
                    labels[edge.face_slots[1] as usize],
                );
            }
        }
        for port in 0..4 * (self.side - 1) {
            let label = unpack_field(&ports, port);
            if label != STREAM_EMPTY {
                pack_field(&mut ports, port, find_label(&mut parent, label));
            }
        }
        let mut renaming = [STREAM_EMPTY; STREAM_EMPTY as usize];
        let mut canonical_count = 0u8;
        for port in 0..4 * (self.side - 1) {
            let old = unpack_field(&ports, port);
            if old != STREAM_EMPTY {
                let canonical = canonical_label(&mut renaming, &mut canonical_count, old);
                pack_field(&mut ports, port, canonical);
            }
        }
        let mut frontier = u128::MAX;
        for (slot, &old_slot) in step.after_indices.iter().enumerate() {
            let old = find_label(&mut parent, labels[old_slot]);
            let canonical = canonical_label(&mut renaming, &mut canonical_count, old);
            pack_frontier_field(&mut frontier, slot, canonical);
        }
        Ok(StreamingSquareState { frontier, ports })
    }

    pub fn port_word(&self, state: &StreamingSquareState) -> Vec<usize> {
        (0..4 * (self.side - 1))
            .filter_map(|port| {
                let label = unpack_field(&state.ports, port);
                (label != STREAM_EMPTY).then_some(label as usize)
            })
            .collect()
    }

    pub fn summary(&self, state: &StreamingSquareState) -> PortWordSummary {
        summarize_port_word(&self.port_word(state))
    }
}

fn unpack_field(words: &[u128; 2], index: usize) -> u8 {
    let bit = index * STREAM_LABEL_BITS;
    let word = bit / 128;
    let shift = bit % 128;
    if shift <= 128 - STREAM_LABEL_BITS {
        ((words[word] >> shift) & 63) as u8
    } else {
        let low = words[word] >> shift;
        let high = words[word + 1] << (128 - shift);
        ((low | high) & 63) as u8
    }
}

fn pack_field(words: &mut [u128; 2], index: usize, value: u8) {
    let bit = index * STREAM_LABEL_BITS;
    let word = bit / 128;
    let shift = bit % 128;
    words[word] &= !(63u128 << shift);
    words[word] |= (value as u128) << shift;
    if shift > 128 - STREAM_LABEL_BITS {
        let high_bits = STREAM_LABEL_BITS - (128 - shift);
        words[word + 1] &= !((1u128 << high_bits) - 1);
        words[word + 1] |= (value as u128) >> (128 - shift);
    }
}

fn pack_frontier_field(word: &mut u128, index: usize, value: u8) {
    let shift = index * STREAM_LABEL_BITS;
    *word &= !(63u128 << shift);
    *word |= (value as u128) << shift;
}

fn find_label(parent: &mut [u8], mut label: u8) -> u8 {
    while parent[label as usize] != label {
        parent[label as usize] = parent[parent[label as usize] as usize];
        label = parent[label as usize];
    }
    label
}

fn union_labels(parent: &mut [u8], left: u8, right: u8) {
    let left = find_label(parent, left);
    let right = find_label(parent, right);
    if left != right {
        parent[right as usize] = left;
    }
}

fn canonical_label(renaming: &mut [u8], count: &mut u8, old: u8) -> u8 {
    if renaming[old as usize] == STREAM_EMPTY {
        renaming[old as usize] = *count;
        *count += 1;
    }
    renaming[old as usize]
}

fn component_port_masks(state: &StreamingSquareState, side: usize) -> Vec<u64> {
    let mut masks = Vec::new();
    for port in 0..4 * (side - 1) {
        let label = unpack_field(&state.ports, port);
        if label != STREAM_EMPTY {
            if masks.len() <= label as usize {
                masks.resize(label as usize + 1, 0);
            }
            masks[label as usize] |= 1 << port;
        }
    }
    masks
}

impl CenteredSquareMonitor {
    pub fn from_row_masks(
        n: usize,
        row_masks: impl IntoIterator<Item = u128>,
    ) -> Result<Self, String> {
        if n == 0 || n > u128::BITS as usize {
            return Err(format!("pattern side must be in 1..={}", u128::BITS));
        }
        let row_masks: Vec<_> = row_masks.into_iter().collect();
        if row_masks.len() != n {
            return Err(format!(
                "pattern has {} row masks, expected {n}",
                row_masks.len()
            ));
        }
        let valid_bits = if n == u128::BITS as usize {
            u128::MAX
        } else {
            (1u128 << n) - 1
        };
        if let Some((row, mask)) = row_masks
            .iter()
            .enumerate()
            .find(|(_, mask)| **mask & !valid_bits != 0)
        {
            return Err(format!(
                "row {row} mask 0x{mask:x} has bits beyond column {}",
                n - 1
            ));
        }
        Ok(Self { n, row_masks })
    }

    /// Parses a square pattern. Blank lines and lines beginning with `#` are ignored.
    pub fn parse(pattern: &str) -> Result<Self, String> {
        let rows: Vec<_> = pattern
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect();
        let n = rows.len();
        if n == 0 {
            return Err("pattern contains no rows".into());
        }
        if n > u128::BITS as usize {
            return Err(format!("pattern side must be at most {}", u128::BITS));
        }
        let mut masks = Vec::with_capacity(n);
        for (row, line) in rows.into_iter().enumerate() {
            if line.len() != n {
                return Err(format!(
                    "pattern row {row} has width {}, expected {n}",
                    line.len()
                ));
            }
            let mut mask = 0u128;
            for (column, value) in line.bytes().enumerate() {
                match value {
                    b'U' => mask |= 1u128 << column,
                    b'.' => {}
                    _ => {
                        return Err(format!(
                            "pattern row {row}, column {column} is not `U` or `.`"
                        ));
                    }
                }
            }
            masks.push(mask);
        }
        Self::from_row_masks(n, masks)
    }

    pub fn side(&self) -> usize {
        self.n
    }

    /// Returns all centered prefixes in the same order and parity as the Python analysis.
    pub fn profiles(&self) -> Vec<CenteredSquareProfile> {
        let first = if self.n % 2 == 0 { 2 } else { 3 };
        (first..=self.n)
            .step_by(2)
            .map(|side| {
                self.profile(side)
                    .expect("generated centered side is valid")
            })
            .collect()
    }

    pub fn profile(&self, side: usize) -> Result<CenteredSquareProfile, String> {
        if side < 2 || side > self.n || side % 2 != self.n % 2 {
            return Err(format!(
                "centered side must be in 2..={} and have the pattern's parity",
                self.n
            ));
        }
        let offset = (self.n - side) / 2;
        let face_side = side - 1;
        let mut dsu = Dsu::new(face_side * face_side);
        let face = |row: usize, column: usize| row * face_side + column;
        let chosen = |row: usize, column: usize| {
            self.row_masks[offset + row] & (1u128 << (offset + column)) != 0
        };

        // Perimeter primal edges are ports, so only non-perimeter primal edges join faces here.
        for row in 1..side - 1 {
            for column in 0..side - 1 {
                if chosen(row, column) && chosen(row, column + 1) {
                    dsu.union(face(row - 1, column), face(row, column));
                }
            }
        }
        for row in 0..side - 1 {
            for column in 1..side - 1 {
                if chosen(row, column) && chosen(row + 1, column) {
                    dsu.union(face(row, column - 1), face(row, column));
                }
            }
        }

        let mut roots = Vec::new();
        for column in 0..side - 1 {
            if chosen(0, column) && chosen(0, column + 1) {
                roots.push(dsu.find(face(0, column)));
            }
        }
        for row in 0..side - 1 {
            if chosen(row, side - 1) && chosen(row + 1, side - 1) {
                roots.push(dsu.find(face(row, side - 2)));
            }
        }
        for column in (0..side - 1).rev() {
            if chosen(side - 1, column) && chosen(side - 1, column + 1) {
                roots.push(dsu.find(face(side - 2, column)));
            }
        }
        for row in (0..side - 1).rev() {
            if chosen(row, 0) && chosen(row + 1, 0) {
                roots.push(dsu.find(face(row, 0)));
            }
        }

        Ok(CenteredSquareProfile {
            side,
            port_word: summarize_port_word(&roots),
        })
    }
}

/// Canonicalizes arbitrary component labels by first occurrence and computes the exact metrics.
pub fn summarize_port_word(word: &[usize]) -> PortWordSummary {
    let mut observed = Vec::new();
    let canonical_word: Vec<_> = word
        .iter()
        .map(
            |label| match observed.iter().position(|seen| seen == label) {
                Some(index) => index,
                None => {
                    observed.push(*label);
                    observed.len() - 1
                }
            },
        )
        .collect();
    let mut counts = vec![0usize; observed.len()];
    for &label in &canonical_word {
        counts[label] += 1;
    }
    let repeated_components = counts.iter().filter(|&&count| count > 1).count();
    let maximum_cyclic_runs_per_component = counts
        .iter()
        .enumerate()
        .filter(|(_, count)| **count != 0)
        .map(|(label, _)| {
            canonical_word
                .iter()
                .enumerate()
                .filter(|&(index, &value)| {
                    value == label
                        && canonical_word[(index + canonical_word.len() - 1) % canonical_word.len()]
                            != label
                })
                .count()
                .max(1)
        })
        .max()
        .unwrap_or(0);

    let mut repeated_names = vec![None; counts.len()];
    let mut next_repeated = 0usize;
    let compressed_tokens: Vec<_> = canonical_word
        .iter()
        .map(|&label| {
            if counts[label] == 1 {
                "S".to_owned()
            } else {
                let name = *repeated_names[label].get_or_insert_with(|| {
                    let name = next_repeated;
                    next_repeated += 1;
                    name
                });
                format!("R{name}")
            }
        })
        .collect();
    let mut compressed_runs: Vec<CompressedRun> = Vec::new();
    for token in &compressed_tokens {
        if let Some(run) = compressed_runs.last_mut().filter(|run| run.token == *token) {
            run.length += 1;
        } else {
            compressed_runs.push(CompressedRun {
                token: token.clone(),
                length: 1,
            });
        }
    }
    PortWordSummary {
        canonical_word,
        repeated_components,
        maximum_cyclic_runs_per_component,
        compressed_tokens,
        compressed_linear_run_count: compressed_runs.len(),
        compressed_runs,
    }
}

struct Dsu {
    parent: Vec<usize>,
}

impl Dsu {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
        }
    }

    fn find(&mut self, mut value: usize) -> usize {
        while self.parent[value] != value {
            self.parent[value] = self.parent[self.parent[value]];
            value = self.parent[value];
        }
        value
    }

    fn union(&mut self, left: usize, right: usize) {
        let left = self.find(left);
        let right = self.find(right);
        if left != right {
            self.parent[right] = left;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn streaming_summary(stream: &StreamingSquare, mask: u32) -> PortWordSummary {
        let side = stream.side;
        let mut state = stream.initial_state();
        let mut row_u = 0u16;
        for position in 0..side * side {
            let col = position % side;
            let chosen = mask & (1 << position) != 0;
            state = stream.advance(state, position, chosen, row_u).unwrap();
            if chosen {
                row_u |= 1 << col;
            } else {
                row_u &= !(1 << col);
            }
        }
        assert!(state.completed_port_masks(side).len() <= 4 * (side - 1));
        stream.summary(&state)
    }

    fn terminal_summary(side: usize, mask: u32) -> PortWordSummary {
        let row_mask = (1u128 << side) - 1;
        let rows = (0..side).map(|row| ((mask as u128) >> (row * side)) & row_mask);
        CenteredSquareMonitor::from_row_masks(side, rows)
            .unwrap()
            .profile(side)
            .unwrap()
            .port_word
    }

    fn assert_streaming_exhaustive(side: usize) {
        let stream = StreamingSquare::new(side).unwrap();
        for mask in 0..1u32 << (side * side) {
            assert_eq!(
                streaming_summary(&stream, mask),
                terminal_summary(side, mask),
                "side={side} mask=0x{mask:x}"
            );
        }
    }

    #[test]
    fn canonical_summary_distinguishes_cyclic_and_linear_runs() {
        let summary = summarize_port_word(&[7, 2, 7, 2]);
        assert_eq!(summary.canonical_word, [0, 1, 0, 1]);
        assert_eq!(summary.repeated_components, 2);
        assert_eq!(summary.maximum_cyclic_runs_per_component, 2);
        assert_eq!(summary.compressed_tokens, ["R0", "R1", "R0", "R1"]);
        assert_eq!(summary.compressed_linear_run_count, 4);
    }

    #[test]
    fn all_u_square_has_one_component_and_one_run() {
        let monitor = CenteredSquareMonitor::parse("UUU\nUUU\nUUU\n").unwrap();
        let summary = monitor.profile(3).unwrap().port_word;
        assert_eq!(summary.canonical_word, vec![0; 8]);
        assert_eq!(summary.repeated_components, 1);
        assert_eq!(summary.maximum_cyclic_runs_per_component, 1);
        assert_eq!(summary.compressed_linear_run_count, 1);
    }

    #[test]
    fn hollow_three_square_preserves_clockwise_port_order() {
        let monitor = CenteredSquareMonitor::parse("UUU\nU.U\nUUU\n").unwrap();
        let summary = monitor.profile(3).unwrap().port_word;
        assert_eq!(summary.canonical_word, [0, 1, 1, 2, 2, 3, 3, 0]);
        assert_eq!(summary.repeated_components, 4);
        assert_eq!(summary.maximum_cyclic_runs_per_component, 1);
        assert_eq!(summary.compressed_linear_run_count, 5);
    }

    #[test]
    fn row_masks_and_parser_select_the_same_centered_square() {
        let parsed = CenteredSquareMonitor::parse(".....\n.UUU.\n.U.U.\n.UUU.\n.....").unwrap();
        let masks = [0, 0b01110, 0b01010, 0b01110, 0];
        let packed = CenteredSquareMonitor::from_row_masks(5, masks).unwrap();
        assert_eq!(parsed.profile(3).unwrap(), packed.profile(3).unwrap());
        assert_eq!(parsed.profiles().len(), 2);
    }

    #[test]
    fn empty_word_has_zero_metrics() {
        let summary = summarize_port_word(&[]);
        assert!(summary.canonical_word.is_empty());
        assert_eq!(summary.repeated_components, 0);
        assert_eq!(summary.maximum_cyclic_runs_per_component, 0);
        assert_eq!(summary.compressed_linear_run_count, 0);
    }

    #[test]
    fn oversized_text_pattern_is_rejected_before_bit_packing() {
        let row = ".".repeat(129);
        let pattern = std::iter::repeat_n(row, 129).collect::<Vec<_>>().join("\n");
        assert!(CenteredSquareMonitor::parse(&pattern).is_err());
    }

    #[test]
    fn streaming_state_agrees_with_terminal_monitor_exhaustively_through_side_four() {
        for side in 2..=4 {
            assert_streaming_exhaustive(side);
        }
    }

    #[test]
    #[ignore = "33,554,432-pattern exhaustive control; run explicitly in release mode"]
    fn streaming_state_agrees_with_terminal_monitor_exhaustively_at_side_five() {
        assert_streaming_exhaustive(5);
    }

    #[test]
    fn streaming_state_forgets_closed_portless_components() {
        let stream = StreamingSquare::new(5).unwrap();
        let mut state = stream.initial_state();
        for position in 0..25 {
            state = stream.advance(state, position, false, 0).unwrap();
        }
        assert!(stream.port_word(&state).is_empty());
        assert!(state.completed_port_masks(5).is_empty());
        assert_eq!(stream.summary(&state), terminal_summary(5, 0));
    }

    #[test]
    fn streaming_state_does_not_retain_redundant_row_bits() {
        assert_eq!(std::mem::size_of::<StreamingSquareState>(), 48);
        let stream = StreamingSquare::new(3).unwrap();
        let mut state = stream.initial_state();
        for position in 0..4 {
            state = stream.advance(state, position, false, 0).unwrap();
        }
        // At local (1, 1), only prior-row column 1 and current-row column 0 matter.
        assert_eq!(
            stream.advance(state, 4, true, 0),
            stream.advance(state, 4, true, 1 << 2)
        );
    }
}
