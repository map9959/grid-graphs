# Analysis Tools

This directory contains historical experiments, witness checkers, and proof
notes. The mathematical roadmap is [../docs/ROADMAP.md](../docs/ROADMAP.md);
the final proofs live in `../lean/`. A stored experiment is evidence within its
declared scope, not an arbitrary-width theorem.

## Python Layout

| Package | Purpose |
|---|---|
| `patterns/` | Construction definitions and independent witness checks |
| `tiles/` | Tile grammars, row transitions, and frontier encodings |
| `bounds/` | General inequalities, forced forests, and potential arguments |
| `transport/` | Equality corridors, slab transport, and alignment |
| `residue_geometry/` | Geometric classifications and obstruction censuses |
| `residue_certificates/` | Residue-two certificate and grammar experiments |
| `searches/` | Historical construction searches and search-specific exports |
| `witness_tools/` | Extraction, rendering, and inspection of witness files |
| `tests/` | Tests grouped by the corresponding subject; `_support.py` is shared |
| `provenance/` | Source-layout migration record and exact historical source snapshots |

No analyses or artifacts were deleted during this organization. Result JSON,
witness text, proof notes, and C++ checkers remain at their existing locations.
`_paths.py` separates those artifact locations from Python source locations.
User-specified output paths still retain their usual meaning.

## Running Tools

Run modules from the repository root, preserving their existing arguments:

```bash
python3 -m analysis.patterns.construction_lab --help
python3 -m analysis.witness_tools.render_witness --help
```

Use module execution, not `python3 analysis/<folder>/<file>.py`. There are no
flat-path wrappers or per-script `sys.path` bootstraps. From another directory,
put the repository root on `PYTHONPATH` before invoking a module.

Moving a search into `searches/` does not authorize running it. Do not start
optimization above 15x15, unbounded state enumeration, HiGHS, or shard jobs as
part of routine checks. Larger existing witnesses may be replayed without
searching for an optimum.

## Bounded Checks

The core checks use only the Python standard library. From the repository root:

```bash
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.test_package_layout \
  analysis.tests.patterns.test_diagonal_patterns \
  analysis.tests.tiles.test_row_packet_transition \
  analysis.tests.bounds.test_annulus_streaming_result \
  analysis.tests.searches.test_frontier_n17_result \
  analysis.tests.residue_certificates.test_residue_two_n11_face_cut_defect_result
```

Do not substitute unrestricted test discovery for that smoke suite: some
historical tests run searches and not all expensive tests have a slow marker.
Both slow-test environment variables must be unset; setting `GRID_GRAPHS_SLOW`
to `0` still enables tests that use its truthiness. Pytest may also run explicit
test paths when installed, but it is not required for this smoke suite.

The reorganization was checked with the 23-test smoke/layout suite above,
six additional historical-provenance tests, CLI help from the repository root
and another working directory, and explicit 5x5/8x8 witness replay. All 303
current Python sources parse and their qualified imports resolve. The 104
original root-level JSON/TXT/CSV artifacts are byte-identical. No unrestricted
test discovery, optimization search, or result regeneration was run.

## Historical Provenance

Saved results were not regenerated or relabeled as products of the reorganized
source. `provenance/layout_migration.json` records each moved file's original
and new paths and exact before/after SHA-256 hashes. Original Python source
bytes whose hashes appear in the existing artifacts are retained under
`provenance/sources/`, with a `.py.txt` suffix so they are not executable modules.

Tests use the explicit `migrated_artifact` helper when comparing historical
records to current replay metadata. It maps only documented source hashes,
source paths, and Python invocation forms. It checks historical source bytes
and the recorded post-migration source hash; it does not accept arbitrary later
source edits, alter scientific counts or witnesses, or rewrite result files.

Newly produced provenance hashes the current source and records current module
commands. If a later algorithm change invalidates a provenance comparison,
review or regenerate that result under its resource policy. Do not silently
edit historical result hashes or refresh the migration ledger to hide the change.
