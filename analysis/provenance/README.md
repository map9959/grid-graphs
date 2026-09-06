# Source Layout Migration

`layout_migration.json` records the Python package reorganization. Each entry
contains the original and relocated paths and the SHA-256 of the source before
and after the import/path/command changes. This is migration metadata, not a
new experiment result or a certificate of a mathematical claim.

`sources/<sha256>.py.txt` preserves exact pre-move source bytes when their hash
appears in an existing result artifact. The extension is deliberate: these are
historical provenance documents, not modules to import or execute.

The result JSON and witness files themselves remain unchanged. The test-only
`analysis.tests._support.migrated_artifact` adapter makes the documented layout
changes explicit during comparisons and rejects subsequent unrecorded source
drift. See the analysis README for details.
