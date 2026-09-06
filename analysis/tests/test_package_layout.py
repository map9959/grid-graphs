"""Bounded checks for module paths and preservation of historical provenance."""

import ast
import copy
import hashlib
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

from analysis._paths import (
    ANALYSIS_ROOT,
    REPO_ROOT,
    analysis_path,
    module_command,
    source_path,
)
from analysis.tests._support import migrated_artifact


class PackageLayoutTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger = json.loads(
            (ANALYSIS_ROOT / "provenance" / "layout_migration.json").read_text()
        )

    def test_every_moved_source_has_one_destination(self):
        for entry in self.ledger["files"]:
            with self.subTest(source=entry["old_path"]):
                self.assertEqual(
                    source_path(Path(entry["old_path"]).name),
                    REPO_ROOT / entry["new_path"],
                )

    def test_no_bare_local_imports_remain(self):
        old_modules = {Path(entry["old_path"]).stem for entry in self.ledger["files"]}
        for entry in self.ledger["files"]:
            path = REPO_ROOT / entry["new_path"]
            for node in ast.walk(ast.parse(path.read_text(), filename=str(path))):
                if isinstance(node, ast.ImportFrom):
                    self.assertNotIn(node.module, old_modules, str(path))
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        self.assertNotIn(alias.name, old_modules, str(path))

    def test_artifact_and_source_roots_are_distinct(self):
        self.assertEqual(
            analysis_path("residue_two_phase_front_witness.txt"),
            ANALYSIS_ROOT / "residue_two_phase_front_witness.txt",
        )
        self.assertEqual(
            analysis_path("tile_grammar.py"),
            ANALYSIS_ROOT / "tiles" / "tile_grammar.py",
        )
        self.assertEqual(
            analysis_path("not-yet-produced.json"),
            ANALYSIS_ROOT / "not-yet-produced.json",
        )

    def test_python_subprocess_command_uses_a_module(self):
        self.assertEqual(
            module_command("construction_lab.py"),
            [sys.executable, "-m", "analysis.patterns.construction_lab"],
        )

    def test_archived_sources_match_their_recorded_hashes(self):
        archives = list((ANALYSIS_ROOT / "provenance" / "sources").glob("*.py.txt"))
        self.assertTrue(archives)
        known = {entry["before_sha256"] for entry in self.ledger["files"]}
        for path in archives:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            self.assertEqual(path.name, f"{digest}.py.txt")
            self.assertIn(digest, known)

    def archived_entry(self):
        return next(
            entry
            for entry in self.ledger["files"]
            if entry["before_sha256"] != entry["after_sha256"]
            and (
                ANALYSIS_ROOT
                / "provenance"
                / "sources"
                / f"{entry['before_sha256']}.py.txt"
            ).is_file()
        )

    def test_metadata_mapping_preserves_scientific_payload_and_original(self):
        entry = self.archived_entry()
        record = {
            "payload": {"rows": ["UUU", "UFU", "UUU"], "score": 1},
            "source": {"path": entry["old_path"], "sha256": entry["before_sha256"]},
            "command": [
                "python3",
                "-B",
                entry["old_path"],
                "--output",
                "analysis/result.json",
            ],
        }
        original = copy.deepcopy(record)
        migrated = migrated_artifact(record)
        self.assertEqual(record, original)
        self.assertEqual(migrated["payload"], original["payload"])
        self.assertEqual(migrated["source"]["sha256"], entry["after_sha256"])
        self.assertEqual(migrated["command"][:3], ["python3", "-B", "-m"])
        self.assertEqual(migrated["command"][-1], "analysis/result.json")

    def test_provenance_adapter_rejects_later_source_drift(self):
        entry = self.archived_entry()
        current = REPO_ROOT / entry["new_path"]
        original_read = Path.read_bytes

        def read_bytes(path):
            return b"unrecorded source edit" if path == current else original_read(path)

        with patch.object(Path, "read_bytes", read_bytes):
            with self.assertRaisesRegex(
                AssertionError, "source changed after layout migration"
            ):
                migrated_artifact({"sha256": entry["before_sha256"]})


if __name__ == "__main__":
    unittest.main()
