from __future__ import annotations

import os
import unittest


slow_test = unittest.skipUnless(
    os.environ.get("GRID_GRAPHS_RUN_SLOW_TESTS") == "1",
    "set GRID_GRAPHS_RUN_SLOW_TESTS=1 to run slow exact-search/integration tests",
)


def migrated_artifact(record):
    """Compare historical results after the documented source-layout-only migration.

    Result files are never rewritten. Only recorded Python source hashes and
    relocated source/command metadata are mapped. A later source edit still
    fails provenance checks, rather than being silently accepted.
    """
    import hashlib
    import json
    import re

    from analysis._paths import ANALYSIS_ROOT, REPO_ROOT

    ledger = json.loads((ANALYSIS_ROOT / "provenance" / "layout_migration.json").read_text())
    paths = {item["old_path"]: item["new_path"] for item in ledger["files"]}
    hashes = {}
    for item in ledger["files"]:
        hashes.setdefault(item["before_sha256"], []).append(item)

    command_pattern = re.compile(
        r"\b(python(?:3)?(?:\s+-[A-Za-z]+)*)\s+(analysis/[A-Za-z0-9_]+\.py)\b"
    )
    path_pattern = re.compile(r"\banalysis/[A-Za-z0-9_]+\.py\b")

    def command(match):
        new = paths.get(match.group(2))
        if new is None:
            return match.group()
        module = new.removesuffix(".py").replace("/", ".")
        return f"{match.group(1)} -m {module}"

    def text(value):
        if value in hashes:
            entries = hashes[value]
            changed = {item["after_sha256"] for item in entries}
            if len(changed) != 1:
                raise AssertionError(f"ambiguous migrated source hash: {value}")
            item = entries[0]
            if item["after_sha256"] == value:
                return value
            current = REPO_ROOT / item["new_path"]
            digest = hashlib.sha256(current.read_bytes()).hexdigest()
            if digest != item["after_sha256"]:
                raise AssertionError(f"source changed after layout migration: {current}")
            archived = ANALYSIS_ROOT / "provenance" / "sources" / f"{value}.py.txt"
            if not archived.is_file() or hashlib.sha256(archived.read_bytes()).hexdigest() != value:
                raise AssertionError(f"missing or altered historical source: {value}")
            return digest
        value = command_pattern.sub(command, value)
        return path_pattern.sub(
            lambda match: paths.get(match.group(), match.group()),
            value,
        )

    def walk(value):
        if isinstance(value, dict):
            return {key: walk(item) for key, item in value.items()}
        if isinstance(value, list):
            return [walk(item) for item in value]
        return text(value) if isinstance(value, str) else value

    return walk(record)
