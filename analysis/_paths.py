"""Source and artifact locations shared by the reorganized analysis packages."""

import sys
from pathlib import Path

ANALYSIS_ROOT = Path(__file__).resolve().parent
REPO_ROOT = ANALYSIS_ROOT.parent

SUBJECTS = (
    "patterns",
    "tiles",
    "bounds",
    "transport",
    "residue_geometry",
    "residue_certificates",
    "searches",
    "witness_tools",
)

_RENAMED_TESTS = {
    "n23_target_search_test.py": "test_n23_target_search.py",
    "open_slab_repair_test.py": "test_open_slab_repair.py",
    "residue_two_open_slab_test.py": "test_residue_two_open_slab.py",
    "test_support.py": "_support.py",
}


def source_path(name: str) -> Path:
    """Find one analysis source by basename, without importing or executing it."""
    if Path(name).name != name or not name.endswith(".py"):
        raise ValueError(f"expected a Python source basename, got {name!r}")
    name = _RENAMED_TESTS.get(name, name)
    directories = [ANALYSIS_ROOT, ANALYSIS_ROOT / "tests"]
    directories.extend(ANALYSIS_ROOT / subject for subject in SUBJECTS)
    directories.extend(ANALYSIS_ROOT / "tests" / subject for subject in SUBJECTS)
    matches = [directory / name for directory in directories if (directory / name).is_file()]
    if len(matches) != 1:
        raise FileNotFoundError(f"expected one source for {name!r}, found {matches}")
    return matches[0]


def analysis_path(name: str) -> Path:
    """Resolve a former sibling resource; result files need not exist yet."""
    if Path(name).name != name:
        raise ValueError(f"expected an analysis resource basename, got {name!r}")
    return source_path(name) if name.endswith(".py") else ANALYSIS_ROOT / name


def module_command(source: str | Path) -> list[str]:
    """Python module argv for a subprocess run with cwd=REPO_ROOT."""
    path = source_path(source) if isinstance(source, str) else source
    relative = path.resolve().relative_to(REPO_ROOT)
    if relative.parts[0] != "analysis" or relative.suffix != ".py":
        raise ValueError(f"not an analysis Python module: {path}")
    return [sys.executable, "-m", ".".join(relative.with_suffix("").parts)]
