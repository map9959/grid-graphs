"""Export the actual compressed price predicates for southeast atlas windows.

Use the same price table and cover producer as defect_window.window.
Only the distinct southeast representative points are stored. Lean
independently audits the cubes against its price definitions.
"""
from itertools import product
from pathlib import Path

from .defect_window import table
from .square_current import DIR
from .tight_corner_sat import cover

PATCH = (6, 7, 8, 15, 16, 17, 18, 19, 20)
STAR = (6, 7, 8, 17, 18, 19, 20, 21, 22)
DEST = (Path(__file__).resolve().parents[2] /
        "lean/GridGraphs/ResidueTwoUpper/OneGap/SouthCapPriceCubes.txt")


def export():
    typ, patch, star = table(119)
    rows = []

    def emit(values):
        # +1 distinguishes an actual zero mask from a blank row.
        rows.append(" ".join(str(1+m+512*b) for m, b in
                             cover(tuple(q != 0 for q in values))) or "0")

    for r, c in product(PATCH, repeat=2):
        emit(patch(typ(1, r+96*(r >= 15), c+96*(c >= 15))))
    for r, c in product(STAR, repeat=2):
        x, y = r+96*(r >= 17), c+96*(c >= 17)
        ds = tuple(d for d, (a, b) in enumerate(DIR) if x+a<119 and y+b<119)
        for out in range(5):
            if out != 4 and out not in ds:
                rows.append("0")
            else:
                emit(star(typ(0, x, y), ds, -1 if out == 4 else out,
                          r == c == 22, r == c == 22))

    # Check the producer's own type vectors at every site of the
    # southeast envelope; the window-specific sets are subsets of it.
    for t, size in ((0, 119), (1, 117)):
        def source(x):
            return x if x >= size-6 else 6+(x-6) % 3
        for x, y in product(range(88, size), repeat=2):
            assert typ(t, x, y) == typ(t, source(x), source(y))
    DEST.write_text("\n".join(rows)+"\n")
    print(f"{len(rows)} rows, {DEST.stat().st_size} bytes")


if __name__ == "__main__":
    export()
