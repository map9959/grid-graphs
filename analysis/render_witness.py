#!/usr/bin/env python3
"""
Render the optimal spanning tree from `cargo run --release -- witness M N`
as ASCII art, plus a per-column edge digest, plus full-degree mark.

Run from repo root:
    python3 analysis/render_witness.py M N
or to dump several:
    python3 analysis/render_witness.py --probe
"""
import argparse
import os
import subprocess
import sys
from typing import List, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def run_witness(m: int, n: int) -> Tuple[int, int, int, bool, List[Tuple[int, int, int, int]]]:
    """Returns (m_eff, n_eff, value, transposed, edges)."""
    out = subprocess.run(
        ["cargo", "run", "--release", "--quiet", "--", "witness", str(m), str(n)],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout
    header = None
    edges: List[Tuple[int, int, int, int]] = []
    for line in out.splitlines():
        if line.startswith("#"):
            header = line
        else:
            parts = line.split()
            edges.append((int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3])))
    # parse "# m=M n=N value=V transposed=T edges=E"
    assert header is not None, f"no header in output:\n{out}"
    fields = dict(p.split("=") for p in header.lstrip("#").split())
    return (int(fields["m"]), int(fields["n"]), int(fields["value"]),
            fields["transposed"] == "true", edges)


def grid_deg(m: int, n: int, r: int, c: int) -> int:
    return (r > 0) + (r + 1 < m) + (c > 0) + (c + 1 < n)


def render_tree(m: int, n: int, edges) -> str:
    """ASCII render: each cell is one character (the row index), with `-` for
    horizontal edges between cells and `|` between rows. Full-degree vertices
    are uppercased / starred."""
    horiz = set()  # ((r, c), (r, c+1))
    vert = set()   # ((r, c), (r+1, c))
    deg = [[0] * n for _ in range(m)]
    for (r1, c1, r2, c2) in edges:
        deg[r1][c1] += 1
        deg[r2][c2] += 1
        if r1 == r2 and c2 == c1 + 1:
            horiz.add((r1, c1))
        elif c1 == c2 and r2 == r1 + 1:
            vert.add((r1, c1))

    # full-degree set
    full = [[deg[r][c] == grid_deg(m, n, r, c) for c in range(n)] for r in range(m)]

    # Build a (2m - 1) x (2n - 1) char grid.
    out_h = 2 * m - 1
    out_w = 2 * n - 1
    grid = [[" " for _ in range(out_w)] for _ in range(out_h)]
    for r in range(m):
        for c in range(n):
            ch = "*" if full[r][c] else "."
            grid[2 * r][2 * c] = ch
    for (r, c) in horiz:
        grid[2 * r][2 * c + 1] = "-"
    for (r, c) in vert:
        grid[2 * r + 1][2 * c] = "|"
    return "\n".join("".join(row) for row in grid)


def column_digest(m: int, n: int, edges) -> List[str]:
    """For each column c (0..n-1), produce a string summary:
       'V<down-bits>|H<right-bits>'
       where down-bits[r] = 1 if (r, c)-(r+1, c) ∈ T (r ∈ 0..m-2),
       and right-bits[r] = 1 if (r, c)-(r, c+1) ∈ T (r ∈ 0..m-1)."""
    horiz = [[0] * n for _ in range(m)]
    vert = [[0] * n for _ in range(m)]
    for (r1, c1, r2, c2) in edges:
        if r1 == r2 and c2 == c1 + 1:
            horiz[r1][c1] = 1
        elif c1 == c2 and r2 == r1 + 1:
            vert[r1][c1] = 1
    out = []
    for c in range(n):
        v = "".join(str(vert[r][c]) for r in range(m - 1))
        h = "".join(str(horiz[r][c]) for r in range(m))
        out.append(f"V{v}|H{h}")
    return out


def probe():
    """Inspect motifs for m ∈ {3, 5, 6, 8} at moderate n."""
    for m in [3, 5, 6, 8]:
        n = 18 if m == 8 else 12
        if m == 6:
            n = 14
        m_eff, n_eff, value, transposed, edges = run_witness(m, n)
        print(f"=== m_user={m} n_user={n} → canonical {m_eff}x{n_eff}, "
              f"transposed={transposed}, P={value} ===")
        print(render_tree(m_eff, n_eff, edges))
        print()
        cols = column_digest(m_eff, n_eff, edges)
        print("  Column digests (V=vertical-edges-going-down per row, H=horizontal-edges-going-right per row):")
        for c, s in enumerate(cols):
            print(f"    c={c:>2}: {s}")
        print()
        print(f"  Total full-degree: {value}")
        print()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("m", nargs="?", type=int)
    ap.add_argument("n", nargs="?", type=int)
    ap.add_argument("--probe", action="store_true")
    args = ap.parse_args()
    if args.probe:
        probe()
        return
    if args.m is None or args.n is None:
        ap.error("provide M N or --probe")
    m_eff, n_eff, value, transposed, edges = run_witness(args.m, args.n)
    print(f"# m={m_eff} n={n_eff} P={value} (transposed={transposed})")
    print(render_tree(m_eff, n_eff, edges))
    print()
    for c, s in enumerate(column_digest(m_eff, n_eff, edges)):
        print(f"c={c:>2}: {s}")


if __name__ == "__main__":
    main()
