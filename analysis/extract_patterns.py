#!/usr/bin/env python3
"""Decode per-column edge patterns from `cargo run -- witness M N`.

Outputs, for each column c:
  v = bit-string of length m-1 (vertical edges within column c)
  h = bit-string of length m   (horizontal edges from column c to c+1)

Plus per-column full-degree gain. Useful for hand-constructing motifs.
"""
import subprocess, sys, os

def witness(m, n):
    proj = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = subprocess.run(
        ["cargo", "run", "--release", "--quiet", "--", "witness", str(m), str(n)],
        capture_output=True, text=True, cwd=proj
    )
    edges = []
    transposed = False
    for ln in out.stdout.split("\n"):
        if ln.startswith("# "):
            if "transposed=true" in ln.lower():
                transposed = True
            continue
        if not ln.strip(): continue
        parts = ln.split()
        if len(parts) >= 4:
            try:
                edges.append((int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3])))
            except ValueError:
                pass
    return edges, transposed


def grid_deg(m, n, r, c):
    return (r > 0) + (r + 1 < m) + (c > 0) + (c + 1 < n)


def decode(m, n, edges):
    vert = [["0"] * (m - 1) for _ in range(n)]
    horiz = [["0"] * m for _ in range(n)]
    deg = [[0] * n for _ in range(m)]
    for r1, c1, r2, c2 in edges:
        if c1 == c2 and r2 == r1 + 1:
            vert[c1][r1] = "1"
        elif r1 == r2 and c2 == c1 + 1:
            horiz[c1][r1] = "1"
        else:
            raise ValueError(f"weird edge {(r1,c1)}-{(r2,c2)}")
        deg[r1][c1] += 1
        deg[r2][c2] += 1
    gains = []
    for c in range(n):
        g = sum(1 for r in range(m) if deg[r][c] == grid_deg(m, n, r, c))
        gains.append(g)
    return vert, horiz, gains


def find_period(seq, qmax=12, skip=None, min_repeats=2):
    n = len(seq)
    if skip is None: skip = max(2, qmax)
    for q in range(1, qmax + 1):
        if (n - 2*skip) < min_repeats * q + 1: continue
        ok = True
        for c in range(skip, n - skip - q):
            if seq[c] != seq[c + q]:
                ok = False
                break
        if ok:
            return q
    return None


def main():
    if len(sys.argv) != 3:
        print(f"usage: {sys.argv[0]} M N")
        sys.exit(1)
    m, n = int(sys.argv[1]), int(sys.argv[2])
    edges, transposed = witness(m, n)
    if transposed:
        # The witness is in canonical (m_eff, n_eff) frame with
        # m_eff <= n_eff. Our (m, n) request had m > n; swap so output
        # is in the requested frame.
        edges = [(c1, r1, c2, r2) if (c1, r1) < (c2, r2) else (c2, r2, c1, r1)
                 for r1, c1, r2, c2 in edges]
        m, n = n, m
    vert, horiz, gains = decode(m, n, edges)
    print(f"# m={m} n={n} edges={len(edges)} value={sum(gains)}")
    print("# per-column patterns and gains:")
    for c in range(n):
        v = "".join(vert[c])
        h = "".join(horiz[c])
        print(f"  col[{c:3}] v={v} h={h} gain={gains[c]}")
    q = find_period(gains, qmax=12)
    print(f"# gain-sequence period q={q}")
    # Try to find period in (vert, horiz) tuple sequence too.
    pat_seq = [(tuple(vert[c]), tuple(horiz[c])) for c in range(n)]
    qe = find_period(pat_seq, qmax=12, skip=max(3, m), min_repeats=2)
    print(f"# edge-pattern period qe={qe}")
    if qe is not None:
        skip = max(3, m)
        print(f"# motif (one period of edge patterns, columns {skip}..{skip+qe}):")
        for c in range(skip, skip + qe):
            v = "".join(vert[c]); h = "".join(horiz[c])
            print(f"#   col[{c}] v={v} h={h}")


if __name__ == "__main__":
    main()
