#!/usr/bin/env python3
"""
Verify explicit spanning-tree constructions for m × n grid graphs.

For each construction, this script:
  1. Confirms the edge set is a valid spanning tree of G(m, n)
     (correct edge count = m*n - 1, all vertices reachable, acyclic).
  2. Counts full-degree vertices (deg_T(v) == deg_G(v)).
  3. Compares against the empirical P(m, n) (loaded from extended.csv /
     extended_long.csv) for the constructed n.

Run: python3 -m analysis.patterns.check_constructions
"""
import csv
import os
from typing import Iterable, List, Tuple

from analysis._paths import REPO_ROOT

ROOT = str(REPO_ROOT)
DATA_CSV = os.path.join(ROOT, "data", "extended.csv")
DATA_LONG_CSV = os.path.join(ROOT, "data", "extended_long.csv")

Edge = Tuple[Tuple[int, int], Tuple[int, int]]


def load_known() -> dict:
    known = {}
    for path in (DATA_CSV, DATA_LONG_CSV):
        if not os.path.exists(path):
            continue
        with open(path) as f:
            rd = csv.DictReader(f)
            for row in rd:
                m, n = int(row["m"]), int(row["n"])
                p = int(row.get("actual", row.get("P", "0")))
                known[(m, n)] = p
    return known


def grid_deg(m: int, n: int, r: int, c: int) -> int:
    return (r > 0) + (r + 1 < m) + (c > 0) + (c + 1 < n)


def normalize(e: Edge) -> Edge:
    a, b = e
    return (a, b) if a < b else (b, a)


def is_spanning_tree(m: int, n: int, edges: Iterable[Edge]) -> Tuple[bool, str]:
    edges = [normalize(e) for e in edges]
    eset = set(edges)
    if len(eset) != len(edges):
        return False, "duplicate edges"
    if len(edges) != m * n - 1:
        return False, f"edge count {len(edges)} != {m*n - 1}"
    for (a, b) in edges:
        if abs(a[0] - b[0]) + abs(a[1] - b[1]) != 1:
            return False, f"non-grid edge {a}-{b}"
        if not (0 <= a[0] < m and 0 <= a[1] < n and 0 <= b[0] < m and 0 <= b[1] < n):
            return False, f"out-of-range edge {a}-{b}"
    parent = {(r, c): (r, c) for r in range(m) for c in range(n)}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for (a, b) in edges:
        ra, rb = find(a), find(b)
        if ra == rb:
            return False, f"cycle at {a}-{b}"
        parent[ra] = rb
    roots = {find((r, c)) for r in range(m) for c in range(n)}
    if len(roots) != 1:
        return False, f"disconnected; {len(roots)} components"
    return True, "ok"


def count_full_degree(m: int, n: int, edges: Iterable[Edge]) -> int:
    deg_t = [[0] * n for _ in range(m)]
    for (a, b) in (normalize(e) for e in edges):
        deg_t[a[0]][a[1]] += 1
        deg_t[b[0]][b[1]] += 1
    full = 0
    for r in range(m):
        for c in range(n):
            if deg_t[r][c] == grid_deg(m, n, r, c):
                full += 1
    return full


# -----------------------------------------------------------------------------
# Verified-optimal constructions
# -----------------------------------------------------------------------------

def tree_m1(n: int) -> List[Edge]:
    """Trivial m=1 case: G(1, n) is a path; the unique spanning tree
    contains every edge."""
    return [((0, c), (0, c + 1)) for c in range(n - 1)]


def tree_m2(n: int) -> List[Edge]:
    """m=2: the 2 × n ladder. Achieves P(2, n) = n.

    Construction: top row spine (n - 1 edges) + every column rung
    (n edges) = 2n - 1 = m·n - 1. ✓
    """
    e: List[Edge] = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
    for c in range(n):
        e.append(((0, c), (1, c)))
    return e


def tree_m4_double_spine(n: int) -> List[Edge]:
    """For G(4, n): top + bottom spine + every (0,c)-(1,c) and (2,c)-(3,c)
    + the col-0 rung (1,0)-(2,0).

    Edge count: 2(n-1) + 2n + 1 = 4n - 1. ✓

    Achieves P(4, n) = 2n exactly for all n ≥ 2. (Optimal: matches the
    conjectured closed form and is verified by checker for n up to 50.)
    """
    edges: List[Edge] = []
    for c in range(n - 1):
        edges.append(((0, c), (0, c + 1)))
        edges.append(((3, c), (3, c + 1)))
    for c in range(n):
        edges.append(((0, c), (1, c)))
        edges.append(((2, c), (3, c)))
        if c == 0:
            edges.append(((1, c), (2, c)))
    return edges


def tree_m3_witness(n: int) -> List[Edge]:
    """Period-3 motif for G(3, n), read off from `solve_with_witness` at large n.

    Per column c (0-indexed), the included edges are:
      c % 3 == 0:  V = 11        H = 101        (full ladder + top + bottom spine)
      c % 3 == 1:  V = 01        H = 001        (mid vertical, only bottom spine)
      c % 3 == 2:  V = 01        H = 101        (mid vertical, top + bottom spine)

    where V[r] indicates the vertical edge (r, c)-(r+1, c) and H[r]
    indicates the horizontal (r, c)-(r, c+1) (only relevant for c < n - 1).

    Boundary correction: when n ≡ 0 (mod 3), one extra (top) vertical at
    column n - 1 is appended to land at exactly m·n − 1 = 3n − 1 edges.

    Achieves P(3, n) for all n ≥ 2 in the verified range. (Optimal.)
    """
    m = 3
    e: List[Edge] = []
    interior_v = ["11", "01", "01"]
    interior_h = ["101", "001", "101"]

    for c in range(n):
        cp = c % 3
        for r in range(m - 1):
            if interior_v[cp][r] == "1":
                e.append(((r, c), (r + 1, c)))
        if c < n - 1:
            for r in range(m):
                if interior_h[cp][r] == "1":
                    e.append(((r, c), (r, c + 1)))

    if n % 3 == 0 and n >= 3:
        e.append(((0, n - 1), (1, n - 1)))

    return e


def tree_m5_three_spine(n: int) -> List[Edge]:
    """Three-spine construction for G(5, n): horizontal spines at rows 0,
    2, and 4; per-column verticals at rows 0-1 and 3-4 (so rows 1 and 3
    hang off rows 0 and 4); plus column-0 rungs (1, 0)-(2, 0) and
    (2, 0)-(3, 0) to glue row 2 to the rest of the tree.

    Edge count: 3(n - 1) + 2n + 2 = 5n - 1. ✓
    Achieves P = 2n + 1 (row 0 fully + row 4 fully + (2, 0) corner).

    This is **optimal for n ≡ 0, 2 (mod 3)** (where conjectured P = 2n + 1)
    and **off by 1 for n ≡ 1 (mod 3)** (where conjectured P = 2n + 2).
    """
    m = 5
    e: List[Edge] = []
    # Three horizontal spines.
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((2, c), (2, c + 1)))
        e.append(((4, c), (4, c + 1)))
    # Per-column verticals at rows 0-1 and 3-4.
    for c in range(n):
        e.append(((0, c), (1, c)))
        e.append(((3, c), (4, c)))
    # Column-0 bridge: connect row 2 to rows 1 and 3 (and thus to rows 0, 4).
    e.append(((1, 0), (2, 0)))
    e.append(((2, 0), (3, 0)))
    return e


def tree_m5_period3_motif(n: int) -> List[Edge]:
    """Period-3 motif for G(5, n) extracted from the witness DP at n=22.

    Per column c (0 ≤ c < n):
      c % 3 == 0 :  V = 1111  H = 10111  (gain 4: rows 0, 2, 3, 4 full)
      c % 3 == 1 :  V = 1000  H = 10000  (gain 1: row 0 full)
      c % 3 == 2 :  V = 1000  H = 10111  (gain 1: row 0 full)

    where V[r] is the vertical edge (r, c)-(r+1, c), H[r] is the
    horizontal (r, c)-(r, c+1) (only for c < n-1).

    Per period (3 columns) this contributes 8 + 2 + 5 = 15 = m·q − 0
    edges. For n = 3k we'd get exactly 15k edges, but the spanning tree
    has m·n − 1 = 15k − 1 edges, which means 1 too many — a cycle. So
    for n ≡ 0 (mod 3) this motif is invalid (it would force a cycle in
    the last column). We exclude that case here.

    For n ≡ 1 (mod 3) and n ≡ 2 (mod 3), the spanning-tree edge count
    works out exactly. Achieves `P(5, n) = 2n + 2` when n ≡ 1 (mod 3)
    and `P(5, n) = 2n + 1` when n ≡ 2 (mod 3) — the conjectured
    optimum.

    The c % 3 == 0 column with V = 1111 is the "fully preserved
    interior column" referenced in `analysis/proofs_m345.md`: every
    vertex in this column has its full grid degree retained.
    """
    m = 5
    interior_v = ["1111", "1000", "1000"]
    interior_h = ["10111", "10000", "10111"]
    e: List[Edge] = []
    for c in range(n):
        cp = c % 3
        v = interior_v[cp]
        h = interior_h[cp]
        for r in range(m - 1):
            if v[r] == "1":
                e.append(((r, c), (r + 1, c)))
        if c < n - 1:
            for r in range(m):
                if h[r] == "1":
                    e.append(((r, c), (r, c + 1)))
    return e


def tree_m5_witness(n: int) -> List[Edge]:
    """`m=5` construction, optimal in the n ≥ m regime for **all**
    residues n mod 3 (Phase 4 update).

    Strategy:
      - n ≡ 0 (mod 3):  three-spine construction (preserves rows 0, 4)
        — achieves `P(5, n) = 2n + 1`.
      - n ≡ 1 or 2 (mod 3):  period-3 motif with "fully preserved
        interior column" — achieves `P(5, n) = 2n + 2` (for n%3==1)
        or `2n + 1` (for n%3==2), both matching the conjectured
        optimum.

    The n ≡ 1 case is the residue that the prior three-spine
    construction missed by 1; the period-3 motif (extracted by the
    Phase 4 witness analysis at n=22) closes that gap.
    """
    if n % 3 == 0:
        return tree_m5_three_spine(n)
    return tree_m5_period3_motif(n)


def tree_m7_witness(n: int) -> List[Edge]:
    """Period-1 (eventually constant) motif for G(7, n), read off from
    witness at n = 18.

    Per column c:
      c == 0     :  V = 111111   H = 1111111  (left boundary, full ladder + all spines)
      c == 1     :  V = 000000   H = 1001001  (left boundary, three spines only)
      c >= 2     :  V = 101101   H = 1001001  (interior period-1 motif)
      c == n - 1 :  V = 101101   H = 0000000  (right boundary, last col)

    V = 101101 = verticals (0-1, 2-3, 3-4, 5-6) yes; (1-2, 4-5) no.
    H = 1001001 = horizontals at rows 0, 3, 6 (three spine rows).

    Achieves P(7, n) = 3n + 1 for all n in the verified range.
    """
    m = 7
    e: List[Edge] = []
    if n < 2: return []

    def add_v(c, vbits):
        for r in range(m - 1):
            if vbits[r] == "1":
                e.append(((r, c), (r + 1, c)))

    def add_h(c, hbits):
        if c == n - 1: return
        for r in range(m):
            if hbits[r] == "1":
                e.append(((r, c), (r, c + 1)))

    for c in range(n):
        if c == 0:
            add_v(c, "111111"); add_h(c, "1111111")
        elif c == 1:
            add_v(c, "000000"); add_h(c, "1001001")
        else:
            add_v(c, "101101"); add_h(c, "1001001")

    return e


def tree_m8_witness(n: int) -> List[Edge]:
    """Period-7 motif for G(8, n) extracted from the witness DP.

    The optimal m=8 spanning trees have a period-7 interior structure
    that alternates between two reflected blocks (Block A and Block B,
    related by row-reversal). For widths where n ≡ 6 (mod 7) and
    n ≥ 20, we use the explicit witness layout observed at n = 20:

        col 0     :  V = 1111111  H = 11111111   (left boundary, gain 8)
        col 1     :  V = 0000000  H = 10001001   (left boundary, gain 0)
        cols 2..n-3 (interior, alternating blocks A and B every 7 cols)
        col n-2   :  V = 1000001  H = 10011101   (right boundary, gain 2)
        col n-1   :  V = 1011111  H = 00000000   (right boundary, gain 5)

    Each interior block of 7 columns contributes gain 22 = α₈·7. With
    one boundary contribution of 8 + 0 + 2 + 5 = 15 spread over the 4
    boundary cols, we have:
      P(8, n) = 15 + 22·k where k = (n - 4) / 7.

    Cross-check with closed form (recurrences.md): for n ≡ 6 (mod 7)
    starting at n = 20 (k = 1): P(8, 20) = 15 + 22 = 37? — no, observed
    P(8, 20) = 65. Let me re-tally: gain seq for n=20 is
        [8, 0, 3,3,3,3,3,4,3, 3,3,3,3,3,4,3, 2, 5]
        = 8 + 22 + 22 + 6 + 7 = 65 ✓.
    So actually the right boundary takes 4 cols (cols 16-19) with
    total gain 6 + 7 = 13, and the right boundary's last 2 cols add to
    the right boundary's first 2 cols (which are partial). Treating
    cols 16-17 as **part of an incomplete Block B**, the structure
    becomes: cols 0-1 boundary (gain 8) + 2 full blocks (cols 2-15,
    gain 44) + cols 16-19 right boundary (gain 13).

    For arbitrary n the right boundary needs to be rederived per
    residue class; this implementation handles only n = 20, 34, 48
    (n − 20 divisible by 14 — i.e. an even number of full A/B block
    pairs after the left boundary). Other widths fall through to an
    empty edge list, which the caller will flag as invalid.
    """
    m = 8
    if n < 20 or (n - 20) % 14 != 0:
        return []

    # Block A (cols 2..8): the period-7 motif.
    block_a = [
        ("1001101", "10101001"),  # gain 3
        ("1110001", "10100101"),  # gain 3
        ("1000111", "10010101"),  # gain 3
        ("1011001", "10010001"),  # gain 3
        ("1011001", "10010101"),  # gain 3
        ("1011111", "10010101"),  # gain 4
        ("1011001", "10010001"),  # gain 3
    ]
    # Block B (cols 9..15): row-reversal of Block A.
    block_b = [
        (v[::-1], h[::-1]) for v, h in block_a
    ]
    # Left boundary cols 0, 1.
    left_cols = [
        ("1111111", "11111111"),
        ("0000000", "10001001"),
    ]
    # Right boundary cols n-4..n-1. Pattern observed at n = 20.
    right_cols = [
        ("1001101", "10101001"),
        ("1110001", "10100101"),
        ("1000001", "10011101"),
        ("1011111", "00000000"),
    ]
    # Number of full A/B pairs in interior (each pair = 14 cols).
    k = (n - 20) // 14 + 1
    interior: List[tuple] = []
    for _ in range(k):
        interior.extend(block_a)
        interior.extend(block_b)
    cols = left_cols + interior + right_cols
    assert len(cols) == n, f"expected {n} cols, built {len(cols)}"
    e: List[Edge] = []
    for c, (v, h) in enumerate(cols):
        for r in range(m - 1):
            if v[r] == "1":
                e.append(((r, c), (r + 1, c)))
        if c < n - 1:
            for r in range(m):
                if h[r] == "1":
                    e.append(((r, c), (r, c + 1)))
    return e


def tree_m6_witness(n: int) -> List[Edge]:
    """Period-4 motif for G(6, n), read off from witness at n=24.

    Currently only implemented for n ≡ 0 (mod 4) with n ≥ 8. Returns an
    empty edge set otherwise (caller will see edge-count failure).

    Per column c:
      c == 0     :  V = 10111   H = 100111   (left boundary)
      c == 1     :  V = 10000   H = 101001   (left boundary)
      c == n - 2 :  V = 10000   H = 101111   (right boundary)
      c == n - 1 :  V = 11111   H = 000000   (right boundary, full ladder)
      otherwise: with c' = (c - 2) % 4:
        c' = 0:  V = 11101   H = 101001
        c' = 1:  V = 10001   H = 100101
        c' = 2:  V = 10111   H = 100101
        c' = 3:  V = 10001   H = 101001

    Achieves P(6, n) for n ∈ {8, 12, 16, 20, ...} (verified by checker).
    """
    m = 6
    e: List[Edge] = []
    if n < 4 or (n - 4) % 4 != 0:
        return []

    def add_v(c, vbits):
        for r in range(m - 1):
            if vbits[r] == "1":
                e.append(((r, c), (r + 1, c)))

    def add_h(c, hbits):
        if c == n - 1: return
        for r in range(m):
            if hbits[r] == "1":
                e.append(((r, c), (r, c + 1)))

    interior_v = ["11101", "10001", "10111", "10001"]
    interior_h = ["101001", "100101", "100101", "101001"]

    for c in range(n):
        if c == 0:
            add_v(c, "10111"); add_h(c, "100111")
        elif c == 1:
            add_v(c, "10000"); add_h(c, "101001")
        elif c == n - 2:
            add_v(c, "10000"); add_h(c, "101111")
        elif c == n - 1:
            add_v(c, "11111"); add_h(c, "000000")
        else:
            cp = (c - 2) % 4
            add_v(c, interior_v[cp]); add_h(c, interior_h[cp])

    return e


# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------

def main():
    """Verify each construction.

    The constructions are *asymptotic*: they describe a periodic interior
    motif that becomes optimal at large n. Small grids (n < m) follow a
    different combinatorial regime where boundary effects dominate, so we
    report n < m and n >= m separately.
    """
    known = load_known()
    print(f"Loaded {len(known)} known P(m, n) values.\n")

    constructions = [
        ("m=1 trivial path", 1, tree_m1, range(2, 51)),
        ("m=2 ladder", 2, tree_m2, range(2, 51)),
        ("m=3 period-3 witness", 3, tree_m3_witness, range(2, 51)),
        ("m=4 double-spine", 4, tree_m4_double_spine, range(2, 51)),
        ("m=5 (three-spine for n%3=0; period-3 for n%3 in {1,2})", 5, tree_m5_witness, range(2, 51)),
        ("m=6 period-4 witness (n%4==0 only)", 6, tree_m6_witness, range(4, 49, 4)),
        ("m=7 period-1 witness", 7, tree_m7_witness, range(2, 31)),
        ("m=8 period-7 witness (n in {20, 34, 48} only)", 8, tree_m8_witness,
         [20, 34, 48]),
    ]

    summary = []
    for name, m, builder, ns in constructions:
        print(f"=== {name} ===")
        for region_label, region_filter in [
            ("n < m (boundary regime)", lambda n: n < m),
            ("n >= m (asymptotic regime)", lambda n: n >= m),
        ]:
            valid_count = 0
            opt_count = 0
            misses = []
            tested = 0
            for n in ns:
                if not region_filter(n):
                    continue
                tested += 1
                edges = builder(n)
                ok, why = is_spanning_tree(m, n, edges)
                if not ok:
                    misses.append((n, "invalid"))
                    continue
                valid_count += 1
                cnt = count_full_degree(m, n, edges)
                target = known.get((m, n)) or closed_form_P(m, n)
                if target is None:
                    continue
                if cnt == target:
                    opt_count += 1
                else:
                    misses.append((n, target - cnt))
            if tested == 0:
                continue
            line = f"  {region_label}: {opt_count}/{tested} optimal, {valid_count} valid"
            if misses:
                short = ", ".join(f"n={n}({g})" for n, g in misses[:6])
                if len(misses) > 6:
                    short += f", ... ({len(misses)} misses)"
                line += f"; misses: {short}"
            print(line)
        summary.append((name, sum(1 for n in ns if n >= m),
                        sum(1 for n in ns if n >= m
                            and is_spanning_tree(m, n, builder(n))[0]
                            and count_full_degree(m, n, builder(n))
                            == (known.get((m, n)) or closed_form_P(m, n) or -1))))
        print()

    print("\nSummary (asymptotic regime, n >= m):")
    print(f"{'construction':<42} {'tested':>7} {'optimal':>8}")
    for name, tested, opt in summary:
        print(f"{name:<42} {tested:>7} {opt:>8}")


def closed_form_P(m, n):
    if m == 1: return n
    if m == 2: return max(2, n)
    if m == 3:
        if n <= 2: return 3
        return (4*n + 2) // 3
    if m == 4:
        if n <= 2: return 4
        return 2 * n
    if m == 5:
        if n <= 3: return [None, 5, 5, 7][n]
        return 2*n + 2 if n % 3 == 1 else 2*n + 1
    if m == 6:
        if n < 10: return None
        return 5*n//2 + 1 if n % 2 == 0 else (5*n + 1) // 2
    if m == 7:
        if n < 7: return None
        return 3 * n + 1
    if m == 8:
        if n < 13: return None
        k = n - 13
        q, r = divmod(k, 7)
        return 43 + 22*q + (3*r if r else 0)
    return None


if __name__ == "__main__":
    main()
