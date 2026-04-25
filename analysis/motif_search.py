#!/usr/bin/env python3
"""
Try out periodic-motif candidate constructions for m ∈ {3, 5, 6, 8} and check
their full-degree count against the conjectured P(m, n).

For each candidate, we describe the construction as a function building an
edge set in numpy-friendly form and run it through the same validity +
counting checks as `check_constructions.py`.
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_constructions import is_spanning_tree, count_full_degree, load_known


def closed_form_P(m: int, n: int):
    """Return conjectured P(m, n) (or None if unknown)."""
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
        if n < 10: return None  # boundary, look up
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


# -------- m=3 attempts --------

def m3_attempt_v1(n):
    """Top spine + bottom spine + (1,c)-(2,c) every column + (0,c)-(1,c) at c=0."""
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((2, c), (2, c + 1)))
    for c in range(n):
        e.append(((1, c), (2, c)))
    e.append(((0, 0), (1, 0)))
    return e


def m3_attempt_v2(n):
    """Period-3: at c%3==0 keep verticals (0-1)+(1-2); at c%3==1 keep (1-2);
       at c%3==2 keep (0-1). Plus both spines."""
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((2, c), (2, c + 1)))
    for c in range(n):
        if c % 3 == 0:
            e.append(((0, c), (1, c)))
            e.append(((1, c), (2, c)))
        elif c % 3 == 1:
            e.append(((1, c), (2, c)))
        else:  # c%3 == 2
            e.append(((0, c), (1, c)))
    return e


def m3_witness_motif(n):
    """Period-3 motif read off from the m=3 witness solver at n=24.

    Motif A (used by witness in many positions):
      c % 3 == 0: V=11 H=101  (full ladder + top spine + bottom spine)
      c % 3 == 1: V=01 H=001  (mid vertical r1->r2 + bottom spine)
      c % 3 == 2: V=01 H=101  (mid vertical r1->r2 + top + bottom spine)

    Right boundary (last column) has no horizontals.
    """
    m = 3
    e = []

    def add_v(c, vbits):
        for r in range(m - 1):
            if vbits[r] == "1":
                e.append(((r, c), (r + 1, c)))

    def add_h(c, hbits):
        if c == n - 1: return
        for r in range(m):
            if hbits[r] == "1":
                e.append(((r, c), (r, c + 1)))

    interior_v = ["11", "01", "01"]
    interior_h = ["101", "001", "101"]

    for c in range(n):
        cp = c % 3
        add_v(c, interior_v[cp])
        add_h(c, interior_h[cp])

    # Boundary correction for n % 3 == 0: add the top vertical at last col.
    if n % 3 == 0 and n >= 3:
        e.append(((0, n - 1), (1, n - 1)))

    return e


def m3_attempt_v3(n):
    """Period-3 with row-1 vertices full-degree once per period.
       Top spine + bottom spine + carefully-placed verticals so that
       (0, c) at c%3==0 and (2, c) at c%3 in {0, 1} are full-degree.

       Plan: keep all (1,c)-(2,c) verticals (n edges, makes row 2 hung off
       row 1 path) + (0,c)-(1,c) only at c%3==0 (lights up row 0 at those
       cols).

       Edges: 2(n-1) + n + ceil(n/3). For n divisible by 3, that's
       2n - 2 + n + n/3 = (10n/3) - 2. Need 3n - 1.
       (10n/3 - 2) - (3n - 1) = (n/3 - 1). Off by n/3 (excess).
       Need to drop n/3 vertical edges to break cycles.
       """
    # Skip this; arithmetic doesn't work out cleanly.
    return []


# -------- m=4 attempts (sanity check the existing winner) --------

def m4_double_spine(n):
    """Same as in check_constructions.py."""
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((3, c), (3, c + 1)))
    for c in range(n):
        e.append(((0, c), (1, c)))
        e.append(((2, c), (3, c)))
        if c == 0:
            e.append(((1, c), (2, c)))
    return e


# -------- m=5 attempts --------

def m5_attempt_v1(n):
    """Generalize m=4: top + bottom spines, (0,c)-(1,c), (3,c)-(4,c) every
       column, plus rungs in middle. Need a periodic mid-rung pattern."""
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((4, c), (4, c + 1)))
    for c in range(n):
        e.append(((0, c), (1, c)))
        e.append(((3, c), (4, c)))
    # Now we need to connect rows 1-2 and 2-3 to the rest, and not create cycles.
    # Add (1,0)-(2,0), (2,0)-(3,0) at c=0.
    e.append(((1, 0), (2, 0)))
    e.append(((2, 0), (3, 0)))
    # For c >= 1, add (1,c)-(2,c) every column (so row 2 is hung off row 1).
    # That makes row 1 vertex (1, c) at c >= 1 have 4 edges: (0,c)-(1,c),
    # (1,c)-(2,c), and we'd need (1, c-1)-(1, c) and (1, c)-(1, c+1). NOT in.
    # So row 1 not full-degree. But we still need to connect row 2 across
    # cols. Let's just add (1, c)-(2, c) for all c.
    for c in range(1, n):
        e.append(((1, c), (2, c)))
    # Edge count: 2(n-1) + 2n + 2 + (n-1) = 5n - 2. Need 5n-1. Off by 1.
    # We could also add row-2 horizontal edges, but those would form cycles.
    # For now, return as-is.
    return e


def m5_attempt_v2(n):
    """Top + bottom spines, full ladder at c=0 (4 verticals), and at every
       column c>=1: (0,c)-(1,c), (1,c)-(2,c), (3,c)-(4,c). That should make
       row 0 and row 4 fully preserved (interior + corners), giving 2n
       full-degree.
       Edges: 2(n-1) + 4 + 3(n-1) = 5n - 1. ✓
    """
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((4, c), (4, c + 1)))
    for r in range(4):
        e.append(((r, 0), (r + 1, 0)))
    for c in range(1, n):
        e.append(((0, c), (1, c)))
        e.append(((1, c), (2, c)))
        e.append(((3, c), (4, c)))
    return e


def m5_witness_motif(n):
    """Period-3 motif read off from the m=5 witness solver at large n.

    Per column c (0-indexed):
      - V (verticals (r,c)-(r+1,c) for r=0..3):
          c % 3 == 0:  V = 1111  (full ladder)
          c % 3 == 1:  V = 1000  (only top vertical (0,c)-(1,c))
          c % 3 == 2:  V = 1000

      - H (horizontals (r,c)-(r,c+1) for r=0..4):
          c % 3 == 0:  H = 10111  (top spine + rows 2,3,4 spine, but row 1 absent)
          c % 3 == 1:  H = 10000  (only top spine)
          c % 3 == 2:  H = 10111

    To match m·n − 1 edges exactly for all n, we additionally drop the col-0
    full-ladder rung (1, 0)-(2, 0) when n ≡ 0 (mod 3) to break a cycle that
    would otherwise form. (This makes (2, 0) hang from the bottom rather
    than the top in such grids — same overall structure, one bridge moved.)
    """
    e = []
    m = 5
    for c in range(n):
        # verticals
        if c % 3 == 0:
            for r in range(4):
                # When n%3==0 we drop one rung of the col-0 ladder later.
                e.append(((r, c), (r + 1, c)))
        else:
            e.append(((0, c), (1, c)))
        # horizontals to next col
        if c == n - 1:
            continue
        if c % 3 in (0, 2):
            e.append(((0, c), (0, c + 1)))
            e.append(((2, c), (2, c + 1)))
            e.append(((3, c), (3, c + 1)))
            e.append(((4, c), (4, c + 1)))
        else:  # c%3 == 1
            e.append(((0, c), (0, c + 1)))
    # Boundary correction for n % 3 == 0: the last column has c%3==2 and
    # would have 4 outgoing horizontals in the interior pattern but has none
    # as the last col; compensate by completing column n-1 as a full ladder.
    # This recovers 2n full-degree but is 1 short of the optimum 2n+1.
    if n % 3 == 0 and n >= 3:
        e.append(((1, n - 1), (2, n - 1)))
        e.append(((2, n - 1), (3, n - 1)))
        e.append(((3, n - 1), (4, n - 1)))
    return e


# -------- m=6 attempts --------

def m6_witness_motif(n):
    """Period-4 motif read off from the m=6 witness solver at n=24.

    Per column c, transcribed directly from the n=24 witness tree:

      c=0     : V=10111  H=100111  (left boundary, special)
      c=1     : V=10000  H=101001  (left boundary, special)
      c=2..n-3 (period 4): with c' = (c - 2) % 4:
        c'=0  : V=11101  H=101001
        c'=1  : V=10001  H=100101
        c'=2  : V=10111  H=100101
        c'=3  : V=10001  H=101001
      c=n-2   : V=10000  H=101111  (right boundary, special)
      c=n-1   : V=11111  H=000000  (right boundary, full ladder)

    For this motif to align cleanly we need (n - 4) % 4 == 0, i.e. n ≡ 0
    (mod 4). For other n we'd need different boundary corrections; we mark
    those as not yet supported.
    """
    m = 6
    e = []
    if n < 4 or (n - 4) % 4 != 0:
        # Pattern only works for n = 4, 8, 12, 16, 20, 24, ...
        return []

    def add_v(c, vbits):
        for r in range(m - 1):
            if vbits[r] == "1":
                e.append(((r, c), (r + 1, c)))

    def add_h(c, hbits):
        if c == n - 1:
            return
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


def m6_attempt_v1(n):
    """Top + bottom spines, full ladder at c=0, then per c>=1 hang row 1 off
       row 0, row 4 off row 5, and connect 2-3 via spine alternation."""
    # We have 5n-1 needed edges.  Spines 2(n-1) + col-0 ladder 5 +
    # per c>=1: (0,c)-(1,c), (4,c)-(5,c), and one of (2,c)-(3,c) etc.
    # Try: per c>=1, hang each interior row from the spines symmetrically.
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((5, c), (5, c + 1)))
    for r in range(5):
        e.append(((r, 0), (r + 1, 0)))
    for c in range(1, n):
        e.append(((0, c), (1, c)))
        e.append(((1, c), (2, c)))
        e.append(((3, c), (4, c)))
        e.append(((4, c), (5, c)))
    # Edges: 2(n-1) + 5 + 4(n-1) = 6n - 1. We need m*n - 1 = 6n - 1. ✓
    return e


# -------- m=7 attempts --------

def m7_general_tile(n):
    """Generalization that gives 2n full-degree (top + bottom row) for any m.
       Same structure as m6_attempt_v1 but generalized."""
    m = 7
    e = []
    for c in range(n - 1):
        e.append(((0, c), (0, c + 1)))
        e.append(((m - 1, c), (m - 1, c + 1)))
    for r in range(m - 1):
        e.append(((r, 0), (r + 1, 0)))
    for c in range(1, n):
        e.append(((0, c), (1, c)))
        e.append(((m - 2, c), (m - 1, c)))
        for r in range(1, m - 2):
            e.append(((r, c), (r + 1, c)))
    return e


def m_general_tile(m: int):
    """Make a builder for arbitrary m: spines + col-0 ladder + per-column
       full vertical chain except the spine-spine endpoints."""
    def builder(n):
        e = []
        for c in range(n - 1):
            e.append(((0, c), (0, c + 1)))
            e.append(((m - 1, c), (m - 1, c + 1)))
        for r in range(m - 1):
            e.append(((r, 0), (r + 1, 0)))
        for c in range(1, n):
            for r in range(m - 1):
                e.append(((r, c), (r + 1, c)))
        return e
    return builder


# -------- main --------

def evaluate(name, m, builder, ns=range(2, 22)):
    known = load_known()
    print(f"=== {name} (m={m}) ===")
    print(f"{'n':>4} {'edges':>6} {'valid':>6} {'count':>6} {'P*':>5} {'gap':>5}")
    for n in ns:
        try:
            edges = builder(n)
        except Exception as exc:
            print(f"  n={n:>2}  builder error: {exc}")
            continue
        ok, why = is_spanning_tree(m, n, edges)
        cnt = count_full_degree(m, n, edges) if ok else None
        target = known.get((m, n), closed_form_P(m, n))
        gap = (target - cnt) if (ok and target is not None) else "—"
        valid = "yes" if ok else f"no({why[:8]})"
        cnt_s = str(cnt) if ok else "—"
        target_s = str(target) if target is not None else "?"
        print(f"  {n:>2}  {len(edges):>6}  {valid:>6}  {cnt_s:>6}  {target_s:>5}  {gap}")
    print()


def main():
    evaluate("m=3 attempt v1 (spines + all 1-2 + col-0 0-1)", 3, m3_attempt_v1)
    evaluate("m=3 attempt v2 (period-3 vertical alt)", 3, m3_attempt_v2)
    evaluate("m=3 witness motif (period-3)", 3, m3_witness_motif)
    evaluate("m=4 double-spine (known optimal)", 4, m4_double_spine)
    evaluate("m=5 attempt v2 (spines + col-0 ladder + per-c hangers)", 5, m5_attempt_v2)
    evaluate("m=5 witness motif (period-3 read off)", 5, m5_witness_motif)
    evaluate("m=6 attempt v1 (spines + col-0 ladder + per-c)", 6, m6_attempt_v1)
    evaluate("m=6 witness motif (period-4)", 6, m6_witness_motif)
    evaluate("m=7 general tile (spines + col-0 ladder + full verts)", 7, m7_general_tile)
    evaluate("m=8 general tile", 8, m_general_tile(8))


if __name__ == "__main__":
    main()
