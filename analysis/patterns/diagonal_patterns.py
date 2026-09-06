#!/usr/bin/env python3
"""Candidate parametric U-patterns for the diagonal construction.

Rows are printed using `U` for non-full vertices and `.` for full vertices,
suitable for piping into `dual_decycling.py`.

Status by residue (n mod 3):

  residue 1 (n = 3k+1, k >= 1):
      `residue_one_pattern(n)` is a verified construction. See
      `analysis/patterns/check_diagonal_patterns.py`, which validates the construction
      through n = 40 by completing the forced forest to a spanning tree.

  residue 0 (n = 3k, k >= 2):
      `residue_zero_pattern(n)` returns cached exact witnesses for
      n in {6, 9, 12, 15, 18}, then the exact phase-boundary family for every
      n >= 21. `residue_zero_skeleton_pattern(n)` retains the older surplus
      scaffold for analysis.

  residue 2 (n = 3k+2, k >= 1):
      `residue_two_pattern(n)` returns only canonical target-count witnesses:
      cached exact witnesses through n=14 and revised bases at n=17,20.
      `residue_two_affine_pattern(n)` remains the separate surplus family.

The residue-2 skeleton remains off by an `O(k)` correction. For residue zero,
the phase-boundary family absorbs the correction with `k-2` seam rows.
"""

from __future__ import annotations

import argparse
from analysis._paths import analysis_path



def q_old_formula(n: int) -> int:
    """Original diagonal U-count, retained for residue-two equality analysis."""
    k, r = divmod(n, 3)
    if r == 0:
        return 6 * k * k - 3 * k + 2
    if r == 1:
        return 6 * k * k + k + 1
    return 6 * k * k + 5 * k + 3


def q_formula(n: int) -> int:
    """Current candidate minimum U-count, including the n=17 residue-two break."""
    k, r = divmod(n, 3)
    return q_old_formula(n) + int(r == 2 and k >= 5)


# -----------------------------------------------------------------------------
# Residue 1: n = 3k + 1.
# -----------------------------------------------------------------------------


def residue_one_pattern(n: int) -> list[str]:
    """Verified parametric pattern for n = 3k + 1, k >= 1.

    The pattern consists of `k` 3-row blocks plus an empty bottom row.

    For each non-final 3-row block:
      row 3t:     only column 1 is in U
      rows 3t+1, 3t+2: columns 1..n-1 are in U

    For the final 3-row block (t = k - 1):
      row 3(k-1):     only column 1 is in U
      row 3(k-1)+1:   columns 1..n-1 are in U
      row 3(k-1)+2:   columns 0..n-1 are in U  (extra left anchor)
      row 3(k-1)+3 = n-1: empty (all full)

    Cardinality: (k-1)(2n-1) + 2n = 6k^2 + k + 1 = q(3k+1).

    Validated against `check_diagonal_patterns.py` for every n in [4, 40].
    """
    if n % 3 != 1 or n < 4:
        raise ValueError("residue_one_pattern requires n >= 4 and n ≡ 1 mod 3")
    k = (n - 1) // 3
    u = [[False for _ in range(n)] for _ in range(n)]
    for t in range(k):
        r0 = 3 * t
        u[r0][1] = True
        for c in range(1, n):
            u[r0 + 1][c] = True
        if t + 1 == k:
            for c in range(n):
                u[r0 + 2][c] = True
        else:
            for c in range(1, n):
                u[r0 + 2][c] = True
    return ["".join("U" if x else "." for x in row) for row in u]


# -----------------------------------------------------------------------------
# Residue 2: n = 3k + 2 with k >= 1.
#
# Skeleton: a residue-1-style top sandwich (rows 0, 1) + column stripes
# (rows 2..n-3) + a mirror residue-1 bottom sandwich (rows n-2, n-1).
# A horizontal "bridge row" at row 2 plugs in single-U bridges across each
# F-column to keep the dual graph connected through the column stripes.
# Right-boundary anchoring uses two U cells in column n-1.
#
# Status:
#   * n = 5 (k = 1): exact match of the conjectured q(5) = 14. Verified.
#   * n >= 8: the skeleton overshoots the conjectured count by exactly k
#     (1 per F-column gap not yet absorbed). The extension layer that
#     subtracts those k cells is not yet parametric; for these n we fall
#     back to either the cached witness or an SA-tuned candidate.
# -----------------------------------------------------------------------------


def residue_two_skeleton_pattern(n: int) -> list[str]:
    """Skeleton residue-2 pattern. May not match q(n) exactly.

    See module docstring. The skeleton is dual-connected and forest-completable
    by construction (verified for n in {5, 8, 11, 14}). For n = 5 it gives the
    exact count q(5) = 14. For n >= 8 it gives q(n) + k extra U's. Of these,
    k - 1 correspond to the F-column bridges added at row 2.

    Use `analysis/patterns/construction_lab.py` to verify the skeleton against
    `dual_connectivity_check` and `forest_completion_check` for any specific n.
    """
    if n % 3 != 2 or n < 5:
        raise ValueError("residue_two_skeleton_pattern requires n >= 5, n ≡ 2 mod 3")
    k = (n - 2) // 3
    u = [[False for _ in range(n)] for _ in range(n)]
    # Top sandwich: row 0 sparse at col 1, row 1 dense at cols 1..n-1.
    u[0][1] = True
    for c in range(1, n):
        u[1][c] = True
    # Bottom sandwich: row n-2 dense at cols 1..n-2, row n-1 sparse at cols 1, n-2.
    for c in range(1, n - 1):
        u[n - 2][c] = True
    u[n - 1][1] = True
    u[n - 1][n - 2] = True
    # Middle rows: column stripes plus col n-2 anchor.
    for r in range(2, n - 2):
        for t in range(k):
            u[r][3 * t + 1] = True
            u[r][3 * t + 2] = True
        u[r][n - 2] = True
    # Bridges across F-columns 3, 6, ..., n-5 at row 2.
    for t in range(1, k):
        u[2][3 * t] = True
    # Right-boundary OUT anchor: two cells in col n-1.
    u[2][n - 1] = True
    u[3][n - 1] = True
    return ["".join("U" if x else "." for x in row) for row in u]


def residue_two_pattern(n: int) -> list[str]:
    """Return a canonical target-count residue-two construction.

    Cached exact witnesses cover n=5,8,11,14. Revised target-count bases are
    known at n=17,20. Unsupported larger widths deliberately do not fall back
    to the surplus affine family.
    """
    if n in _RESIDUE_TWO_EXPLICIT:
        return list(_RESIDUE_TWO_EXPLICIT[n])
    if n in (17, 20):
        return residue_two_revised_pattern(n)
    if n % 3 != 2 or n < 5:
        raise ValueError("residue_two_pattern requires n >= 5, n ≡ 2 mod 3")
    raise KeyError(f"no target-count residue-two construction known for n={n}")


_RESIDUE_TWO_AFFINE_17 = [
    ".U...............",
    ".UUUUUUUUUUUUUUUU",
    ".UUUU.UU.UU.UU.UU",
    ".UU.UUUU.UU.UUUU.",
    ".UU.UU.UUUU.U.UU.",
    ".UU.UU.UU.UUU.UU.",
    ".UU.UU.UU.U.UUUU.",
    ".UU.UU.UUUU.UU.U.",
    ".UU.UU.U.UU.UUUU.",
    ".UU.UU.UUUU.U.UU.",
    ".UU.UU.UU.UUU.UU.",
    ".UU.UU.UU.UUU.UU.",
    ".UU.UU.UU.U.UUUU.",
    ".UU.UU.UU.UUUU.U.",
    ".UU.UU.UU.UU.UUU.",
    ".UUUUUUUUUUUUUUU.",
    ".U.............U.",
]


def residue_two_revised_pattern(n: int) -> list[str]:
    """Return a canonical revised target-count base at n=17 or n=20."""
    if n == 17:
        return list(_RESIDUE_TWO_AFFINE_17)
    if n == 20:
        path = analysis_path("residue_two_phase_front_witness.txt")
        rows = [line.strip() for line in path.read_text().splitlines() if line.strip()]
        if len(rows) != n or any(len(row) != n for row in rows):
            raise ValueError(f"invalid canonical residue-two witness at {path}")
        return rows
    raise KeyError(f"no revised residue-two base cached for n={n}")


def residue_two_affine_pattern(n: int) -> list[str]:
    """Return the affine residue-two word pattern for n=3k+2, k>=5."""
    if n % 3 != 2 or n < 17:
        raise ValueError("residue_two_affine_pattern requires n >= 17, n ≡ 2 mod 3")
    rows = list(_RESIDUE_TWO_AFFINE_17)
    while len(rows) < n:
        old_n = len(rows)
        row_indices = [*range(9), 9, 10, 11, *range(9, old_n)]
        column_indices = [*range(4), 4, 5, 6, *range(4, old_n)]
        rows = ["".join(rows[row][column] for column in column_indices) for row in row_indices]
    return rows


# -----------------------------------------------------------------------------
# Residue 0: n = 3k, k >= 2.
#
# Skeleton: a residue-1-style top sandwich (rows 0, 1) + column stripes
# (rows 2..n-3) + a mirror bottom sandwich (rows n-2, n-1). The skeleton is
# similar to residue 2 but does not require the right-boundary anchor since
# column stripes naturally extend to col n-1 (n is divisible by 3, so the
# stripes fit perfectly).
#
# Status:
#   * the skeleton is one of several `O(k)`-far valid candidates; it does
#     not yet match q(n) exactly for k >= 2.
# -----------------------------------------------------------------------------


def residue_zero_skeleton_pattern(n: int) -> list[str]:
    """Skeleton residue-0 pattern; structured but not yet count-exact.

    Uses the same residue-1 sandwich top/bottom and column stripes in the
    middle. The trailing pair of columns (cols n-2, n-1) inherits the
    `.UU` stripe so col n-1 is U everywhere in the middle rows. No
    additional anchoring needed.
    """
    if n % 3 != 0 or n < 6:
        raise ValueError("residue_zero_skeleton_pattern requires n >= 6, n ≡ 0 mod 3")
    k = n // 3
    u = [[False for _ in range(n)] for _ in range(n)]
    # Top sandwich.
    u[0][1] = True
    for c in range(1, n):
        u[1][c] = True
    # Bottom sandwich.
    for c in range(1, n):
        u[n - 2][c] = True
    u[n - 1][1] = True
    # Middle rows: column stripes (.UU)^k.
    for r in range(2, n - 2):
        for t in range(k):
            u[r][3 * t + 1] = True
            u[r][3 * t + 2] = True
    # Bridges at row 2 to break the F-cols.
    for t in range(1, k):
        u[2][3 * t] = True
    return ["".join("U" if x else "." for x in row) for row in u]


def residue_zero_improved_pattern(n: int) -> list[str]:
    """Return the dual-connected residue-zero scaffold with surplus n/3 - 2."""
    rows = [list(row) for row in residue_zero_skeleton_pattern(n)]
    for r in range(2, n - 3, 3):
        rows[r][n - 1] = "."
    return ["".join(row) for row in rows]


def residue_zero_phase_pattern(n: int) -> list[str]:
    """Return the exact phase-boundary construction for n = 3k, k >= 7."""
    if n % 3 != 0 or n < 21:
        raise ValueError("residue_zero_phase_pattern requires n >= 21, n ≡ 0 mod 3")
    k = n // 3

    def phase_row(a: int, seam: bool = False) -> str:
        dots = set(range(0, 3 * a + 1, 3))
        tail_start = 3 * a + (2 if seam else 5)
        dots.update(range(tail_start, n, 3))
        return "".join("." if c in dots else "U" for c in range(n))

    interior = [
        phase_row(4),
        phase_row(3),
        phase_row(2),
        phase_row(2, seam=True),
        phase_row(1),
        phase_row(0),
        phase_row(0, seam=True),
        phase_row(0),
        phase_row(1, seam=True),
        phase_row(1),
        phase_row(2),
        phase_row(3, seam=True),
        phase_row(3),
        phase_row(4, seam=True),
        phase_row(4),
        phase_row(5),
        phase_row(6),
    ]
    for size in range(8, k + 1):
        interior = [
            phase_row(size - 3),
            phase_row(size - 3, seam=True),
            *interior,
            phase_row(size - 1),
        ]

    return [
        "." * n,
        "U" * n,
        *interior,
        "." + "U" * (n - 1),
        ".U" + "." * (n - 2),
    ]


def residue_zero_pattern(n: int) -> list[str]:
    """Best available residue-0 pattern."""
    if n in _RESIDUE_ZERO_EXPLICIT:
        return list(_RESIDUE_ZERO_EXPLICIT[n])
    if n >= 21:
        return residue_zero_phase_pattern(n)
    return residue_zero_skeleton_pattern(n)


_RESIDUE_ZERO_EXPLICIT: dict[int, list[str]] = {
    6: [
        "......",
        "UUUUUU",
        ".UUUU.",
        ".U..UU",
        ".UUUUU",
        ".UU...",
    ],
    9: [
        ".........",
        "UUUUUUUUU",
        ".UUUUU.UU",
        ".U...UUU.",
        ".UUUUUUU.",
        ".UUUU..U.",
        ".U..UUUU.",
        ".UUUUUUU.",
        ".UU....U.",
    ],
    12: [
        "............",
        "UUUUUUUUUUUU",
        ".UUUUUUUU.UU",
        ".U......UUU.",
        ".UUUUUUUUUU.",
        ".UUUUUUU..U.",
        ".U.....UUUU.",
        ".UUUUUUUUUU.",
        ".UU.UUU...U.",
        ".UUUU.UUUUU.",
        ".UUUUUUUUUU.",
        ".U........U.",
    ],
    15: [
        "...............",
        "UUUUUUUUUUUUUUU",
        ".UU.UUUUUUUUUU.",
        ".UU.UU.......U.",
        ".UU.UUUUUUUUUU.",
        ".UU.U.UU.UU.UU.",
        ".UUUU.UU.UU.UU.",
        ".U.UU.UU.UU.UU.",
        ".UUUU.UU.UU.UU.",
        ".UU.UUUU.UU.UU.",
        ".UU.UU.UUUU.UU.",
        ".UU.UU.UU.UUUU.",
        ".UU.UU.UU.UU.U.",
        ".UUUUUUUUUUUUU.",
        ".U..........UU.",
    ],
    18: [
        "..................",
        "UUUUUUUUUUUUUUUUUU",
        ".UU.UU.UUUUUUUUUU.",
        ".UU.UU.UU.......U.",
        ".UU.UU.UUUUUUUUUU.",
        ".UU.UUUU.UU.UU.UU.",
        ".UUUU.UU.UU.UU.UU.",
        ".U.UU.UU.UU.UU.UU.",
        ".UUUU.UU.UU.UU.UU.",
        ".UU.U.UU.UU.UU.UU.",
        ".UU.UUUU.UU.UU.UU.",
        ".UU.UU.U.UU.UU.UU.",
        ".UU.UU.UUUU.UU.UU.",
        ".UU.UU.UU.UUUU.UU.",
        ".UU.UU.UU.UU.UUUU.",
        ".UU.UU.UU.UU.UU.U.",
        ".UUUUUUUUUUUUUUUU.",
        ".U.............UU.",
    ],
    21: [
        ".....................",
        "UUUUUUUUUUUUUUUUUUUUU",
        ".UU.UU.UU.UU.UUUU.UU.",
        ".UU.UU.UU.UUUU.UU.UU.",
        ".UU.UU.UUUU.UU.UU.UU.",
        ".UU.UU.U.UU.UU.UU.UU.",
        ".UU.UUUU.UU.UU.UU.UU.",
        ".UUUU.UU.UU.UU.UU.UU.",
        ".U.UU.UU.UU.UU.UU.UU.",
        ".UUUU.UU.UU.UU.UU.UU.",
        ".UU.U.UU.UU.UU.UU.UU.",
        ".UU.UUUU.UU.UU.UU.UU.",
        ".UU.UU.UUUU.UU.UU.UU.",
        ".UU.UU.UU.U.UU.UU.UU.",
        ".UU.UU.UU.UUUU.UU.UU.",
        ".UU.UU.UU.UU.U.UU.UU.",
        ".UU.UU.UU.UU.UUUU.UU.",
        ".UU.UU.UU.UU.UU.UUUU.",
        ".UU.UU.UU.UU.UU.UU.UU",
        ".UUUUUUUUUUUUUUUUUUUU",
        ".U...................",
    ],
}


def residue_zero_explicit_pattern(n: int) -> list[str]:
    """Return a cached exact residue-0 witness where available."""
    if n not in _RESIDUE_ZERO_EXPLICIT:
        raise KeyError(f"no explicit residue-0 pattern cached for n={n}")
    return list(_RESIDUE_ZERO_EXPLICIT[n])


# -----------------------------------------------------------------------------
# Explicit residue-2 patterns from `fullub-pattern` (non-parametric).
#
# These are exact optimal patterns extracted from the Rust solver. They are
# kept as concrete witnesses while a parametric family is being developed.
# -----------------------------------------------------------------------------


_RESIDUE_TWO_EXPLICIT: dict[int, list[str]] = {
    5: [
        "....U",
        "UUUUU",
        "U.UU.",
        "UUUU.",
        "...U.",
    ],
    8: [
        "........",
        "UUUUUUUU",
        ".UU.UUU.",
        ".UUUU.U.",
        ".U.UUUU.",
        ".UUU.UU.",
        ".UUUUUUU",
        ".U.....U",
    ],
    11: [
        ".U.........",
        ".UUUUUUUUUU",
        ".UU.UUUUUU.",
        ".UUUU....U.",
        ".U.UUUUUUU.",
        ".UUU.UU.UU.",
        ".UUUUUU.UU.",
        ".U....UUUU.",
        ".UUUUUUU.UU",
        ".UUUUUUUUUU",
        ".U.........",
    ],
    14: [
        ".U............",
        ".UUUUUUUUUUUUU",
        ".UUUU.UU.UU.UU",
        ".UU.UUUU.UUUU.",
        ".UU.UU.UUU.UU.",
        ".UU.UU.UUU.UU.",
        ".UU.UU.U.U.UU.",
        ".UU.UU.UUU.UU.",
        ".UU.UU.UUU.UU.",
        ".UU.UU.U.UUUU.",
        ".UU.UU.UUUU.U.",
        ".UU.UU.UU.UUU.",
        ".UUUUUUUUUUUU.",
        ".U..........U.",
    ],
}


def residue_two_explicit_pattern(n: int) -> list[str]:
    """Return an explicit optimal residue-2 pattern for small n where one is cached."""
    if n not in _RESIDUE_TWO_EXPLICIT:
        raise KeyError(f"no explicit pattern cached for n={n}")
    return list(_RESIDUE_TWO_EXPLICIT[n])


# -----------------------------------------------------------------------------
# Status registry.
# -----------------------------------------------------------------------------


# Explicit-cache registries. Parametric families are checked separately.
STATUS_RESIDUE_ONE: dict[int, str] = {n: "verified" for n in range(4, 41) if n % 3 == 1}
STATUS_RESIDUE_TWO: dict[int, str] = {
    5: "old-formula-exact",
    8: "old-formula-exact",
    11: "old-formula-exact",
    14: "old-formula-exact",
    17: "revised-globally-exact",
    20: "revised-construction",
}
STATUS_RESIDUE_ZERO: dict[int, str] = {
    n: "explicit" for n in (6, 9, 12, 15, 18, 21)
}


# -----------------------------------------------------------------------------
# Rejected experimental patterns kept for reference.
# -----------------------------------------------------------------------------


def residue_zero_experimental_pattern(n: int) -> list[str]:
    """Rejected count-matching pattern for n = 3k. Disconnected dual."""
    if n % 3 != 0 or n < 6:
        raise ValueError
    k = n // 3
    u = [[False for _ in range(n)] for _ in range(n)]
    for t in range(k):
        r0 = 3 * t
        u[r0][1] = True
        for c in range(1, n - 1):
            u[r0 + 1][c] = True
        if t + 1 == k:
            for c in range(n):
                u[r0 + 2][c] = True
        else:
            for c in range(1, n - 1):
                u[r0 + 2][c] = True
    return ["".join("U" if x else "." for x in row) for row in u]


def residue_two_experimental_pattern(n: int) -> list[str]:
    """Rejected count-matching pattern for n = 3k+2. Disconnected dual."""
    if n % 3 != 2 or n < 5:
        raise ValueError
    k = (n - 2) // 3
    u = [[False for _ in range(n)] for _ in range(n)]
    for t in range(k):
        r0 = 3 * t
        u[r0][1] = True
        for c in range(1, n - 1):
            u[r0 + 1][c] = True
            u[r0 + 2][c] = True
    for c in range(n):
        u[n - 2][c] = True
    for j in range(k + 1):
        c = 1 + 3 * j
        if c < n:
            u[n - 1][c] = True
    return ["".join("U" if x else "." for x in row) for row in u]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument(
        "--experimental",
        action="store_true",
        help="print rejected count-matching patterns for residues 0 and 2",
    )
    args = parser.parse_args()
    if args.n % 3 == 0:
        if args.experimental:
            rows = residue_zero_experimental_pattern(args.n)
        else:
            rows = residue_zero_pattern(args.n)
    elif args.n % 3 == 1:
        rows = residue_one_pattern(args.n)
    else:
        if args.experimental:
            rows = residue_two_experimental_pattern(args.n)
        else:
            rows = residue_two_pattern(args.n)
    count = sum(row.count("U") for row in rows)
    print(f"# n={args.n} nonfull={count} conjectured_q={q_formula(args.n)}")
    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
