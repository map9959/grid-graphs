#!/usr/bin/env python3
"""Slab insertion for residue-2 q-construction (incomplete).

Given a valid q-witness at n_old = 3k+2, attempts to construct a q-witness at
n_new = n_old + 3 by inserting a 3-row + 3-col slab at position (n_old-2,
n_old-3) (just before the bottom 2 rows / right 2 cols of the old pattern).

Status:
  * `slab_extend_n8_to_n11`: WORKS exactly. Reproduces cached n=11 from cached
    n=8 using a specific slab + 3 cell modifications.
  * `slab_extend_general`: PARTIALLY WORKS. The slab content alone overcounts
    by 1 cell when applied iteratively. The 3 cell mods only have effect when
    going from "n=8 envelope" (top-row empty, row-1 fully dense incl col 0) to
    "n=11 envelope" (top-row sparse col 1, row-1 cols 1..n-1, sparse col-1
    bottom). After that transition, the mods become no-ops.
  * Iterative slab (n=11 -> n=14 -> n=17 -> ...) overshoots q by k_old - 2
    cells per iteration AND breaks dual connectivity.

The slab content is HAND-DERIVED from cached patterns, NOT proven to work for
general k. It is a starting point for further investigation.

The key remaining task: identify (i) the correct ENVELOPE-PRESERVING slab for
n=11+ patterns, and (ii) the correct 1-cell adjustment that compensates for
the slab's overcount.
"""

from __future__ import annotations

import sys

sys.path.insert(0, "analysis")

from construction_lab import run_check
from diagonal_patterns import residue_two_explicit_pattern


def slab_extend_general(rows_old: list[str], apply_mods: bool = True) -> list[str]:
    """Insert 3 rows + 3 cols at position (n_old-2, n_old-3) into rows_old.

    Slab content is hand-derived from the n=8 -> n=11 example. Applies cell
    modifications (ADD (0,1), REMOVE (1,0), REMOVE (n_new-1, n_new-1)) which
    transition from n=8-style envelope to n=11-style envelope.

    Verified: slab_extend_general(cached_n8) == cached_n11 (exact match).

    Known limitation: slab_extend_general(cached_n11) overshoots q(14) by 1
    and has 2 cells with broken dual connectivity. Needs refinement.
    """
    n_old = len(rows_old)
    if n_old % 3 != 2:
        raise ValueError("n_old must be 3k+2")
    n_new = n_old + 3
    ir = n_old - 2
    ic = n_old - 3
    new = [["." for _ in range(n_new)] for _ in range(n_new)]

    def map_r(r: int) -> int:
        return r if r < ir else r + 3

    def map_c(c: int) -> int:
        return c if c < ic else c + 3

    # Copy old data
    for r in range(n_old):
        for c in range(n_old):
            if rows_old[r][c] == "U":
                new[map_r(r)][map_c(c)] = "U"

    if apply_mods:
        # Cell modifications (envelope transition)
        new[0][1] = "U"
        new[1][0] = "."
        new[n_new - 1][n_new - 1] = "."

    # Insert slab rows ir, ir+1, ir+2
    for c in range(1, ic + 2):
        new[ir][c] = "U"
    for c in range(ic + 3, n_new - 1):
        new[ir][c] = "U"

    new[ir + 1][1] = "U"
    for c in range(ic + 1, n_new - 1):
        new[ir + 1][c] = "U"

    for c in range(1, ic + 3):
        new[ir + 2][c] = "U"
    for c in range(ic + 4, n_new):
        new[ir + 2][c] = "U"

    # Insert slab cols ic, ic+1, ic+2
    for r in [1, 2]:
        new[r][ic] = "U"
    for r in range(4, ir + 1):
        new[r][ic] = "U"
    for r in range(ir + 2, n_new - 1):
        new[r][ic] = "U"

    for r in [1, 2]:
        new[r][ic + 1] = "U"
    for r in range(4, n_new - 1):
        new[r][ic + 1] = "U"

    for r in [1, 2, 4]:
        new[r][ic + 2] = "U"
    for r in range(ir + 1, n_new - 1):
        new[r][ic + 2] = "U"

    return ["".join(row) for row in new]


def main():
    """Demonstrate slab insertion: works for n=8->n=11, partial for n=11->n=14."""
    n8 = residue_two_explicit_pattern(8)
    n11 = residue_two_explicit_pattern(11)
    n14 = residue_two_explicit_pattern(14)

    print("Test 1: slab_extend(n=8) should match cached n=11")
    n11_recon = slab_extend_general(n8)
    match = all(n11_recon[r] == n11[r] for r in range(11))
    info = run_check(11, n11_recon)
    print(f"  match cached: {match}, valid: {info['all_ok']}, |U|={info['u_count']}/{info['expected_u']}")

    print()
    print("Test 2: slab_extend(n=11) -> n=14 (mods should be no-ops)")
    n14_recon = slab_extend_general(n11, apply_mods=False)
    info = run_check(14, n14_recon)
    print(f"  valid: {info['all_ok']}, |U|={info['u_count']}/{info['expected_u']}, dual={info['dual_connected']}/{info['dual_total']}, forest={info['forest_ok']}")

    print()
    print("Test 3: slab_extend(n=11) -> n=14 with mods (should also be no-ops mostly)")
    n14_recon2 = slab_extend_general(n11, apply_mods=True)
    info = run_check(14, n14_recon2)
    print(f"  valid: {info['all_ok']}, |U|={info['u_count']}/{info['expected_u']}, dual={info['dual_connected']}/{info['dual_total']}, forest={info['forest_ok']}")


if __name__ == "__main__":
    main()
