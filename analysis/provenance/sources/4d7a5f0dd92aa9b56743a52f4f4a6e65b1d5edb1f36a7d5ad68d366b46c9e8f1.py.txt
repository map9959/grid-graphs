#!/usr/bin/env python3
"""Iterative test bench for candidate diagonal U-pattern constructions.

This is the workhorse for synthesizing residue-0 and residue-2 patterns.
Given a candidate generator function `n -> rows`, it checks:

  1. |U| matches conjectured q(n).
  2. The dual graph of U-U primal edges connects every cell-face to OUT.
  3. The forced graph (G - E(G[U])) is a forest.
  4. The forced forest can be greedily completed to a spanning tree. Since all
     non-U-U grid edges are forced already, every added edge is U-U.

This module imports nothing from `diagonal_patterns` to avoid circular
dependency: candidate generators live here during exploration, then the
verified ones get promoted to `diagonal_patterns.py`.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from typing import Callable, Iterable

from diagonal_patterns import q_formula, q_old_formula

class DSU:
    def __init__(self, items: Iterable):
        self.parent = {x: x for x in items}

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        self.parent[rb] = ra
        return True


def grid_degree(n: int, r: int, c: int) -> int:
    return (r > 0) + (r + 1 < n) + (c > 0) + (c + 1 < n)


def dual_connectivity_check(rows: list[str]) -> tuple[bool, int, int]:
    """Return `(all_connected, connected, total)` for the dual face graph."""
    n = len(rows)
    is_u = [[ch == "U" for ch in row] for row in rows]
    faces: list = ["OUT"] + [(r, c) for r in range(n - 1) for c in range(n - 1)]
    dsu = DSU(faces)

    def dh(r, c):
        if r == 0:
            return "OUT", (0, c)
        if r == n - 1:
            return "OUT", (n - 2, c)
        return (r - 1, c), (r, c)

    def dv(r, c):
        if c == 0:
            return "OUT", (r, 0)
        if c == n - 1:
            return "OUT", (r, n - 2)
        return (r, c - 1), (r, c)

    for r in range(n):
        for c in range(n - 1):
            if is_u[r][c] and is_u[r][c + 1]:
                a, b = dh(r, c)
                dsu.union(a, b)
    for r in range(n - 1):
        for c in range(n):
            if is_u[r][c] and is_u[r + 1][c]:
                a, b = dv(r, c)
                dsu.union(a, b)
    root = dsu.find("OUT")
    connected = sum(1 for f in faces if dsu.find(f) == root)
    return connected == len(faces), connected, len(faces)


def forest_completion_check(rows: list[str]) -> tuple[bool, str]:
    """Verify the forced graph is acyclic and can be completed to a spanning tree.

    Returns `(ok, reason)`.
    """
    n = len(rows)
    is_u = [ch == "U" for row in rows for ch in row]
    is_full = [not x for x in is_u]
    dsu = DSU(range(n * n))
    forced = []
    optional = []
    for r in range(n):
        for c in range(n):
            a = r * n + c
            if c + 1 < n:
                b = a + 1
                if is_full[a] or is_full[b]:
                    if not dsu.union(a, b):
                        return False, "forced edges contain a cycle"
                    forced.append((a, b))
                else:
                    optional.append((a, b))
            if r + 1 < n:
                b = a + n
                if is_full[a] or is_full[b]:
                    if not dsu.union(a, b):
                        return False, "forced edges contain a cycle"
                    forced.append((a, b))
                else:
                    optional.append((a, b))
    edges = list(forced)
    for a, b in optional:
        if dsu.union(a, b):
            edges.append((a, b))
    if len(edges) != n * n - 1:
        return False, f"completion has {len(edges)} edges, expected {n*n-1}"
    root = dsu.find(0)
    if any(dsu.find(v) != root for v in range(n * n)):
        return False, "completion is disconnected"
    # Every full vertex must end up at full grid degree (it should because every
    # incident grid edge is forced into the tree).
    deg = [0] * (n * n)
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    for r in range(n):
        for c in range(n):
            v = r * n + c
            if is_full[v] and deg[v] != grid_degree(n, r, c):
                return False, f"full vertex ({r},{c}) only has degree {deg[v]}"
    return True, "ok"


def run_check(
    n: int,
    rows: list[str],
    verbose: bool = False,
    *,
    expected_u: int | None = None,
) -> dict:
    if expected_u is None:
        expected_u = q_formula(n)
    actual_u = sum(row.count("U") for row in rows)
    info = {
        "n": n,
        "u_count": actual_u,
        "expected_u": expected_u,
        "u_match": actual_u == expected_u,
    }
    dual_ok, conn, total = dual_connectivity_check(rows)
    info["dual_ok"] = dual_ok
    info["dual_connected"] = conn
    info["dual_total"] = total
    forest_ok, reason = forest_completion_check(rows)
    info["forest_ok"] = forest_ok
    info["forest_reason"] = reason
    info["all_ok"] = info["u_match"] and dual_ok and forest_ok
    if verbose:
        print(f"n={n}: |U|={actual_u} (target {expected_u}) "
              f"dual={conn}/{total} forest={forest_ok} -> {info['all_ok']}")
    return info


def sweep(generator: Callable[[int], list[str]], ns: Iterable[int],
          verbose: bool = True) -> list[dict]:
    out = []
    for n in ns:
        try:
            rows = generator(n)
        except Exception as exc:  # pragma: no cover
            print(f"n={n}: GENERATOR FAILED: {exc}")
            continue
        info = run_check(n, rows, verbose=verbose)
        out.append(info)
        if verbose and not info["all_ok"]:
            print("  rows:")
            for row in rows:
                print(f"  {row}")
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gen", required=True,
                        help="generator name in this module or diagonal_patterns")
    parser.add_argument("--ns", nargs="+", type=int, required=True)
    args = parser.parse_args()
    import importlib
    name = args.gen
    fn = None
    for mod_name in ("diagonal_patterns", "construction_lab"):
        try:
            mod = importlib.import_module(mod_name)
            if hasattr(mod, name):
                fn = getattr(mod, name)
                break
        except ImportError:
            pass
    if fn is None:
        raise SystemExit(f"could not find generator '{name}'")
    sweep(fn, args.ns)


if __name__ == "__main__":
    main()
