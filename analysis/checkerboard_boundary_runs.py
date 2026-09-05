#!/usr/bin/env python3
"""Census and small-coefficient search for checkerboard boundary-run bounds.

This is finite computational evidence, not a proof.  A forced set is encoded by
little-endian row masks, as in the other forced-forest analysis scripts.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations, product
from math import gcd
from typing import Iterable, Iterator, Sequence

from forced_forest_row_grammar import State, first_row_state, transition
from max_fr_checker import (
    TARGETED_MAXIMUM_WITNESSES,
    canonical_witness,
    maximum_witnesses,
    random_maximum_witnesses,
    transform,
)


BLACK = 0
WHITE = 1


def boundary_vertices(n: int) -> tuple[tuple[int, int], ...]:
    """Clockwise boundary cycle, with every corner occurring once."""
    if n < 2:
        raise ValueError("boundary words require n >= 2")
    return (
        *((0, c) for c in range(n)),
        *((r, n - 1) for r in range(1, n)),
        *((n - 1, c) for c in range(n - 2, -1, -1)),
        *((r, 0) for r in range(n - 2, 0, -1)),
    )


def cyclic_runs(word: Sequence[object]) -> int:
    """Number of changes in a nonempty cyclic word (zero for a constant word)."""
    if not word:
        return 0
    return sum(word[index] != word[index - 1] for index in range(len(word)))


class UnionFind:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))

    def root(self, vertex: int) -> int:
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def union(self, left: int, right: int) -> None:
        left, right = self.root(left), self.root(right)
        if left != right:
            self.parent[left] = right


def normalized_labels(labels: Sequence[int]) -> tuple[int, ...]:
    names: dict[int, int] = {}
    return tuple(names.setdefault(label, len(names)) for label in labels)


def star_labels_and_components(
    n: int, rows: Sequence[int], color: int
) -> tuple[tuple[int, ...], int, int]:
    """Boundary labels, ambient component count, and edge count for one color."""
    forest = UnionFind(n * n)
    edges = 0
    for r, c in product(range(n), repeat=2):
        if (r + c) % 2 != color or not (rows[r] >> c) & 1:
            continue
        for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            rr, cc = r + dr, c + dc
            if 0 <= rr < n and 0 <= cc < n:
                forest.union(r * n + c, rr * n + cc)
                edges += 1
    labels = normalized_labels(
        [forest.root(r * n + c) for r, c in boundary_vertices(n)]
    )
    components = len({forest.root(vertex) for vertex in range(n * n)})
    return labels, components, edges


def labels_nonalternating(labels: Sequence[int]) -> bool:
    """Check that no two labels occur cyclically in the pattern A,B,A,B."""
    length = len(labels)
    doubled = tuple(labels) * 2
    for start in range(length):
        word = doubled[start : start + length]
        for a, b, c, d in combinations(range(length), 4):
            if word[a] == word[c] and word[b] == word[d] and word[a] != word[b]:
                return False
    return True


@dataclass(frozen=True)
class ColorProfile:
    forced: int
    unforced: int
    boundary_deficiency: int
    components: int
    label_runs: int
    labels: tuple[int, ...]

    @property
    def charge(self) -> int:
        return self.boundary_deficiency + self.unforced + 2 - self.components


@dataclass(frozen=True)
class Profile:
    n: int
    rows: tuple[int, ...]
    fu_word: str
    fu_runs: int
    black: ColorProfile
    white: ColorProfile


def profile(n: int, rows: Iterable[int]) -> Profile:
    rows = tuple(rows)
    if (
        n < 2
        or len(rows) != n
        or any(mask < 0 or mask >= 1 << n for mask in rows)
    ):
        raise ValueError("rows must encode an n by n set with n >= 2")
    boundary = boundary_vertices(n)
    fu_word = "".join("F" if (rows[r] >> c) & 1 else "U" for r, c in boundary)
    colors = []
    for color in (BLACK, WHITE):
        forced = sum(
            (rows[r] >> c) & 1
            for r, c in product(range(n), repeat=2)
            if (r + c) % 2 == color
        )
        population = (n * n + (1 if color == BLACK and n % 2 else 0)) // 2
        deficiency = sum(
            (
                4
                - sum(
                    0 <= r + dr < n and 0 <= c + dc < n
                    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1))
                )
            )
            for r, c in product(range(n), repeat=2)
            if (r + c) % 2 == color and (rows[r] >> c) & 1
        )
        labels, components, _ = star_labels_and_components(n, rows, color)
        colors.append(
            ColorProfile(
                forced=forced,
                unforced=population - forced,
                boundary_deficiency=deficiency,
                components=components,
                label_runs=cyclic_runs(labels),
                labels=labels,
            )
        )
    return Profile(n, rows, fu_word, cyclic_runs(fu_word), colors[0], colors[1])


def allowances(n: int, odd_bias: int = 3) -> tuple[int, int]:
    """Return A_B,A_W, whose sum is 3n; black is the larger odd-grid class."""
    bias = odd_bias if n % 2 else 0
    if (3 * n + bias) % 2:
        raise ValueError("allowance bias has the wrong parity")
    black = (3 * n + bias) // 2
    return black, 3 * n - black


def run_bound_margins(
    item: Profile, scale: int = 2, run_coefficient: int = 1, odd_bias: int = 3
) -> tuple[int, int]:
    """Margins in s*A_c + k*R_other - (s*Q_c + k*R_c)."""
    black_allowance, white_allowance = allowances(item.n, odd_bias)
    return (
        scale * black_allowance
        + run_coefficient * item.white.label_runs
        - scale * item.black.charge
        - run_coefficient * item.black.label_runs,
        scale * white_allowance
        + run_coefficient * item.black.label_runs
        - scale * item.white.charge
        - run_coefficient * item.white.label_runs,
    )


def acyclic_row_sets(n: int) -> Iterator[tuple[int, ...]]:
    """Enumerate all forced-acyclic row sets using the exact frontier grammar."""
    def extend(
        rows: tuple[int, ...], state: State | None
    ) -> Iterator[tuple[int, ...]]:
        if len(rows) == n:
            yield rows
            return
        for mask in range(1 << n):
            next_state = (
                first_row_state(n, mask)
                if state is None
                else transition(n, state, mask)
            )
            if next_state is not None:
                yield from extend(rows + (mask,), next_state)

    yield from extend((), None)


def search_coefficients(
    profiles: Sequence[Profile], max_scale: int = 6, max_abs_bias: int = 7
) -> list[tuple[int, int, int]]:
    """Find primitive (scale, run coefficient, odd bias) pairs fitting the data."""
    valid = []
    for scale in range(1, max_scale + 1):
        for coefficient in range(scale + 1):
            if gcd(scale, coefficient) > 1:
                continue
            for bias in range(-max_abs_bias, max_abs_bias + 1, 2):
                if all(
                    min(run_bound_margins(item, scale, coefficient, bias)) >= 0
                    for item in profiles
                ):
                    valid.append((scale, coefficient, bias))
    return valid


def targeted_maxima(n: int, random_count: int) -> set[tuple[int, ...]]:
    seeds = {canonical_witness(n), *TARGETED_MAXIMUM_WITNESSES.get(n, ())}
    result = {
        transform(rows, rotation, reflect)
        for rows in seeds
        for rotation in range(4)
        for reflect in (False, True)
    }
    for index, rows in enumerate(sorted(seeds)):
        result.update(
            random_maximum_witnesses(rows, random_count, 7919 * n + index)
        )
    return result


def census(
    exhaustive_n: int, maximum_n: int, targeted_maximum_n: int, random_count: int
) -> list[Profile]:
    result = []
    for n in range(2, exhaustive_n + 1):
        rows = list(acyclic_row_sets(n))
        items = [profile(n, item) for item in rows]
        failures = [item for item in items if min(run_bound_margins(item)) < 0]
        equalities = [item for item in items if run_bound_margins(item) == (0, 0)]
        print(
            f"n={n} exhaustive={len(items)} failures={len(failures)} "
            f"equalities={len(equalities)}"
        )
        result.extend(items)
    for n in range(exhaustive_n + 1, maximum_n + 1):
        items = [profile(n, item) for item in maximum_witnesses(n)]
        failures = [item for item in items if min(run_bound_margins(item)) < 0]
        equalities = [item for item in items if run_bound_margins(item) == (0, 0)]
        print(
            f"n={n} maxima={len(items)} failures={len(failures)} "
            f"equalities={len(equalities)}"
        )
        result.extend(items)
    for n in range(maximum_n + 1, targeted_maximum_n + 1):
        items = [profile(n, item) for item in targeted_maxima(n, random_count)]
        failures = [item for item in items if min(run_bound_margins(item)) < 0]
        equalities = [item for item in items if run_bound_margins(item) == (0, 0)]
        print(
            f"n={n} targeted_maxima={len(items)} failures={len(failures)} "
            f"equalities={len(equalities)}"
        )
        result.extend(items)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-n", type=int, default=5)
    parser.add_argument("--maximum-n", type=int, default=6)
    parser.add_argument("--targeted-maximum-n", type=int, default=9)
    parser.add_argument("--random-count", type=int, default=100)
    parser.add_argument("--max-scale", type=int, default=6)
    args = parser.parse_args()
    items = census(
        args.exhaustive_n,
        args.maximum_n,
        args.targeted_maximum_n,
        args.random_count,
    )
    print("valid (scale, run_coefficient, odd_bias):")
    print(search_coefficients(items, args.max_scale))


if __name__ == "__main__":
    main()
