#!/usr/bin/env python3
"""Exact finite census of omitted-vertex bundle cycle defects.

For a forced-acyclic set F in the n by n grid, U is its complement and H is
the forced-edge graph.  The script computes bundleCycleDefect and its graphic
rank directly from the H-component labels.  It exhausts inclusion-maximal sets
through a requested n, exhausts maximum sets farther, and checks targeted
maximum witnesses after exhaustive maximum enumeration becomes expensive.

All conclusions are finite computational evidence, not proof claims.
"""

from __future__ import annotations

import argparse
import json
import random
from collections import Counter
from dataclasses import asdict, dataclass
from typing import Callable, Iterable, Iterator

from analysis.bounds.boundary_charge_reduction import canonical_rows, exact_maxima
from analysis.bounds.forced_forest_row_grammar import (
    State,
    _DisjointSet,
    first_row_state,
    is_forced_forest,
    transition,
)
from analysis.bounds.max_fr_checker import TARGETED_MAXIMUM_WITNESSES, maximum_witnesses


@dataclass(frozen=True)
class DefectProfile:
    n: int
    forced: int
    unforced: int
    sum_defect: int
    sum_graphic_rank: int
    boundary_deficiency_u: int
    forced_induced_components: int
    unforced_induced_components: int
    forced_graph_components: int
    unforced_edges: int
    defect_distribution: tuple[int, int, int, int]

    @property
    def maximal(self) -> bool:
        return self.unforced == 0 or self.defect_distribution[0] == 0

    @property
    def target_margin(self) -> int:
        """Margin in 3|F|+4 <= n^2+3n."""
        return self.n * self.n + 3 * self.n - 4 - 3 * self.forced

    @property
    def component_strengthened_margin(self) -> int:
        """Margin in B_U+c(F)+c(H) >= n+3+c(U)."""
        return (
            self.boundary_deficiency_u
            + self.forced_induced_components
            + self.forced_graph_components
            - self.n
            - 3
            - self.unforced_induced_components
        )


def row_grammar_accepts(n: int, rows: tuple[int, ...]) -> bool:
    """Check a complete row sequence through the exact frontier grammar."""
    if n <= 0 or len(rows) != n:
        return False
    state = first_row_state(n, rows[0])
    if state is None:
        return False
    for mask in rows[1:]:
        state = transition(n, state, mask)
        if state is None:
            return False
    return True


def neighbors(n: int, vertex: int) -> tuple[int, ...]:
    row, column = divmod(vertex, n)
    return tuple(
        rr * n + cc
        for rr, cc in (
            (row - 1, column),
            (row + 1, column),
            (row, column - 1),
            (row, column + 1),
        )
        if 0 <= rr < n and 0 <= cc < n
    )


def independent_global_counts(
    n: int, rows: tuple[int, ...]
) -> tuple[int, int, int, int]:
    """Return B_U,c(G[F]),c(G[U]),c(H) using plain graph searches.

    H is spanning, so an unforced vertex with no forced neighbour is an
    isolated H component. An empty induced graph has zero components.
    """
    forced = {
        row * n + column
        for row, mask in enumerate(rows)
        for column in range(n)
        if mask >> column & 1
    }
    vertices = set(range(n * n))
    unforced = vertices - forced

    def components(subset: set[int], edge_allowed: Callable[[int, int], bool]) -> int:
        unseen = set(subset)
        count = 0
        while unseen:
            count += 1
            stack = [unseen.pop()]
            while stack:
                vertex = stack.pop()
                for other in neighbors(n, vertex):
                    if other in unseen and edge_allowed(vertex, other):
                        unseen.remove(other)
                        stack.append(other)
        return count

    boundary_u = sum(4 - len(neighbors(n, vertex)) for vertex in unforced)
    c_f = components(forced, lambda _left, _right: True)
    c_u = components(unforced, lambda _left, _right: True)
    c_h = components(vertices, lambda left, right: left in forced or right in forced)
    return boundary_u, c_f, c_u, c_h


def defect_profile(n: int, rows: Iterable[int]) -> DefectProfile:
    """Compute all global statistics and replay their exact identities."""
    rows = tuple(rows)
    if n <= 0 or len(rows) != n or not is_forced_forest(n, list(rows)):
        raise ValueError("rows must encode a forced-acyclic n by n set")

    vertex_count = n * n
    forced = {
        row * n + column
        for row, mask in enumerate(rows)
        for column in range(n)
        if mask >> column & 1
    }
    unforced = set(range(vertex_count)) - forced
    h_dsu = _DisjointSet(vertex_count)
    f_dsu = _DisjointSet(vertex_count)
    u_dsu = _DisjointSet(vertex_count)
    h_edges = 0
    unforced_edges = 0

    for vertex in range(vertex_count):
        for other in neighbors(n, vertex):
            if other <= vertex:
                continue
            if vertex in forced or other in forced:
                if not h_dsu.union_edge(vertex, other):
                    raise AssertionError("forced graph unexpectedly contains a cycle")
                h_edges += 1
            if vertex in forced and other in forced:
                f_dsu.union_summary(vertex, other)
            if vertex in unforced and other in unforced:
                u_dsu.union_summary(vertex, other)
                unforced_edges += 1

    h_labels = tuple(h_dsu.find(vertex) for vertex in range(vertex_count))
    defect_counts = [0, 0, 0, 0]
    sum_defect = 0
    sum_rank = 0
    for vertex in unforced:
        leaves = [other for other in neighbors(n, vertex) if other in unforced]
        noncentral_labels = {h_labels[other] for other in leaves}
        noncentral_labels.discard(h_labels[vertex])
        rank = len(noncentral_labels)
        defect = len(leaves) - rank
        if not 0 <= defect <= 3:
            raise AssertionError("omitted-vertex grid defect must lie in 0..3")
        defect_counts[defect] += 1
        sum_defect += defect
        sum_rank += rank

    boundary_u = sum(4 - len(neighbors(n, vertex)) for vertex in unforced)
    c_f = len({f_dsu.find(vertex) for vertex in forced}) if forced else 0
    c_u = len({u_dsu.find(vertex) for vertex in unforced}) if unforced else 0
    c_h = len(set(h_labels))
    profile = DefectProfile(
        n=n,
        forced=len(forced),
        unforced=len(unforced),
        sum_defect=sum_defect,
        sum_graphic_rank=sum_rank,
        boundary_deficiency_u=boundary_u,
        forced_induced_components=c_f,
        unforced_induced_components=c_u,
        forced_graph_components=c_h,
        unforced_edges=unforced_edges,
        defect_distribution=tuple(defect_counts),
    )

    assert independent_global_counts(n, rows) == (boundary_u, c_f, c_u, c_h)

    # Independent exact replays.  The last two use total boundary deficiency 4n.
    assert profile.sum_defect + profile.sum_graphic_rank == 2 * unforced_edges
    assert h_edges + c_h == vertex_count
    if n >= 2:
        assert (
            3 * profile.forced + c_f + c_h
            == vertex_count + 4 * n - boundary_u
        )
        assert profile.target_margin == (
            boundary_u + c_f + c_h - n - 4
        )
        assert profile.component_strengthened_margin == (
            profile.target_margin - max(0, c_u - 1)
        )
    return profile


def acyclic_sets(n: int) -> Iterator[tuple[int, ...]]:
    """Enumerate every forced-acyclic set with the exact row grammar."""
    def extend(rows: tuple[int, ...], state: State | None):
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


def maximal_profiles(n: int) -> Iterator[tuple[tuple[int, ...], DefectProfile]]:
    for rows in acyclic_sets(n):
        profile = defect_profile(n, rows)
        if profile.maximal:
            yield rows, profile


def maximalize(n: int, rows: tuple[int, ...], order: Iterable[int]) -> tuple[int, ...]:
    """Greedily extend an acyclic set; the result is inclusion-maximal."""
    candidate = list(rows)
    for vertex in order:
        row, column = divmod(vertex, n)
        bit = 1 << column
        if candidate[row] & bit:
            continue
        candidate[row] |= bit
        if not row_grammar_accepts(n, tuple(candidate)):
            candidate[row] &= ~bit
    result = tuple(candidate)
    if not row_grammar_accepts(n, result) or not is_forced_forest(n, list(result)):
        raise AssertionError("grammar and direct acyclicity checks disagree")
    if not defect_profile(n, result).maximal:
        raise AssertionError("greedy extension did not produce a maximal set")
    return result


def adversarial_maximal_witnesses(
    n: int, attempts: int, seed: int
) -> list[tuple[tuple[int, ...], DefectProfile]]:
    """Mutate maximal witnesses to minimize the component-strengthened margin."""
    rng = random.Random(seed)
    vertices = list(range(n * n))
    initial = {canonical_rows(n), *TARGETED_MAXIMUM_WITNESSES.get(n, ())}
    witnesses: dict[tuple[int, ...], DefectProfile] = {}

    def retain(rows: tuple[int, ...]) -> tuple[tuple[int, ...], DefectProfile]:
        profile = defect_profile(n, rows)
        if not profile.maximal:
            shuffled = vertices.copy()
            rng.shuffle(shuffled)
            rows = maximalize(n, rows, shuffled)
            profile = defect_profile(n, rows)
        witnesses[rows] = profile
        return rows, profile

    retained = [retain(rows) for rows in initial]
    current, current_profile = min(
        retained, key=lambda item: item[1].component_strengthened_margin
    )
    for attempt in range(attempts):
        if attempt % max(1, attempts // 8) == 0:
            shuffled = vertices.copy()
            rng.shuffle(shuffled)
            candidate = maximalize(n, (0,) * n, shuffled)
        else:
            forced = [
                vertex
                for vertex in vertices
                if current[vertex // n] >> (vertex % n) & 1
            ]
            candidate_rows = list(current)
            remove_count = min(len(forced), rng.choice((1, 1, 2, 3)))
            for vertex in rng.sample(forced, k=remove_count):
                candidate_rows[vertex // n] &= ~(1 << (vertex % n))
            shuffled = vertices.copy()
            rng.shuffle(shuffled)
            candidate = maximalize(n, tuple(candidate_rows), shuffled)
        candidate, profile = retain(candidate)
        if (
            profile.component_strengthened_margin
            <= current_profile.component_strengthened_margin
            or rng.random() < 0.04
        ):
            current, current_profile = candidate, profile
    return sorted(witnesses.items())


def render_rows(rows: tuple[int, ...]) -> list[str]:
    n = len(rows)
    return [
        "".join("F" if mask >> column & 1 else "U" for column in range(n))
        for mask in rows
    ]


def distribution(values: Iterable[object]) -> dict[str, int]:
    return {
        str(value): count
        for value, count in sorted(Counter(values).items(), key=lambda item: str(item[0]))
    }


def summarize(n: int, coverage: str, samples) -> dict:
    samples = list(samples)
    profiles = [profile for _rows, profile in samples]
    minimum_margin = min(
        (item.component_strengthened_margin for item in profiles), default=None
    )
    return {
        "n": n,
        "coverage": coverage,
        "checked": len(samples),
        "forced_distribution": distribution(item.forced for item in profiles),
        "sum_defect_distribution": distribution(item.sum_defect for item in profiles),
        "sum_graphic_rank_distribution": distribution(
            item.sum_graphic_rank for item in profiles
        ),
        "boundary_deficiency_u_distribution": distribution(
            item.boundary_deficiency_u for item in profiles
        ),
        "forced_induced_components_distribution": distribution(
            item.forced_induced_components for item in profiles
        ),
        "unforced_induced_components_distribution": distribution(
            item.unforced_induced_components for item in profiles
        ),
        "forced_graph_components_distribution": distribution(
            item.forced_graph_components for item in profiles
        ),
        "defect_distribution_distribution": distribution(
            item.defect_distribution for item in profiles
        ),
        "target_margin_distribution": distribution(item.target_margin for item in profiles),
        "component_strengthened_margin_distribution": distribution(
            item.component_strengthened_margin for item in profiles
        ),
        "minimum_component_strengthened_margin": minimum_margin,
        "first_minimum_component_strengthened_witness": next(
            (
                render_rows(rows)
                for rows, item in samples
                if item.component_strengthened_margin == minimum_margin
            ),
            None,
        ),
        "target_equalities": sum(item.target_margin == 0 for item in profiles),
        "component_strengthened_equalities": sum(
            item.component_strengthened_margin == 0 for item in profiles
        ),
        "first_target_equality": next(
            (render_rows(rows) for rows, item in samples if item.target_margin == 0),
            None,
        ),
        "first_component_strengthened_equality": next(
            (
                render_rows(rows)
                for rows, item in samples
                if item.component_strengthened_margin == 0
            ),
            None,
        ),
        "component_strengthened_equality_profile_distribution": distribution(
            (
                item.forced,
                item.boundary_deficiency_u,
                item.forced_induced_components,
                item.unforced_induced_components,
                item.forced_graph_components,
            )
            for item in profiles
            if item.component_strengthened_margin == 0
        ),
    }


def first_failure(
    samples: list[tuple[tuple[int, ...], DefectProfile]],
    credit: Callable[[DefectProfile], int],
) -> dict | None:
    for rows, profile in samples:
        value = credit(profile)
        if profile.target_margin < value:
            return {
                "rows": render_rows(rows),
                "target_margin": profile.target_margin,
                "claimed_extra_credit": value,
                "profile": asdict(profile),
            }
    return None


def build_report(
    maximal_n: int = 5,
    maximum_n: int = 8,
    targeted_n: int = 15,
    all_sets_n: int = 5,
    adversarial_attempts: int = 64,
) -> dict:
    all_samples: list[tuple[tuple[int, ...], DefectProfile]] = []
    records = []
    for n in range(2, max(maximal_n, all_sets_n) + 1):
        if n <= all_sets_n:
            complete = [(rows, defect_profile(n, rows)) for rows in acyclic_sets(n)]
            records.append(summarize(n, "all forced-acyclic sets", complete))
            samples = [(rows, profile) for rows, profile in complete if profile.maximal]
        else:
            samples = list(maximal_profiles(n))
        if n <= maximal_n:
            all_samples.extend(samples)
            records.append(summarize(n, "all inclusion-maximal sets", samples))

    for n in range(2, maximum_n + 1):
        samples = [(rows, defect_profile(n, rows)) for rows in maximum_witnesses(n)]
        all_samples.extend(samples)
        records.append(summarize(n, "all maximum sets", samples))

    certified = exact_maxima()
    for n in range(max(maximal_n, maximum_n) + 1, targeted_n + 1):
        rows_set = {canonical_rows(n), *TARGETED_MAXIMUM_WITNESSES.get(n, ())}
        samples = [(rows, defect_profile(n, rows)) for rows in sorted(rows_set)]
        all_samples.extend(samples)
        exact = certified.get(n)
        coverage = (
            "targeted certified-maximum witnesses"
            if exact is not None and all(profile.forced == exact for _rows, profile in samples)
            else "targeted construction; maximum not certified"
        )
        records.append(summarize(n, coverage, samples))

    adversarial_records = []
    for n in range(max(6, all_sets_n + 1), targeted_n + 1):
        samples = adversarial_maximal_witnesses(
            n, adversarial_attempts, 32452843 + 1009 * n
        )
        all_samples.extend(samples)
        adversarial_records.append(summarize(n, "adversarial random maximal sets", samples))

    credits: dict[str, Callable[[DefectProfile], int]] = {
        "c(G[U])-1 (survives)": lambda item: max(
            0, item.unforced_induced_components - 1
        ),
        "sum_defect-|U|": lambda item: item.sum_defect - item.unforced,
        "sum_graphic_rank": lambda item: item.sum_graphic_rank,
        "c(G[F])-1": lambda item: item.forced_induced_components - 1,
        "c(H)-1": lambda item: item.forced_graph_components - 1,
    }
    candidates = []
    for name, credit in credits.items():
        margins = [profile.target_margin - credit(profile) for _rows, profile in all_samples]
        candidates.append(
            {
                "extra_credit": name,
                "holds_on_samples": min(margins) >= 0,
                "minimum_margin": min(margins),
                "first_counterexample": first_failure(all_samples, credit),
            }
        )

    return {
        "scope": "finite exact computations only; no proof claim",
        "definitions": {
            "H": "grid edges with at least one endpoint in F",
            "D": "sum of bundleCycleDefect(H,F,u) over u in U",
            "R": "sum of starAttachmentGraphicRank(H,F,u) over u in U",
            "B_U": "sum over u in U of 4-deg_grid(u)",
        },
        "identities_replayed": [
            "D+R=2|E(G[U])|",
            "3|F|+c(G[F])+c(H)=n^2+4n-B_U",
            "target margin=B_U+c(G[F])+c(H)-n-4",
        ],
        "surviving_non_equivalent_inequality": (
            "B_U+c(G[F])+c(H) >= n+3+c(G[U]); for nonempty U this implies "
            "3|F|+4 <= n^2+3n and strengthens its margin by c(G[U])-1"
        ),
        "records": records,
        "adversarial_records": adversarial_records,
        "candidate_extra_credits": candidates,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maximal-n", type=int, default=5)
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--targeted-n", type=int, default=15)
    parser.add_argument("--all-sets-n", type=int, default=5)
    parser.add_argument("--adversarial-attempts", type=int, default=64)
    args = parser.parse_args()
    print(
        json.dumps(
            build_report(
                args.maximal_n,
                args.maximum_n,
                args.targeted_n,
                args.all_sets_n,
                args.adversarial_attempts,
            ),
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
