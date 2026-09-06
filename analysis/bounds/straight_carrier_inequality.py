#!/usr/bin/env python3
"""Census and inequality search for straight components of a forced forest.

For a forced set F, H contains every grid edge with at least one endpoint in
F.  Non-singleton components of G[F] are canonically horizontal or vertical
intervals and are called carriers here.  Singleton components are kept
separate: assigning them an axis would make the gap statistics noncanonical.

The computations are finite evidence, not proofs for uncomputed grid sizes.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator, Sequence

from analysis.bounds.boundary_charge_reduction import boundary_charges, canonical_rows
from analysis.bounds.checkerboard_boundary_runs import acyclic_row_sets
from analysis.bounds.forced_forest_row_grammar import is_forced_forest
from analysis.bounds.max_fr_checker import (
    TARGETED_MAXIMUM_WITNESSES,
    maximum_witnesses,
    random_maximum_witnesses,
    transform,
)


Vertex = tuple[int, int]


@dataclass(frozen=True)
class Carrier:
    orientation: str
    fixed_coordinate: int
    start: int
    end: int
    length: int
    side_contacts: int
    attachment_degree: int
    leaf_attachments: int
    branching_attachments: int
    rows_occupied: int
    columns_occupied: int


@dataclass(frozen=True)
class CarrierProfile:
    n: int
    forced_count: int
    singleton_components: int
    horizontal_carriers: int
    vertical_carriers: int
    carrier_vertices: int
    carrier_side_contacts: int
    carrier_attachment_degree: int
    carrier_leaf_attachments: int
    carrier_branching_attachments: int
    horizontal_rows_occupied: int
    vertical_columns_occupied: int
    internal_u_gaps: int
    internal_u_gap_vertices: int
    boundary_u_gaps: int
    boundary_u_gap_vertices: int
    target_charge: int
    target_bound: int
    target_margin: int
    carriers: tuple[Carrier, ...]


def _neighbors(n: int, vertex: Vertex) -> Iterator[Vertex]:
    row, column = vertex
    for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
        rr, cc = row + dr, column + dc
        if 0 <= rr < n and 0 <= cc < n:
            yield rr, cc


def _components(n: int, forced: set[Vertex]) -> list[frozenset[Vertex]]:
    unseen = set(forced)
    result = []
    while unseen:
        root = unseen.pop()
        component = {root}
        stack = [root]
        while stack:
            vertex = stack.pop()
            for neighbor in _neighbors(n, vertex):
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    component.add(neighbor)
                    stack.append(neighbor)
        result.append(frozenset(component))
    return result


def _carrier(
    n: int,
    component: frozenset[Vertex],
    forced: set[Vertex],
    u_attachment_degree: dict[Vertex, int],
) -> Carrier:
    rows = {row for row, _column in component}
    columns = {column for _row, column in component}
    if len(component) < 2 or (len(rows) > 1 and len(columns) > 1):
        raise ValueError("component is not a non-singleton straight interval")
    horizontal = len(rows) == 1
    orientation = "H" if horizontal else "V"
    fixed = next(iter(rows if horizontal else columns))
    coordinates = sorted(column if horizontal else row for row, column in component)
    if coordinates != list(range(coordinates[0], coordinates[-1] + 1)):
        raise ValueError("straight component is not an interval")

    side_contacts = 0
    attachments: list[Vertex] = []
    for row, column in component:
        side_contacts += (row == 0) + (row == n - 1) + (column == 0) + (column == n - 1)
        attachments.extend(
            neighbor
            for neighbor in _neighbors(n, (row, column))
            if neighbor not in forced
        )
    # A U vertex cannot have two edges to one F component in an acyclic H.
    if len(attachments) != len(set(attachments)):
        raise AssertionError("parallel quotient attachments would create a cycle")
    leaf_attachments = sum(u_attachment_degree[vertex] == 1 for vertex in attachments)
    branching_attachments = len(attachments) - leaf_attachments
    length = len(component)
    if len(attachments) != 2 * length + 2 - side_contacts:
        raise AssertionError("carrier length/side/attachment identity failed")
    return Carrier(
        orientation=orientation,
        fixed_coordinate=fixed,
        start=coordinates[0],
        end=coordinates[-1],
        length=length,
        side_contacts=side_contacts,
        attachment_degree=len(attachments),
        leaf_attachments=leaf_attachments,
        branching_attachments=branching_attachments,
        rows_occupied=1 if horizontal else length,
        columns_occupied=length if horizontal else 1,
    )


def _axis_gaps(
    n: int, carriers: Sequence[Carrier], forced: set[Vertex]
) -> tuple[int, int, int, int]:
    """Count maximal positive U intervals between carriers and the boundary.

    Only collinear carriers with the same canonical orientation participate.
    An internal gap lies between consecutive carriers.  A boundary gap lies
    between an extreme carrier and one end of its row or column.  This avoids
    assigning singleton components an arbitrary axis.
    """
    internal_count = internal_vertices = boundary_count = boundary_vertices = 0
    for orientation in ("H", "V"):
        for fixed in range(n):
            intervals = sorted(
                (carrier.start, carrier.end)
                for carrier in carriers
                if carrier.orientation == orientation
                and carrier.fixed_coordinate == fixed
            )
            if not intervals:
                continue
            left = intervals[0][0]
            boundary_intervals = ((0, left), (intervals[-1][1] + 1, n))
            for start, end in boundary_intervals:
                length = end - start
                positions = (
                    ((fixed, axis) if orientation == "H" else (axis, fixed))
                    for axis in range(start, end)
                )
                if length and not any(vertex in forced for vertex in positions):
                    boundary_count += 1
                    boundary_vertices += length
            for (_start, end), (next_start, _next_end) in zip(intervals, intervals[1:]):
                length = next_start - end - 1
                if length <= 0:
                    raise AssertionError("distinct collinear F components must have a U gap")
                positions = (
                    ((fixed, axis) if orientation == "H" else (axis, fixed))
                    for axis in range(end + 1, next_start)
                )
                if not any(vertex in forced for vertex in positions):
                    internal_count += 1
                    internal_vertices += length
    return internal_count, internal_vertices, boundary_count, boundary_vertices


def carrier_profile(n: int, rows: Iterable[int]) -> CarrierProfile:
    rows = tuple(rows)
    if len(rows) != n or not is_forced_forest(n, list(rows)):
        raise ValueError("rows must describe an acyclic forced set")
    forced = {
        (row, column)
        for row, column in product(range(n), repeat=2)
        if rows[row] >> column & 1
    }
    u_attachment_degree = {
        vertex: sum(neighbor in forced for neighbor in _neighbors(n, vertex))
        for vertex in product(range(n), repeat=2)
        if vertex not in forced
    }
    components = _components(n, forced)
    carriers = tuple(
        sorted(
            (
                _carrier(n, component, forced, u_attachment_degree)
                for component in components
                if len(component) > 1
            ),
            key=lambda item: (item.orientation, item.fixed_coordinate, item.start),
        )
    )
    singleton_components = sum(len(component) == 1 for component in components)
    internal_gaps, internal_gap_vertices, boundary_gaps, boundary_gap_vertices = (
        _axis_gaps(n, carriers, forced)
    )
    charges = boundary_charges(n, rows)
    target_bound = 3 * n - 4
    target_margin = target_bound - charges.charged_expression
    assert target_margin == n * n + target_bound - 3 * len(forced)
    return CarrierProfile(
        n=n,
        forced_count=len(forced),
        singleton_components=singleton_components,
        horizontal_carriers=sum(item.orientation == "H" for item in carriers),
        vertical_carriers=sum(item.orientation == "V" for item in carriers),
        carrier_vertices=sum(item.length for item in carriers),
        carrier_side_contacts=sum(item.side_contacts for item in carriers),
        carrier_attachment_degree=sum(item.attachment_degree for item in carriers),
        carrier_leaf_attachments=sum(item.leaf_attachments for item in carriers),
        carrier_branching_attachments=sum(item.branching_attachments for item in carriers),
        horizontal_rows_occupied=len(
            {item.fixed_coordinate for item in carriers if item.orientation == "H"}
        ),
        vertical_columns_occupied=len(
            {item.fixed_coordinate for item in carriers if item.orientation == "V"}
        ),
        internal_u_gaps=internal_gaps,
        internal_u_gap_vertices=internal_gap_vertices,
        boundary_u_gaps=boundary_gaps,
        boundary_u_gap_vertices=boundary_gap_vertices,
        target_charge=charges.charged_expression,
        target_bound=target_bound,
        target_margin=target_margin,
        carriers=carriers,
    )


EXTRA_FEATURES = (
    "internal_u_gaps",
    "internal_u_gap_vertices",
    "carrier_branching_attachments",
)

REPORTED_FEATURES = (
    "forced_count",
    "singleton_components",
    "horizontal_carriers",
    "vertical_carriers",
    "carrier_vertices",
    "carrier_side_contacts",
    "carrier_attachment_degree",
    "carrier_leaf_attachments",
    "carrier_branching_attachments",
    "horizontal_rows_occupied",
    "vertical_columns_occupied",
    "internal_u_gaps",
    "internal_u_gap_vertices",
    "boundary_u_gaps",
    "boundary_u_gap_vertices",
)


def search_strengthenings(
    profiles: Sequence[CarrierProfile], max_coefficient: int = 3
) -> list[tuple[int, ...]]:
    """Find nonzero small coefficients a with charge + a.features <= 3n-4.

    Every searched feature and coefficient is nonnegative.  A survivor is
    therefore a genuine sufficient strengthening, not an algebraic rewriting
    of the exact target charge.
    """
    survivors = []
    for coefficients in product(range(max_coefficient + 1), repeat=len(EXTRA_FEATURES)):
        if not any(coefficients):
            continue
        if all(
            item.target_charge
            + sum(
                coefficient * getattr(item, feature)
                for coefficient, feature in zip(coefficients, EXTRA_FEATURES)
            )
            <= item.target_bound
            for item in profiles
        ):
            survivors.append(coefficients)
    return survivors


def larger_witnesses(n: int, random_count: int) -> set[tuple[int, ...]]:
    """Return maximal dihedral/random exchanges of target-count witnesses."""
    seeds = {
        canonical_rows(n),
        *TARGETED_MAXIMUM_WITNESSES.get(n, ()),
    }
    if not all(is_forced_forest(n, list(rows)) for rows in seeds):
        raise AssertionError("known larger witness is not forced-acyclic")
    witnesses = {
        transform(rows, rotation, reflect)
        for rows in seeds
        for rotation in range(4)
        for reflect in (False, True)
    }
    per_seed = max(0, random_count // len(seeds))
    for index, rows in enumerate(sorted(seeds)):
        witnesses.update(random_maximum_witnesses(rows, per_seed, 65537 * n + index))
    if not all(is_inclusion_maximal(n, rows) for rows in witnesses):
        raise AssertionError("larger witness is not inclusion-maximal")
    return witnesses


def is_inclusion_maximal(n: int, rows: tuple[int, ...]) -> bool:
    """Check that no single U vertex can be added while H remains acyclic."""
    if not is_forced_forest(n, list(rows)):
        return False
    for row, column in product(range(n), repeat=2):
        if rows[row] >> column & 1:
            continue
        extended = list(rows)
        extended[row] |= 1 << column
        if is_forced_forest(n, extended):
            return False
    return True


def _coverage(exhaustive_n: int, maximum_n: int, targeted_n: int, random_count: int):
    for n in range(2, exhaustive_n + 1):
        yield n, "all acyclic sets", acyclic_row_sets(n)
    for n in range(exhaustive_n + 1, maximum_n + 1):
        yield n, "all maximum witnesses", maximum_witnesses(n)
    for n in range(maximum_n + 1, targeted_n + 1):
        kind = (
            "target-count maximal witnesses"
            if n == 13
            else "targeted maximal maximum witnesses"
        )
        yield n, kind, sorted(larger_witnesses(n, random_count))


def build_report(
    exhaustive_n: int = 5,
    maximum_n: int = 6,
    targeted_n: int = 9,
    random_count: int = 100,
    max_coefficient: int = 3,
) -> dict:
    profiles = []
    coverage = []
    for n, kind, witnesses in _coverage(exhaustive_n, maximum_n, targeted_n, random_count):
        witness_rows = list(witnesses)
        items = [carrier_profile(n, rows) for rows in witness_rows]
        profiles.extend(items)
        candidate_margins = [
            item.target_margin - 2 * item.internal_u_gaps for item in items
        ]
        length_margins = [
            item.target_margin - item.internal_u_gap_vertices for item in items
        ]
        worst_candidate = min(range(len(items)), key=candidate_margins.__getitem__)
        coverage.append(
            {
                "n": n,
                "coverage": kind,
                "checked": len(items),
                "target_failures": sum(item.target_margin < 0 for item in items),
                "target_margin_distribution": dict(Counter(item.target_margin for item in items)),
                "aggregate_ranges": {
                    feature: [
                        min(getattr(item, feature) for item in items),
                        max(getattr(item, feature) for item in items),
                    ]
                    for feature in REPORTED_FEATURES
                },
                "minimum_candidate_margin": candidate_margins[worst_candidate],
                "worst_candidate_rows": list(witness_rows[worst_candidate]),
                "minimum_gap_length_margin": min(length_margins),
            }
        )
    survivors = search_strengthenings(profiles, max_coefficient)
    return {
        "scope": "finite computational evidence only; no Lean proof claim",
        "carrier_definition": "non-singleton component of G[F]; singleton components are axis-free",
        "identities_checked": [
            "each carrier is a horizontal or vertical interval",
            "attachment_degree(C) = 2*length(C)+2-side_contacts(C)",
            "target_margin = n^2+3n-4-3|F|",
        ],
        "extra_feature_order": list(EXTRA_FEATURES),
        "searched_inequality": "target_charge + dot(coefficients, extra_features) <= 3n-4",
        "reported_aggregate_order": list(REPORTED_FEATURES),
        "coefficient_range": [0, max_coefficient],
        "surviving_coefficients": survivors,
        "coverage": coverage,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-n", type=int, default=5)
    parser.add_argument("--maximum-n", type=int, default=6)
    parser.add_argument("--targeted-n", type=int, default=9)
    parser.add_argument("--random-count", type=int, default=100)
    parser.add_argument("--max-coefficient", type=int, default=3)
    args = parser.parse_args()
    report = build_report(
        args.exhaustive_n,
        args.maximum_n,
        args.targeted_n,
        args.random_count,
        args.max_coefficient,
    )
    import json

    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
