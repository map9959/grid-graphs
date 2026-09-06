#!/usr/bin/env python3
"""Deterministic Wave 2 Hall census for occurrence-labelled bare combs.

Declared family
---------------
A template has one of four outward orientations, depth ``1..D``, a run of
``s`` consecutive starting gaps, and uniform occurrence multiplicity ``1..M``.
Each starting gap chooses one word in ``{-1,+1}^depth``.  A letter moves to an
adjacent gap on the next outward comb.  The word is copied ``multiplicity``
times, but every copy remains the distinct value

    Demand(origin_id, start, transition_history).

Thus equal starts, histories, intermediate positions, and terminal positions
never quotient occurrences.  Templates are ordered lexicographically by
orientation, depth, multiplicity, start count, and history profile.  Only
templates with at most ``demand_limit`` demands and ``resource_limit`` distinct
geometric owner slots are in the family.  Owner slots are the distinct gap
positions visited at every level, including level zero.  This is an abstract
transition-network census, not a claim that every template is realizable by a
grid spanning tree.

The geometry is the four-orientation version of ``BareCombTransition.lean``.
The occurrence provenance follows ``RankedTransitionOwnership.lean``.  We use
the component routine from ``check_boundary_peeling_lemmas`` to form transported
basins; the forest and annular scripts do not expose additional machinery that
is applicable to these already-contracted transition networks.

Policies
--------
``immediate-local`` offers only the owner slot at the final geometric gap.
It intentionally exposes collisions when labelled paths reconverge.
``transported-basin`` joins occurrences whose full traces meet (transitively)
and offers every owner slot visited by that component.

Hall is checked by enumerating every demand subset.  Matching is computed by a
separate deterministic augmenting-path implementation and every emitted
certificate is replayed independently before it is written.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, Iterator, Mapping, Sequence

from analysis.bounds.check_boundary_peeling_lemmas import components


ORIENTATIONS = ("north", "east", "south", "west")
POLICIES = ("immediate-local", "transported-basin")
DEFAULT_TEMPLATE_CAP = 50_000


@dataclass(frozen=True, order=True)
class Demand:
    origin_id: int
    start: int
    transition_history: tuple[int, ...]


@dataclass(frozen=True, order=True)
class Resource:
    row: int
    column: int


@dataclass(frozen=True)
class Template:
    orientation: str
    depth: int
    multiplicity: int
    starts: tuple[int, ...]
    histories: tuple[tuple[int, ...], ...]

    def demands(self) -> tuple[Demand, ...]:
        result = []
        origin = 0
        for start, history in zip(self.starts, self.histories, strict=True):
            for _ in range(self.multiplicity):
                result.append(Demand(origin, start, history))
                origin += 1
        return tuple(result)


@dataclass(frozen=True)
class CensusBounds:
    max_depth: int = 6
    max_multiplicity: int = 3
    demand_limit: int = 16
    resource_limit: int = 24
    template_cap: int = DEFAULT_TEMPLATE_CAP

    def validate(self) -> None:
        if not 1 <= self.max_depth <= 6:
            raise ValueError("max_depth must be in 1..6")
        if not 1 <= self.max_multiplicity <= 3:
            raise ValueError("max_multiplicity must be in 1..3")
        if not 1 <= self.demand_limit <= 16:
            raise ValueError("demand_limit must be in 1..16")
        if not 1 <= self.resource_limit <= 24:
            raise ValueError("resource_limit must be in 1..24")
        if not 1 <= self.template_cap <= DEFAULT_TEMPLATE_CAP:
            raise ValueError(
                f"template_cap must be in 1..{DEFAULT_TEMPLATE_CAP}"
            )


def oriented_position(orientation: str, level: int, lateral: int) -> Resource:
    if orientation == "north":
        return Resource(-level, lateral)
    if orientation == "east":
        return Resource(lateral, level)
    if orientation == "south":
        return Resource(level, lateral)
    if orientation == "west":
        return Resource(lateral, -level)
    raise ValueError(f"unknown orientation: {orientation}")


def trace(template: Template, demand: Demand) -> tuple[Resource, ...]:
    lateral = demand.start
    result = [oriented_position(template.orientation, 0, lateral)]
    for level, step in enumerate(demand.transition_history, start=1):
        lateral += step
        result.append(oriented_position(template.orientation, level, lateral))
    return tuple(result)


def resources(template: Template) -> tuple[Resource, ...]:
    return tuple(sorted({slot for demand in template.demands() for slot in trace(template, demand)}))


def neighborhoods(template: Template, policy: str) -> tuple[frozenset[Resource], ...]:
    demands = template.demands()
    ordered_traces = tuple(trace(template, demand) for demand in demands)
    traces = tuple(frozenset(path) for path in ordered_traces)
    if policy == "immediate-local":
        return tuple(frozenset((path[-1],)) for path in ordered_traces)
    if policy != "transported-basin":
        raise ValueError(f"unknown policy: {policy}")

    overlap_edges = [
        (left, right)
        for left in range(len(demands))
        for right in range(left + 1, len(demands))
        if traces[left] & traces[right]
    ]
    basins = components(set(range(len(demands))), overlap_edges)  # type: ignore[arg-type]
    owner = {index: basin for basin in basins for index in basin}
    return tuple(
        frozenset().union(*(traces[index] for index in owner[demand_index]))
        for demand_index in range(len(demands))
    )


def _demand_json(demand: Demand) -> dict[str, object]:
    return {
        "origin_id": demand.origin_id,
        "start": demand.start,
        "transition_history": list(demand.transition_history),
    }


def _resource_json(resource: Resource) -> dict[str, int]:
    return {"row": resource.row, "column": resource.column}


def exact_hall_check(template: Template, policy: str) -> dict[str, object]:
    """Enumerate all subsets in size/lexicographic order and return a certificate."""
    demands = template.demands()
    candidates = neighborhoods(template, policy)
    for size in range(1, len(demands) + 1):
        for subset in combinations(range(len(demands)), size):
            union = frozenset().union(*(candidates[index] for index in subset))
            if len(union) < size:
                return {
                    "hall": False,
                    "violating_indices": list(subset),
                    "violating_demands": [_demand_json(demands[index]) for index in subset],
                    "neighborhood": [_resource_json(item) for item in sorted(union)],
                    "demand_count": size,
                    "neighborhood_count": len(union),
                }

    matching = deterministic_matching(candidates)
    if matching is None:
        raise AssertionError("Hall subsets passed but independent matching failed")
    return {
        "hall": True,
        "matching": [
            {
                "demand_index": index,
                "demand": _demand_json(demands[index]),
                "resource": _resource_json(matching[index]),
            }
            for index in range(len(demands))
        ],
    }


def deterministic_matching(
    candidates: Sequence[frozenset[Resource]],
) -> dict[int, Resource] | None:
    """Independent Kuhn matching; this does not use subset-enumeration state."""
    resource_owner: dict[Resource, int] = {}

    def augment(demand: int, seen: set[Resource]) -> bool:
        for resource in sorted(candidates[demand]):
            if resource in seen:
                continue
            seen.add(resource)
            previous = resource_owner.get(resource)
            if previous is None or augment(previous, seen):
                resource_owner[resource] = demand
                return True
        return False

    for demand in range(len(candidates)):
        if not augment(demand, set()):
            return None
    return {demand: resource for resource, demand in resource_owner.items()}


def replay_certificate(template: Template, policy: str, certificate: Mapping[str, object]) -> bool:
    """Replay JSON-shaped output without calling either certificate producer."""
    demands = template.demands()
    candidates = neighborhoods(template, policy)
    if certificate.get("hall") is False:
        indices = tuple(int(index) for index in certificate["violating_indices"])  # type: ignore[index]
        if len(indices) != len(set(indices)) or any(not 0 <= index < len(demands) for index in indices):
            return False
        union = frozenset().union(*(candidates[index] for index in indices))
        recorded = {
            Resource(int(item["row"]), int(item["column"]))
            for item in certificate["neighborhood"]  # type: ignore[index,union-attr]
        }
        return union == recorded and len(union) < len(indices)

    if certificate.get("hall") is not True:
        return False
    entries = certificate.get("matching")
    if not isinstance(entries, list) or len(entries) != len(demands):
        return False
    seen_demands: set[int] = set()
    seen_resources: set[Resource] = set()
    for entry in entries:
        index = int(entry["demand_index"])
        item = entry["resource"]
        resource = Resource(int(item["row"]), int(item["column"]))
        if (
            not 0 <= index < len(demands)
            or index in seen_demands
            or resource in seen_resources
            or resource not in candidates[index]
        ):
            return False
        seen_demands.add(index)
        seen_resources.add(resource)
    return seen_demands == set(range(len(demands)))


def template_json(template: Template) -> dict[str, object]:
    return {
        "orientation": template.orientation,
        "depth": template.depth,
        "multiplicity": template.multiplicity,
        "starts": list(template.starts),
        "histories": [list(history) for history in template.histories],
    }


def template_from_json(data: Mapping[str, object]) -> Template:
    return Template(
        orientation=str(data["orientation"]),
        depth=int(data["depth"]),
        multiplicity=int(data["multiplicity"]),
        starts=tuple(int(value) for value in data["starts"]),  # type: ignore[union-attr]
        histories=tuple(tuple(int(step) for step in word) for word in data["histories"]),  # type: ignore[union-attr]
    )


def enumerate_templates(bounds: CensusBounds) -> Iterator[Template]:
    bounds.validate()
    for orientation in ORIENTATIONS:
        for depth in range(1, bounds.max_depth + 1):
            words = tuple(product((-1, 1), repeat=depth))
            for multiplicity in range(1, bounds.max_multiplicity + 1):
                for start_count in range(1, bounds.demand_limit // multiplicity + 1):
                    starts = tuple(range(start_count))
                    for history_profile in product(words, repeat=start_count):
                        template = Template(
                            orientation, depth, multiplicity, starts, history_profile
                        )
                        if len(resources(template)) <= bounds.resource_limit:
                            yield template


def run_policy_census(bounds: CensusBounds, policy: str) -> dict[str, object]:
    checked = 0
    last_matching: dict[str, object] | None = None
    iterator = enumerate_templates(bounds)
    for template in iterator:
        if checked == bounds.template_cap:
            return {
                "status": "incomplete_due_to_cap",
                "templates_checked": checked,
                "template_cap": bounds.template_cap,
                "last_matching": last_matching,
            }
        certificate = exact_hall_check(template, policy)
        if not replay_certificate(template, policy, certificate):
            raise AssertionError("internal certificate replay failed")
        checked += 1
        if not certificate["hall"]:
            return {
                "status": "counterexample_found",
                "templates_checked": checked,
                "template": template_json(template),
                "certificate": certificate,
            }
        last_matching = {
            "template": template_json(template),
            "certificate": certificate,
        }
    return {
        "status": "all_templates_satisfy_within_declared_family",
        "templates_checked": checked,
        "last_matching": last_matching,
    }


def run_census(bounds: CensusBounds, selected_policies: Iterable[str]) -> dict[str, object]:
    bounds.validate()
    policies = tuple(selected_policies)
    if not policies or any(policy not in POLICIES for policy in policies):
        raise ValueError(f"policies must be drawn from {POLICIES}")
    return {
        "census": "wave2_occurrence_labelled_hall_micro_census",
        "deterministic": True,
        "declared_family": {
            "orientations": list(ORIENTATIONS),
            "depth": [1, bounds.max_depth],
            "transition_alphabet": [-1, 1],
            "uniform_multiplicity": [1, bounds.max_multiplicity],
            "demand_limit": bounds.demand_limit,
            "resource_limit": bounds.resource_limit,
            "template_order": "orientation, depth, multiplicity, start_count, history_profile",
        },
        "bounds": asdict(bounds),
        "policies": {policy: run_policy_census(bounds, policy) for policy in policies},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth", type=int, default=6)
    parser.add_argument("--max-multiplicity", type=int, default=3)
    parser.add_argument("--demand-limit", type=int, default=16)
    parser.add_argument("--resource-limit", type=int, default=24)
    parser.add_argument("--template-cap", type=int, default=DEFAULT_TEMPLATE_CAP)
    parser.add_argument("--policy", choices=(*POLICIES, "all"), default="all")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    bounds = CensusBounds(
        args.max_depth,
        args.max_multiplicity,
        args.demand_limit,
        args.resource_limit,
        args.template_cap,
    )
    selected = POLICIES if args.policy == "all" else (args.policy,)
    rendered = json.dumps(run_census(bounds, selected), indent=2, sort_keys=True)
    if args.output is None:
        print(rendered)
    else:
        args.output.write_text(rendered + "\n")


if __name__ == "__main__":
    main()
