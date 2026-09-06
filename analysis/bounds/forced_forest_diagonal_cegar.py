#!/usr/bin/env python3
"""Exact finite-width CEGAR for a forced-forest diagonal upper bound.

The row charge is ``q = n + 3 - 3 |F_row|``.  Its path sum is

    n^2 + 3n - 3|F| = W + 2 - n.

Consequently a terminal lower bound of 2 proves ``W >= n`` on the enumerated
source, and phase zero needs terminal value 4 for the sharper residue-zero
target.  This program only tests completely enumerated finite widths.  It does
not turn a successful finite test into a width-independent theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

from analysis.bounds.forced_forest_row_grammar import State, first_row_state, transition


Feature = tuple


@dataclass(frozen=True)
class ConcreteEdge:
    width: int
    row: int
    incoming: State | None
    outgoing: State
    mask: int
    weight: int


@dataclass
class WidthSource:
    width: int
    layers: list[set[State | None]]
    edges: list[list[ConcreteEdge]]
    forward: list[dict[State | None, int]]
    backward: list[dict[State | None, int]]
    optimum: int


def enumerate_complete_source(width: int) -> WidthSource:
    """Enumerate every reachable row transition, retaining no cost pruning."""
    if width <= 0:
        raise ValueError("width must be positive")
    layers: list[set[State | None]] = [{None}]
    edges: list[list[ConcreteEdge]] = []
    forward: list[dict[State | None, int]] = [{None: 0}]
    for row in range(width):
        outgoing_states: set[State] = set()
        row_edges = []
        next_forward: dict[State | None, int] = {}
        for incoming in sorted(layers[-1], key=repr):
            for mask in range(1 << width):
                outgoing = (
                    first_row_state(width, mask)
                    if incoming is None
                    else transition(width, incoming, mask)
                )
                if outgoing is None:
                    continue
                weight = width + 3 - 3 * mask.bit_count()
                edge = ConcreteEdge(width, row, incoming, outgoing, mask, weight)
                row_edges.append(edge)
                outgoing_states.add(outgoing)
                candidate = forward[-1][incoming] + weight
                previous = next_forward.get(outgoing)
                if previous is None or candidate < previous:
                    next_forward[outgoing] = candidate
        layers.append(set(outgoing_states))
        edges.append(row_edges)
        forward.append(next_forward)

    backward: list[dict[State | None, int]] = [{} for _ in layers]
    backward[-1] = {state: 0 for state in layers[-1]}
    for row in range(width - 1, -1, -1):
        values: dict[State | None, int] = {}
        for edge in edges[row]:
            candidate = edge.weight + backward[row + 1][edge.outgoing]
            previous = values.get(edge.incoming)
            if previous is None or candidate < previous:
                values[edge.incoming] = candidate
        backward[row] = values
    optimum = backward[0][None]
    if optimum != min(forward[-1].values()):
        raise AssertionError("forward and backward optimum disagree")
    return WidthSource(width, layers, edges, forward, backward, optimum)


def corridor_edges(source: WidthSource, slack: int | None) -> Iterable[ConcreteEdge]:
    """Yield all edges on a path within ``slack`` of the exact optimum."""
    if slack is not None and slack < 0:
        raise ValueError("corridor slack must be nonnegative")
    for row_edges in source.edges:
        for edge in row_edges:
            total = (
                source.forward[edge.row][edge.incoming]
                + edge.weight
                + source.backward[edge.row + 1][edge.outgoing]
            )
            if slack is None or total <= source.optimum + slack:
                yield edge


def _runs(mask: int, width: int) -> tuple[int, tuple[int, ...]]:
    lengths = []
    current = 0
    for column in range(width):
        if mask & (1 << column):
            current += 1
        elif current:
            lengths.append(current)
            current = 0
    if current:
        lengths.append(current)
    return len(lengths), tuple(lengths)


def _interval_count(values: Sequence[int], label: int) -> int:
    return sum(
        value == label and (index == 0 or values[index - 1] != label)
        for index, value in enumerate(values)
    )


def feature(width: int, row: int, state: State | None, level: str) -> Feature:
    """Project a frontier to width-independent forced-forest statistics."""
    if state is None:
        return ("initial",)
    mask = state.forced_mask
    partition = state.partition
    run_count, run_lengths = _runs(mask, width)
    left = bool(mask & 1)
    right = bool(mask & (1 << (width - 1)))
    boundary_mode = "terminal" if row == width else "top" if row == 1 else "interior"
    labels = sorted(set(partition))
    profiles = []
    orientations = Counter()
    for label in labels:
        columns = [c for c, observed in enumerate(partition) if observed == label]
        forced = [c for c in columns if mask & (1 << c)]
        horizontal = any(
            partition[c] == partition[c + 1] == label and mask & (3 << c)
            for c in range(width - 1)
        )
        nonlocal_contact = _interval_count(partition, label) > 1
        orientation = "mixed" if horizontal and nonlocal_contact else (
            "horizontal" if horizontal else "vertical" if forced else "passive"
        )
        orientations[orientation] += 1
        profiles.append(
            (
                len(columns),
                _interval_count(partition, label),
                len(forced),
                columns[0] == 0,
                columns[-1] == width - 1,
                orientation,
            )
        )
    if level in ("additive", "additive+hinges"):
        reserve: int | str = "terminal" if row == width else min(row, 6)
        additive = (
            row % 3,
            boundary_mode,
            reserve,
            mask.bit_count(),
            run_count,
            int(left),
            int(right),
            len(profiles),
            sum(item[0] for item in profiles),
            sum(item[1] for item in profiles),
            sum(item[2] for item in profiles),
            sum(int(item[3]) for item in profiles),
            sum(int(item[4]) for item in profiles),
            *(orientations[name] for name in ("passive", "vertical", "horizontal", "mixed")),
        )
        if level == "additive+hinges":
            # These are additive component defects: repeated frontier intervals,
            # multiple forced contacts, and passive span beyond one vertex.
            return (
                *additive,
                sum(max(item[1] - 1, 0) for item in profiles),
                sum(max(item[2] - 1, 0) for item in profiles),
                sum(max(item[0] - item[2] - 1, 0) for item in profiles),
                max(len(profiles) - 2, 0),
                int(
                    len(profiles) > 2
                    and any(item[1] > 1 for item in profiles)
                ),
                *(
                    int(
                        len(profiles) > 2
                        and any(
                            item[1] > 1
                        for item in profiles
                        if item[5] == orientation
                        )
                    )
                    for orientation in ("passive", "vertical", "horizontal", "mixed")
                ),
            )
        return additive
    base = (
        row % 3,
        boundary_mode,
        mask.bit_count(),
        run_count,
        left,
        right,
        len(labels),
        partition[0] == partition[-1],
    )
    if level == "runs":
        return base
    if level in ("components", "components+reserve"):
        result = (*base, tuple(sorted(orientations.items())), tuple(sorted(profiles)))
        if level == "components+reserve":
            reserve: int | str = "terminal" if row == width else min(row, 6)
            return (*result, reserve)
        return result
    if level == "ordered":
        # Preserve boundary order without preserving labels themselves.
        ordered_profiles = tuple(profiles[labels.index(label)] for label in partition)
        return (*base, run_lengths, tuple(sorted(orientations.items())), ordered_profiles)
    if level in ("ownership", "ownership+top-debt", "ownership+reserve"):
        ownership_runs = tuple(
            label for index, label in enumerate(partition)
            if index == 0 or partition[index - 1] != label
        )
        result = (
            *base,
            run_lengths,
            tuple(profiles),
            ownership_runs,
        )
        if level == "ownership+top-debt":
            # Three-row productions may not splice startup and stable interior.
            # Terminal states remain pooled by phase rather than absolute height.
            top_debt: int | str = "terminal" if row == width else min(row, 3)
            return (*result, top_debt)
        if level == "ownership+reserve":
            # Keep startup and the first stable three-row production distinct.
            # Further productions share the discharged (six-row) reserve state.
            reserve: int | str = "terminal" if row == width else min(row, 6)
            return (*result, reserve)
        return result
    raise ValueError(
        "feature level must be runs, components, components+reserve, additive, "
        "additive+hinges, ordered, ownership, ownership+top-debt, or ownership+reserve"
    )


def _edge_record(edge: ConcreteEdge, incoming: Feature, outgoing: Feature) -> dict:
    def state_record(state: State | None) -> dict | None:
        if state is None:
            return None
        return {"mask": state.forced_mask, "partition": list(state.partition)}

    return {
        "width": edge.width,
        "row": edge.row,
        "mask": edge.mask,
        "weight": edge.weight,
        "incoming_state": state_record(edge.incoming),
        "outgoing_state": state_record(edge.outgoing),
        "incoming_feature": incoming,
        "outgoing_feature": outgoing,
    }


def solve_constraints(
    sources: Sequence[WidthSource],
    level: str,
    slack: int | None,
    target_mode: str = "residue-zero",
    return_potentials: bool = False,
) -> dict:
    """Solve exact difference constraints or return a projected negative cycle."""
    if target_mode not in ("universal", "residue-zero"):
        raise ValueError("target mode must be universal or residue-zero")
    zero: Feature = ("zero",)
    initial: Feature = ("initial",)
    vertices = {zero, initial}
    # Constraint p(v) <= p(u) + weight is represented by u -> v.
    constraints: dict[tuple[Feature, Feature], tuple[Fraction, ConcreteEdge | None]] = {}

    def retain(u: Feature, v: Feature, weight: int, edge: ConcreteEdge | None) -> None:
        key = (u, v)
        old = constraints.get(key)
        value = Fraction(weight)
        if old is None or value < old[0]:
            constraints[key] = value, edge
        vertices.update((u, v))

    retain(zero, initial, 0, None)
    retain(initial, zero, 0, None)
    terminal_features: dict[int, set[Feature]] = {}
    concrete_count = 0
    for source in sources:
        terminals = {
            feature(source.width, source.width, state, level)
            for state in source.layers[-1]
            if state is not None
        }
        terminal_features[source.width] = terminals
        target = 4 if target_mode == "residue-zero" and source.width % 3 == 0 else 2
        for terminal in terminals:
            # p(terminal) >= target.
            retain(terminal, zero, -target, None)
        for edge in corridor_edges(source, slack):
            incoming = feature(source.width, edge.row, edge.incoming, level)
            outgoing = feature(source.width, edge.row + 1, edge.outgoing, level)
            retain(incoming, outgoing, edge.weight, edge)
            concrete_count += 1

    ordered = sorted(
        ((u, v, weight, edge) for (u, v), (weight, edge) in constraints.items()),
        key=repr,
    )
    adjacency: dict[Feature, list[tuple[Feature, Fraction, ConcreteEdge | None]]] = {
        vertex: [] for vertex in vertices
    }
    for u, v, weight, edge in ordered:
        adjacency[u].append((v, weight, edge))
    distances = {vertex: Fraction(0) for vertex in vertices}
    predecessor: dict[Feature, tuple[Feature, ConcreteEdge | None, Fraction]] = {}
    queue = deque(sorted(vertices, key=repr))
    queued = set(vertices)
    path_edge_count = {vertex: 0 for vertex in vertices}
    changed: Feature | None = None
    while queue and changed is None:
        u = queue.popleft()
        queued.remove(u)
        for v, weight, edge in adjacency[u]:
            candidate = distances[u] + weight
            if candidate < distances[v]:
                distances[v] = candidate
                predecessor[v] = (u, edge, weight)
                path_edge_count[v] = path_edge_count[u] + 1
                if path_edge_count[v] >= len(vertices):
                    changed = v
                    break
                if v not in queued:
                    queue.append(v)
                    queued.add(v)
    if changed is not None:
        cursor = changed
        for _ in vertices:
            cursor = predecessor[cursor][0]
        cycle = []
        start = cursor
        while True:
            u, edge, weight = predecessor[cursor]
            cycle.append(
                {"from": u, "to": cursor, "weight": int(weight), "edge": edge}
            )
            cursor = u
            if cursor == start:
                break
        cycle.reverse()
        return {
            "feasible": False,
            "target_mode": target_mode,
            "feature_states": len(vertices) - 1,
            "concrete_transitions": concrete_count,
            "pooled_constraints": len(constraints),
            "negative_cycle_weight": sum(item["weight"] for item in cycle),
            "counterexample_cycle": [
                {
                    "from": item["from"],
                    "to": item["to"],
                    "weight": item["weight"],
                    "concrete": None
                    if item["edge"] is None
                    else _edge_record(item["edge"], item["from"], item["to"]),
                }
                for item in cycle
            ],
        }

    shift = distances[zero]
    potentials = {state: value - shift for state, value in distances.items()}
    terminal_minima = {
        str(width): min(potentials[state] for state in terminals)
        for width, terminals in terminal_features.items()
    }
    constraint_hash = hashlib.sha256()
    for u, v, weight, _edge in ordered:
        constraint_hash.update(
            json.dumps([u, v, weight.numerator, weight.denominator], separators=(",", ":"))
            .encode("ascii")
        )
        constraint_hash.update(b"\n")
    potential_hash = hashlib.sha256()
    for state, value in sorted(potentials.items(), key=lambda item: repr(item[0])):
        potential_hash.update(
            json.dumps(
                [state, value.numerator, value.denominator], separators=(",", ":")
            ).encode("ascii")
        )
        potential_hash.update(b"\n")
    result = {
        "feasible": True,
        "target_mode": target_mode,
        "feature_states": len(vertices) - 1,
        "concrete_transitions": concrete_count,
        "pooled_constraints": len(constraints),
        "potential_denominators": sorted({value.denominator for value in potentials.values()}),
        "potential_range": [int(min(potentials.values())), int(max(potentials.values()))],
        "terminal_minima": {key: int(value) for key, value in terminal_minima.items()},
        "strongest_constraints_sha256": constraint_hash.hexdigest(),
        "exact_potentials_sha256": potential_hash.hexdigest(),
    }
    if return_potentials:
        result["potential_values"] = sorted(potentials.items(), key=lambda item: repr(item[0]))
    return result


def build_experiment(
    widths: Sequence[int] = tuple(range(3, 9)),
    discovery_widths: Sequence[int] = tuple(range(3, 7)),
) -> dict:
    normalized = tuple(sorted(set(widths)))
    discovery = tuple(sorted(set(discovery_widths)))
    if not normalized or any(width < 2 or width > 8 for width in normalized):
        raise ValueError("widths must be a nonempty subset of 2..8")
    if not set(discovery) <= set(normalized):
        raise ValueError("discovery widths must be among enumerated widths")
    sources = {width: enumerate_complete_source(width) for width in normalized}
    census = {
        str(width): {
            "states_by_layer": [len(layer) for layer in source.layers],
            "complete_transitions_by_row": [len(edges) for edges in source.edges],
            "optimum_charge": source.optimum,
            "maximum_forced": (width * width + 3 * width - source.optimum) // 3,
            "target_met": source.optimum >= (4 if width % 3 == 0 else 2),
            "corridor_transitions": {
                str(slack): sum(1 for _ in corridor_edges(source, slack))
                for slack in (0, 3, 6)
            },
        }
        for width, source in sources.items()
    }
    discovery_sources = [sources[n] for n in discovery]
    through_seven = [sources[n] for n in normalized if n <= 7]
    all_sources = [sources[n] for n in normalized]

    def staged(level: str, slack: int | None, target_mode: str) -> dict:
        result = {
            "discovery_3_through_6": solve_constraints(
                discovery_sources, level, slack, target_mode
            ),
            "with_held_out_7": solve_constraints(
                through_seven, level, slack, target_mode
            ),
        }
        if max(normalized) >= 8:
            result["with_held_out_8"] = solve_constraints(
                all_sources, level, slack, target_mode
            )
        return result

    experiments = {
        "one-block-top-debt:equality": staged(
            "ownership+top-debt", 0, "universal"
        ),
        "saturated-reserve:complete:universal": staged(
            "components+reserve", None, "universal"
        ),
        "saturated-reserve:complete:residue-zero": staged(
            "components+reserve", None, "residue-zero"
        ),
    }
    failed_history = experiments["one-block-top-debt:equality"]["with_held_out_7"]
    history_cycle = failed_history.get("counterexample_cycle", [])
    concrete_pump = [item["concrete"] for item in history_cycle if item["concrete"]]
    universal = experiments["saturated-reserve:complete:universal"]
    residue_zero = experiments["saturated-reserve:complete:residue-zero"]
    final_stage = "with_held_out_8" if max(normalized) >= 8 else "with_held_out_7"
    candidate_survives = universal[final_stage]["feasible"] and residue_zero[final_stage][
        "feasible"
    ]
    return {
        "scope": {
            "semantics": "finite-width-exact-CEGAR-not-a-uniform-proof",
            "enumerated_widths": list(normalized),
            "discovery_widths": list(discovery),
            "held_out_widths": sorted(set(normalized) - set(discovery)),
            "universal_terminal_target": 2,
            "residue_zero_terminal_target": 4,
        },
        "census": census,
        "experiments": experiments,
        "failed_refinement": {
            "kind": "same-exact-frontier-second-three-row-stitch",
            "width": 7,
            "corridor": "exact optimum",
            "negative_cycle_weight": failed_history.get("negative_cycle_weight"),
            "behavior_collision": {
                "rows_processed": [3, 6],
                "exact_frontier": {
                    "mask": 1,
                    "partition": [0, 0, 1, 2, 3, 4, 5],
                },
                "incoming_three_mask_history": [125, 1, 1],
                "one_block_top_debt": 3,
            },
            "concrete_steps": [
                {
                    "row": item["row"],
                    "incoming_state": item["incoming_state"],
                    "mask": item["mask"],
                    "outgoing_state": item["outgoing_state"],
                    "weight": item["weight"],
                }
                for item in concrete_pump
            ],
            "interpretation": (
                "Capping startup debt after one three-row block still identifies "
                "the exact frontier (mask=1, partition=(0,0,1,2,3,4,5)) after "
                "rows 3 and 6. The intervening straight production has charge 6; "
                "splicing it out gives a projected cycle of weight -4."
            ),
            "next_minimal_refinement": (
                "bank one completed positive three-row production in a saturated "
                "reserve bit; equivalently retain min(rows processed, 6)"
            ),
        },
        "candidate": {
            "survives_all_enumerated_complete_sources": candidate_survives,
            "semantics": "finite-width-candidate-not-a-uniform-proof",
            "history_coordinate": (
                "reserve = terminal at the bottom boundary; otherwise "
                "min(rows_processed, 6), represented by seven active values"
            ),
            "structural_feature": (
                "row phase mod 3; top/interior/terminal mode; forced count, runs "
                "and endpoint contacts; component count and boundary connection; "
                "sorted canonical component profiles "
                "(active size, interval count, forced contacts, boundary contacts, "
                "straight orientation); orientation multiplicities"
            ),
            "important_limit": (
                "the history coordinate is bounded and width-independent, but the "
                "unordered component-profile multiset can have width-dependent size; "
                "no raw mask, partition word, rows-remaining value, or width is stored"
            ),
            "universal_result": universal[final_stage],
            "residue_zero_result": residue_zero[final_stage],
        },
        "conclusion": (
            "bounded saturated-reserve history survives all complete enumerated widths"
            if candidate_survives
            else "no tested bounded history certifies every complete held-out source"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--widths", type=int, nargs="+", default=list(range(3, 9)))
    parser.add_argument("--discovery-widths", type=int, nargs="+", default=list(range(3, 7)))
    args = parser.parse_args()
    result = build_experiment(args.widths, args.discovery_widths)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
