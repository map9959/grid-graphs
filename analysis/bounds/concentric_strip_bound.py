#!/usr/bin/env python3
"""Laptop-scale concentric-strip upper-bound relaxation for square grids."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterable

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_one_pattern,
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)

SCHEMA = "grid-graphs.concentric-strip-bound.v1"
DEFAULT_OUTPUT = analysis_path("concentric_strip_bound.json")
KNOWN_RESIDUE_TWO_P = {5: 11, 8: 27, 11: 49, 14: 77, 17: 110}
EXACT_SMALL_P = {
    2: 2,
    3: 4,
    4: 8,
    5: 11,
    6: 16,
    7: 22,
    8: 27,
    9: 34,
    10: 42,
    11: 49,
    12: 58,
    13: 68,
    14: 77,
    15: 88,
    16: 100,
    17: 110,
}


@dataclass(frozen=True, slots=True)
class LayerChoice:
    side: int
    full_boundary: int
    full_corners: int
    weighted_boundary: int

    @property
    def noncorner_full(self) -> int:
        return self.full_boundary - self.full_corners

    @property
    def first_shoulder_minimum(self) -> int:
        """Minimum full count among eight sites one step along from a corner."""
        if self.side < 4:
            return 0
        noncorner_capacity = 4 * self.side - 8
        return max(0, self.noncorner_full - (noncorner_capacity - 8))

    @property
    def first_two_shoulders_minimum(self) -> int:
        """Minimum full count among the first two eight-site shoulder sets."""
        if self.side < 6:
            return self.first_shoulder_minimum
        noncorner_capacity = 4 * self.side - 8
        return max(0, self.noncorner_full - (noncorner_capacity - 16))


@dataclass(frozen=True, slots=True)
class RelaxationState:
    full_total: int
    leading_weights: tuple[int, ...]
    layers: tuple[LayerChoice, ...]


@dataclass(frozen=True, slots=True)
class RankRelaxationState:
    full_total: int
    maximum_induced_u_edges: int
    leading_layers: tuple[LayerChoice, ...]
    layers: tuple[LayerChoice, ...]
    center_full: int | None


def phi_two_by(length: int) -> int:
    if length < 2:
        raise ValueError("a two-row strip requires length at least two")
    return length


def phi_three_by(length: int) -> int:
    if length < 2:
        raise ValueError("a three-row strip requires length at least two")
    return (4 * length + 2) // 3


@lru_cache(maxsize=None)
def _all_boundary_choices(side: int) -> tuple[LayerChoice, ...]:
    if side < 2:
        raise ValueError("ordinary boundary choices require side at least two")
    perimeter = 4 * side - 4
    noncorners = max(0, perimeter - 4)
    return tuple(
        LayerChoice(side, corners + noncorner_full, corners, 2 * corners + noncorner_full)
        for corners in range(5)
        for noncorner_full in range(noncorners + 1)
    )


@lru_cache(maxsize=None)
def _boundary_choices(side: int) -> tuple[LayerChoice, ...]:
    by_signature = {}
    for choice in _all_boundary_choices(side):
        signature = (
            choice.weighted_boundary,
            choice.first_shoulder_minimum,
            choice.first_two_shoulders_minimum,
        )
        retained = by_signature.get(signature)
        if retained is None or (choice.full_boundary, choice.full_corners) > (
            retained.full_boundary,
            retained.full_corners,
        ):
            by_signature[signature] = choice
    return tuple(by_signature[key] for key in sorted(by_signature))


@lru_cache(maxsize=None)
def maximum_perimeter_u_edges(side: int, u_count: int, u_corners: int) -> int:
    """Maximum adjacent U-U pairs on a side-s perimeter with fixed corner count."""
    if side < 2:
        raise ValueError("a perimeter requires side at least two")
    length = 4 * side - 4
    corners = {0, side - 1, 2 * (side - 1), 3 * (side - 1)}
    if not 0 <= u_count <= length or not 0 <= u_corners <= 4:
        return -1
    best = -1
    for first in (0, 1):
        # (used U, used U corners, final bit) -> maximum linear adjacency count.
        states = {(first, int(first and 0 in corners), first): 0}
        for position in range(1, length):
            children = {}
            for (used, used_corners, previous), value in states.items():
                for bit in (0, 1):
                    key = (
                        used + bit,
                        used_corners + int(bit and position in corners),
                        bit,
                    )
                    candidate = value + previous * bit
                    children[key] = max(children.get(key, -1), candidate)
            states = children
        for (used, used_corners, last), value in states.items():
            if (used, used_corners) == (u_count, u_corners):
                best = max(best, value + last * first)
    return best


def _initial_states(n: int) -> dict[tuple[int, ...], RelaxationState]:
    if n % 2:
        # A singleton center occurs in all four depth-two side strips.
        return {
            (0, 0, -1): RelaxationState(0, (0, 0, -1), ()),
            (4, 0, -1): RelaxationState(1, (4, 0, -1), ()),
        }
    result = {}
    for choice in _boundary_choices(2):
        if choice.full_corners != choice.full_boundary:
            continue
        if 3 * choice.full_boundary > 2 + choice.weighted_boundary:
            continue
        key = (choice.weighted_boundary, 0, -1)
        result[key] = RelaxationState(
            choice.full_boundary,
            key,
            (choice,),
        )
    return result


@lru_cache(maxsize=None)
def solve_relaxation(
    n: int,
    include_depth_three: bool = True,
    use_exact_small_anchors: bool = False,
) -> RelaxationState:
    """Maximize full vertices under degree and weakened concentric strip bounds."""
    if n < 2:
        raise ValueError("concentric relaxation requires n at least two")
    states = _initial_states(n)
    first_side = 3 if n % 2 else 4
    for side in range(first_side, n + 1, 2):
        next_states: dict[tuple[int, ...], RelaxationState] = {}
        for inner in states.values():
            inner_weight = inner.leading_weights[0]
            inner_shoulder = inner.leading_weights[1]
            second_inner = inner.leading_weights[2]
            for choice in _boundary_choices(side):
                full_total = inner.full_total + choice.full_boundary
                if (
                    use_exact_small_anchors
                    and side in EXACT_SMALL_P
                    and full_total > EXACT_SMALL_P[side]
                ):
                    continue
                if 3 * full_total > side * side - 2 + choice.weighted_boundary:
                    continue
                if (
                    choice.weighted_boundary
                    + inner_weight
                    + choice.first_shoulder_minimum
                    > 4 * side
                ):
                    continue
                if (
                    include_depth_three
                    and side >= 6
                    and second_inner >= 0
                    and choice.weighted_boundary
                    + inner_weight
                    + second_inner
                    + choice.first_two_shoulders_minimum
                    + inner_shoulder
                    > 4 * phi_three_by(side)
                ):
                    continue
                leading = (
                    choice.weighted_boundary,
                    choice.first_shoulder_minimum,
                    inner_weight,
                )
                candidate = RelaxationState(
                    full_total,
                    leading,
                    (choice, *inner.layers),
                )
                retained = next_states.get(leading)
                if retained is None or (
                    candidate.full_total,
                    tuple((item.full_boundary, item.full_corners) for item in candidate.layers),
                ) > (
                    retained.full_total,
                    tuple((item.full_boundary, item.full_corners) for item in retained.layers),
                ):
                    next_states[leading] = candidate
        if not next_states:
            raise AssertionError(f"concentric relaxation became empty at side {side}")
        states = next_states
    return max(
        states.values(),
        key=lambda state: (
            state.full_total,
            tuple((item.full_boundary, item.full_corners) for item in state.layers),
        ),
    )


def _rank_initial_states(n: int) -> tuple[RankRelaxationState, ...]:
    if n % 2:
        return tuple(
            RankRelaxationState(full, 0, (), (), full)
            for full in (0, 1)
        )
    states = []
    for choice in _all_boundary_choices(2):
        if choice.full_corners != choice.full_boundary:
            continue
        u_count = 4 - choice.full_boundary
        maximum_edges = maximum_perimeter_u_edges(2, u_count, u_count)
        if maximum_edges < 1:
            continue
        states.append(
            RankRelaxationState(
                choice.full_boundary,
                maximum_edges,
                (choice,),
                (choice,),
                None,
            )
        )
    return tuple(states)


def _pareto_rank_states(
    states: tuple[RankRelaxationState, ...],
    include_depth_three: bool,
) -> tuple[RankRelaxationState, ...]:
    grouped: dict[tuple, list[RankRelaxationState]] = {}
    for state in states:
        key = (
            (
                state.leading_layers[0].full_boundary,
                state.leading_layers[0].full_corners,
            ),
            (
                state.leading_layers[1].weighted_boundary
                if include_depth_three and len(state.leading_layers) > 1
                else -1
            ),
        )
        grouped.setdefault(key, []).append(state)
    result = []
    for values in grouped.values():
        best_edges = -1
        for state in sorted(
            values,
            key=lambda item: (item.full_total, item.maximum_induced_u_edges),
            reverse=True,
        ):
            if state.maximum_induced_u_edges <= best_edges:
                continue
            result.append(state)
            best_edges = state.maximum_induced_u_edges
    return tuple(result)


@lru_cache(maxsize=None)
def solve_rank_relaxation(
    n: int, include_depth_three: bool = True
) -> RankRelaxationState:
    """Add necessary dual-rank supply to the concentric strip relaxation."""
    if n < 2:
        raise ValueError("rank-aware concentric relaxation requires n at least two")
    states = _rank_initial_states(n)
    first_side = 3 if n % 2 else 4
    for side in range(first_side, n + 1, 2):
        retained: dict[tuple, RankRelaxationState] = {}
        for inner in states:
            inner_choice = inner.leading_layers[0] if inner.leading_layers else None
            second_inner = (
                inner.leading_layers[1] if len(inner.leading_layers) > 1 else None
            )
            for choice in _all_boundary_choices(side):
                full_total = inner.full_total + choice.full_boundary
                if 3 * full_total > side * side - 2 + choice.weighted_boundary:
                    continue
                inner_weight = (
                    inner_choice.weighted_boundary
                    if inner_choice is not None
                    else 4 * int(inner.center_full or 0)
                )
                inner_shoulder = (
                    inner_choice.first_shoulder_minimum
                    if inner_choice is not None
                    else 0
                )
                if (
                    choice.weighted_boundary
                    + inner_weight
                    + choice.first_shoulder_minimum
                    > 4 * side
                ):
                    continue
                if (
                    include_depth_three
                    and side >= 6
                    and second_inner is not None
                    and choice.weighted_boundary
                    + inner_weight
                    + second_inner.weighted_boundary
                    + choice.first_two_shoulders_minimum
                    + inner_shoulder
                    > 4 * phi_three_by(side)
                ):
                    continue

                perimeter = 4 * side - 4
                outer_u = perimeter - choice.full_boundary
                outer_u_corners = 4 - choice.full_corners
                outer_u_noncorner = outer_u - outer_u_corners
                ring_edges = maximum_perimeter_u_edges(
                    side, outer_u, outer_u_corners
                )
                if inner_choice is None:
                    radial_capacity = 4 * (1 - int(inner.center_full or 0))
                else:
                    inner_perimeter = 4 * inner_choice.side - 4
                    inner_u = inner_perimeter - inner_choice.full_boundary
                    inner_u_corners = 4 - inner_choice.full_corners
                    radial_capacity = inner_u + inner_u_corners
                radial_edges = min(outer_u_noncorner, radial_capacity)
                maximum_edges = (
                    inner.maximum_induced_u_edges + ring_edges + radial_edges
                )
                if maximum_edges < (side - 1) ** 2:
                    continue
                leading = (choice, *(inner.leading_layers[:1]))
                candidate = RankRelaxationState(
                    full_total,
                    maximum_edges,
                    leading,
                    (choice, *inner.layers),
                    inner.center_full,
                )
                signature = (
                    tuple(
                        (item.full_boundary, item.full_corners) for item in leading
                    ),
                    full_total,
                )
                previous = retained.get(signature)
                if previous is None or candidate.maximum_induced_u_edges > previous.maximum_induced_u_edges:
                    retained[signature] = candidate
        if not retained:
            raise AssertionError(f"rank-aware relaxation became empty at side {side}")
        states = _pareto_rank_states(tuple(retained.values()), include_depth_three)
    return max(
        states,
        key=lambda state: (state.full_total, state.maximum_induced_u_edges),
    )


def _square_layer(rows: tuple[str, ...], offset: int) -> dict:
    n = len(rows)
    side = n - 2 * offset
    cells = [
        (row, col)
        for row in range(offset, n - offset)
        for col in range(offset, n - offset)
    ]
    boundary = [
        (row, col)
        for row, col in cells
        if row in (offset, n - offset - 1) or col in (offset, n - offset - 1)
    ]
    corners = {
        (offset, offset),
        (offset, n - offset - 1),
        (n - offset - 1, offset),
        (n - offset - 1, n - offset - 1),
    }
    is_full = lambda cell: rows[cell[0]][cell[1]] == "."
    full_total = sum(map(is_full, cells))
    full_boundary = sum(map(is_full, boundary))
    full_corners = sum(map(is_full, corners)) if side >= 2 else 0
    weighted = 4 * full_total if side == 1 else full_boundary + full_corners
    report = {
        "side": side,
        "full_total": full_total,
        "full_boundary": full_boundary,
        "full_corners": full_corners,
        "weighted_boundary": weighted,
    }
    if side >= 2:
        report["degree_inequality_slack"] = (
            side * side - 2 + weighted - 3 * full_total
        )
    return report


def verify_pattern(rows: Iterable[str]) -> dict:
    materialized = tuple(rows)
    n = len(materialized)
    if n < 2 or any(len(row) != n or set(row) - {"U", "."} for row in materialized):
        raise ValueError("pattern must be a square U/. word array")
    layers = tuple(_square_layer(materialized, offset) for offset in range((n + 1) // 2))
    for layer in layers:
        if layer.get("degree_inequality_slack", 0) < 0:
            raise AssertionError("known pattern violates a nested degree inequality")
    depth_two = []
    depth_three = []
    for index, layer in enumerate(layers):
        side = layer["side"]
        if side >= 3:
            strip_sum = 0
            start = index
            stop = n - index
            strips = (
                ((start, start + 2), (start, stop)),
                ((stop - 2, stop), (start, stop)),
                ((start, stop), (start, start + 2)),
                ((start, stop), (stop - 2, stop)),
            )
            for (row_start, row_stop), (col_start, col_stop) in strips:
                strip_sum += sum(
                    materialized[row][col] == "."
                    for row in range(row_start, row_stop)
                    for col in range(col_start, col_stop)
                )
            limit = 4 * phi_two_by(side)
            if strip_sum > limit:
                raise AssertionError("known pattern violates a depth-two strip inequality")
            depth_two.append({"side": side, "full_incidence_sum": strip_sum, "limit": limit})
        if side >= 3:
            strip_sum = 0
            start = index
            stop = n - index
            strips = (
                ((start, start + 3), (start, stop)),
                ((stop - 3, stop), (start, stop)),
                ((start, stop), (start, start + 3)),
                ((start, stop), (stop - 3, stop)),
            )
            for (row_start, row_stop), (col_start, col_stop) in strips:
                strip_sum += sum(
                    materialized[row][col] == "."
                    for row in range(row_start, row_stop)
                    for col in range(col_start, col_stop)
                )
            limit = 4 * phi_three_by(side)
            if strip_sum > limit:
                raise AssertionError("known pattern violates a depth-three strip inequality")
            depth_three.append({"side": side, "full_incidence_sum": strip_sum, "limit": limit})
    return {
        "n": n,
        "full_vertices": sum(row.count(".") for row in materialized),
        "layers": list(layers),
        "depth_two_strips": depth_two,
        "depth_three_strips": depth_three,
    }


def _residue_two_candidate(n: int) -> int:
    k = (n - 2) // 3
    return 3 * k * k + 7 * k + int(k < 5)


def build_artifact(max_n: int = 20) -> dict:
    if max_n < 20:
        raise ValueError("artifact horizon must include n=20")
    table = []
    for n in range(2, max_n + 1):
        degree_and_two = solve_relaxation(n, include_depth_three=False)
        with_three = solve_relaxation(n, include_depth_three=True)
        anchored = solve_relaxation(
            n, include_depth_three=True, use_exact_small_anchors=True
        )
        rank_only = solve_rank_relaxation(n, include_depth_three=False)
        rank_aware_bound = min(with_three.full_total, rank_only.full_total)
        table.append(
            {
                "n": n,
                "degree_plus_depth_two_bound": degree_and_two.full_total,
                "degree_plus_depth_two_three_bound": with_three.full_total,
                "depth_three_improvement": degree_and_two.full_total - with_three.full_total,
                "rank_aware_bound": rank_aware_bound,
                "rank_improvement": with_three.full_total - rank_aware_bound,
                "exact_small_anchored_bound": anchored.full_total,
                "exact_small_anchor_improvement": with_three.full_total - anchored.full_total,
            }
        )
    residue_two = []
    for n in range(5, min(max_n, 20) + 1, 3):
        state = solve_relaxation(n, include_depth_three=True)
        anchored = solve_relaxation(
            n, include_depth_three=True, use_exact_small_anchors=True
        )
        rank_state = solve_rank_relaxation(n, include_depth_three=False)
        rank_bound = min(state.full_total, rank_state.full_total)
        candidate = _residue_two_candidate(n)
        residue_two.append(
            {
                "n": n,
                "known_or_candidate_P": KNOWN_RESIDUE_TWO_P.get(n, candidate),
                "proposed_formula_P": candidate,
                "relaxation_upper_bound_P": state.full_total,
                "gap_above_proposed_formula": state.full_total - candidate,
                "rank_aware_upper_bound_P": rank_bound,
                "rank_aware_gap_above_proposed_formula": rank_bound - candidate,
                "rank_improvement": state.full_total - rank_bound,
                "exact_small_anchored_upper_bound_P": anchored.full_total,
                "exact_small_anchored_gap_above_proposed_formula": anchored.full_total - candidate,
                "exact_small_anchor_improvement": state.full_total - anchored.full_total,
                "maximizing_layers": [
                    {
                        "side": item.side,
                        "full_boundary": item.full_boundary,
                        "full_corners": item.full_corners,
                        "weighted_boundary": item.weighted_boundary,
                    }
                    for item in state.layers
                ],
            }
        )
    witnesses = {
        f"n{n}-exact": verify_pattern(residue_two_explicit_pattern(n))
        for n in (5, 8, 11, 14)
    }
    witnesses["n4-exact-soundness-control"] = verify_pattern(residue_one_pattern(4))
    witnesses["n17-affine-exact"] = verify_pattern(residue_two_affine_pattern(17))
    phase_path = analysis_path("residue_two_phase_front_witness.txt")
    phase_rows = tuple(
        line.strip()
        for line in phase_path.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    )
    witnesses["n20-phase-250-U"] = verify_pattern(phase_rows)
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "valid-integer-relaxation-not-a-sharp-grid-proof",
            "n_range": [2, max_n],
            "uses_exact_thin_grid_theorems": ["P(2,s)=s", "P(3,s)=floor((4s+2)/3)"],
        },
        "definitions": {
            "weighted_boundary": "full boundary vertices plus full geometric corners",
            "nested_degree": "3F_j <= s_j^2 - 2 + B_j",
            "depth_two_relaxation": "B_j+B_(j+1)+X_j <= 4s_j, using the minimum forced occupancy of the eight first-shoulder sites",
            "depth_three_relaxation": "B_j+B_(j+1)+B_(j+2)+X_j+Y_j+X_(j+1) <= 4 floor((4s_j+2)/3), using minimum forced shoulder occupancy",
        },
        "table": table,
        "residue_two": residue_two,
        "witness_validation": witnesses,
        "conclusion": (
            "The scalar concentric-strip recurrence is valid and laptop-scale, but its "
            "residue-two upper bounds remain above the proposed formula. Connectivity "
            "or ordered annulus attachment data is required beyond scalar layer counts."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=20)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(args.max_n), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"concentric strip bound matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
