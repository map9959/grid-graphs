#!/usr/bin/env python3
"""Exact symbolic compression test for the forced-forest lookup potential.

This fits the canonical shortest feasible potential on the complete pooled
widths 3..8 to additive component statistics and joint phase/reserve constants.
Failure is reported by an exact linear dependence among sampled state equations.
It blocks this compression of this lookup potential; it is not automatically a
Farkas certificate against every other feasible potential in the same basis.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from analysis.bounds.forced_forest_diagonal_cegar import (
    corridor_edges,
    enumerate_complete_source,
    feature,
    solve_constraints,
)


NUMERIC_NAMES = (
    "forced_count",
    "forced_runs",
    "left_forced",
    "right_forced",
    "components",
    "active_size_sum",
    "interval_sum",
    "forced_contact_sum",
    "left_component_contacts",
    "right_component_contacts",
    "passive_components",
    "vertical_components",
    "horizontal_components",
    "mixed_components",
)
HINGE_NAMES = (
    "repeated_interval_excess",
    "repeated_forced_contact_excess",
    "passive_span_excess",
    "component_surplus_over_two",
    "component_surplus_and_repeated_interval",
    "component_surplus_and_passive_interval",
    "component_surplus_and_vertical_interval",
    "component_surplus_and_horizontal_interval",
    "component_surplus_and_mixed_interval",
)


def _fraction(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def _design(feature: tuple, categories: tuple[tuple, ...], hinges: bool) -> list[Fraction]:
    if feature in (("zero",), ("initial",)):
        return [Fraction(0)] * (
            len(categories) + len(NUMERIC_NAMES) + (len(HINGE_NAMES) if hinges else 0)
        )
    category = feature[:3]
    numeric = feature[3:]
    return [
        *(Fraction(category == observed) for observed in categories),
        *(Fraction(value) for value in numeric),
    ]


def fit_lookup(
    potentials: list[tuple[tuple, Fraction]], hinges: bool
) -> dict:
    ordinary = [(state, value) for state, value in potentials if state not in (("zero",), ("initial",))]
    categories = tuple(sorted({state[:3] for state, _ in ordinary}, key=repr))
    names = tuple(f"category:{category!r}" for category in categories) + NUMERIC_NAMES
    if hinges:
        names += HINGE_NAMES
    basis: dict[int, tuple[list[Fraction], Fraction, dict[int, Fraction]]] = {}
    observations = []
    conflict = None
    for index, (state, target) in enumerate(ordinary):
        row = _design(state, categories, hinges)
        provenance = {index: Fraction(1)}
        for pivot in sorted(basis):
            factor = row[pivot]
            if not factor:
                continue
            known_row, known_rhs, known_provenance = basis[pivot]
            row = [left - factor * right for left, right in zip(row, known_row)]
            target -= factor * known_rhs
            for equation, value in known_provenance.items():
                provenance[equation] = provenance.get(equation, Fraction(0)) - factor * value
                if not provenance[equation]:
                    del provenance[equation]
        pivot = next((column for column, value in enumerate(row) if value), None)
        observations.append((state, ordinary[index][1]))
        if pivot is None:
            if target:
                conflict = (target, provenance)
                break
            continue
        scale = row[pivot]
        row = [value / scale for value in row]
        target /= scale
        provenance = {equation: value / scale for equation, value in provenance.items()}
        basis[pivot] = row, target, provenance

    if conflict is not None:
        residual, provenance = conflict
        reconstructed = [Fraction(0)] * len(names)
        reconstructed_rhs = Fraction(0)
        for equation, multiplier in provenance.items():
            state, target = observations[equation]
            row = _design(state, categories, hinges)
            reconstructed = [
                value + multiplier * term for value, term in zip(reconstructed, row)
            ]
            reconstructed_rhs += multiplier * target
        if any(reconstructed) or reconstructed_rhs != residual:
            raise AssertionError("exact lookup-compression obstruction failed replay")
        return {
            "fits": False,
            "basis_terms": len(names),
            "rank": len(basis),
            "equations_processed": len(observations),
            "exact_conflict": {
                "zero_left_hand_side": True,
                "nonzero_right_hand_side": _fraction(residual),
                "equations": [
                    {
                        "multiplier": _fraction(multiplier),
                        "feature": observations[equation][0],
                        "lookup_potential": _fraction(observations[equation][1]),
                    }
                    for equation, multiplier in sorted(provenance.items())
                ],
            },
        }

    coefficients = [Fraction(0)] * len(names)
    for pivot in sorted(basis, reverse=True):
        row, rhs, _ = basis[pivot]
        coefficients[pivot] = rhs - sum(
            row[column] * coefficients[column] for column in range(pivot + 1, len(names))
        )
    for state, target in ordinary:
        actual = sum(
            coefficient * value
            for coefficient, value in zip(coefficients, _design(state, categories, hinges))
        )
        if actual != target:
            raise AssertionError("exact fitted formula failed lookup replay")
    return {
        "fits": True,
        "basis_terms": len(names),
        "rank": len(basis),
        "coefficients": {
            name: _fraction(value) for name, value in zip(names, coefficients) if value
        },
    }


def formula_constraints(sources, level: str = "additive+hinges"):
    """Build deduplicated coefficient halfspaces for the actual local lemma."""
    state_features = []
    for source in sources:
        for row, layer in enumerate(source.layers):
            state_features.extend(
                feature(source.width, row, state, level)
                for state in layer
                if state is not None
            )
    categories = tuple(sorted({item[:3] for item in state_features}, key=repr))
    names = tuple(f"category:{category!r}" for category in categories) + NUMERIC_NAMES + HINGE_NAMES
    strongest: dict[tuple[int, ...], int] = {}

    def retain(row: list[Fraction], rhs: int) -> None:
        integer_row = tuple(int(value) for value in row)
        old = strongest.get(integer_row)
        if old is None or rhs < old:
            strongest[integer_row] = rhs

    for source in sources:
        target = 4 if source.width % 3 == 0 else 2
        for terminal in source.layers[-1]:
            if terminal is None:
                continue
            design = _design(feature(source.width, source.width, terminal, level), categories, True)
            retain([-value for value in design], -target)
        for edge in corridor_edges(source, None):
            incoming = _design(
                feature(source.width, edge.row, edge.incoming, level), categories, True
            )
            outgoing = _design(
                feature(source.width, edge.row + 1, edge.outgoing, level), categories, True
            )
            retain([right - left for left, right in zip(incoming, outgoing)], edge.weight)
    constraints = [(row, rhs) for row, rhs in sorted(strongest.items())]
    return names, categories, constraints


def projected_candidate(
    constraints: list[tuple[tuple[int, ...], int]], epochs: int = 80
) -> list[float]:
    """Find a floating proposal by cyclic orthogonal halfspace projection."""
    dimensions = len(constraints[0][0])
    values = [0.0] * dimensions
    norms = [sum(value * value for value in row) for row, _ in constraints]
    for _epoch in range(epochs):
        maximum = 0.0
        for (row, rhs), norm in zip(constraints, norms):
            violation = sum(value * coefficient for value, coefficient in zip(values, row)) - rhs
            maximum = max(maximum, violation)
            if violation > 1e-10 and norm:
                scale = violation / norm
                values = [value - scale * coefficient for value, coefficient in zip(values, row)]
        if maximum <= 1e-9:
            break
    return values


def projected_farkas_seed(
    constraints: list[tuple[tuple[int, ...], int]], epochs: int = 600
) -> tuple[list[float], list[float]]:
    """Return projection coefficients and accumulated nonnegative corrections."""
    dimensions = len(constraints[0][0])
    values = [0.0] * dimensions
    multipliers = [0.0] * len(constraints)
    norms = [sum(value * value for value in row) for row, _ in constraints]
    for _epoch in range(epochs):
        for index, ((row, rhs), norm) in enumerate(zip(constraints, norms)):
            violation = sum(value * coefficient for value, coefficient in zip(values, row)) - rhs
            if violation > 1e-10 and norm:
                scale = violation / norm
                multipliers[index] += scale
                values = [value - scale * coefficient for value, coefficient in zip(values, row)]
    return values, multipliers


def exact_farkas_from_seed(
    constraints: list[tuple[tuple[int, ...], int]],
    seed: list[float],
    support_order: list[int] | None = None,
) -> dict | None:
    """Try exact row reduction around an approximate nonnegative dual seed."""
    available = {index for index, value in enumerate(seed) if value > 1e-9}
    support = (
        [index for index in support_order if index in available]
        if support_order is not None
        else sorted(available, key=lambda index: seed[index], reverse=True)
    )
    if not support:
        return None
    dimensions = len(constraints[0][0])
    # Equations are A^T y = 0 and sum y = 1. Prefer large seed entries as pivots.
    matrix = [
        [Fraction(constraints[index][0][dimension]) for index in support] + [Fraction(0)]
        for dimension in range(dimensions)
    ]
    matrix.append([Fraction(1) for _ in support] + [Fraction(1)])
    pivot_columns = []
    pivot_row = 0
    for column in range(len(support)):
        selected = next(
            (row for row in range(pivot_row, len(matrix)) if matrix[row][column]), None
        )
        if selected is None:
            continue
        matrix[pivot_row], matrix[selected] = matrix[selected], matrix[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        for row in range(len(matrix)):
            if row == pivot_row or not matrix[row][column]:
                continue
            scale = matrix[row][column]
            matrix[row] = [
                left - scale * right
                for left, right in zip(matrix[row], matrix[pivot_row])
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(matrix):
            break
    if any(not any(row[:-1]) and row[-1] for row in matrix):
        return None
    # Keep the approximate dual ray only as one common scale lambda. Solving the
    # pivot equations makes every multiplier affine in lambda, so positivity and
    # negative RHS reduce to one exact rational interval.
    values = [
        (Fraction(0), Fraction(seed[index]).limit_denominator(10**6))
        for index in support
    ]
    for row, column in reversed(list(enumerate(pivot_columns))):
        constant = matrix[row][-1] - sum(
            matrix[row][other] * values[other][0]
            for other in range(column + 1, len(support))
        )
        slope = -sum(
            matrix[row][other] * values[other][1]
            for other in range(column + 1, len(support))
        )
        values[column] = constant, slope
    rhs_constant = sum(
        value[0] * constraints[index][1] for index, value in zip(support, values)
    )
    rhs_slope = sum(
        value[1] * constraints[index][1] for index, value in zip(support, values)
    )
    lower = Fraction(0)
    upper: Fraction | None = None
    for constant, slope in values:
        if slope > 0:
            lower = max(lower, -constant / slope)
        elif slope < 0:
            bound = constant / -slope
            upper = bound if upper is None else min(upper, bound)
        elif constant < 0:
            return None
    if rhs_slope < 0:
        lower = max(lower, -rhs_constant / rhs_slope)
    elif rhs_slope > 0:
        bound = -rhs_constant / rhs_slope
        upper = bound if upper is None else min(upper, bound)
    elif rhs_constant >= 0:
        return None
    if upper is not None and lower >= upper:
        return None
    parameter = lower + 1 if upper is None else (lower + upper) / 2
    scalar_values = [constant + parameter * slope for constant, slope in values]
    if any(value < 0 for value in scalar_values):
        return None
    normal = [
        sum(value * constraints[index][0][dimension] for index, value in zip(support, scalar_values))
        for dimension in range(dimensions)
    ]
    rhs = sum(value * constraints[index][1] for index, value in zip(support, scalar_values))
    if any(normal) or rhs >= 0:
        return None
    return {
        "rhs": _fraction(rhs),
        "terms": [
            {
                "constraint_index": index,
                "multiplier": _fraction(value),
                "normal": list(constraints[index][0]),
                "rhs": constraints[index][1],
            }
            for index, value in zip(support, scalar_values)
            if value
        ],
    }


def verify_formula(
    coefficients: list[Fraction], constraints: list[tuple[tuple[int, ...], int]]
) -> dict:
    minimum_slack: Fraction | None = None
    tight = 0
    violation = None
    for index, (row, rhs) in enumerate(constraints):
        left = sum(value * coefficient for value, coefficient in zip(coefficients, row))
        slack = Fraction(rhs) - left
        if minimum_slack is None or slack < minimum_slack:
            minimum_slack = slack
        tight += slack == 0
        if slack < 0 and violation is None:
            violation = {"index": index, "left": _fraction(left), "right": [rhs, 1]}
    return {
        "feasible": violation is None,
        "constraints": len(constraints),
        "tight": tight,
        "minimum_slack": _fraction(minimum_slack or Fraction(0)),
        "first_violation": violation,
    }


def build_artifact() -> dict:
    sources = [enumerate_complete_source(width) for width in range(3, 9)]
    experiments = {}
    for level, hinges in (("additive", False), ("additive+hinges", True)):
        lookup = solve_constraints(
            sources, level, None, "residue-zero", return_potentials=True
        )
        potentials = lookup.pop("potential_values")
        experiments[level] = {
            "lookup_difference_constraints": lookup,
            "symbolic_compression": fit_lookup(potentials, hinges),
        }
    names, _categories, constraints = formula_constraints(sources)
    proposal = projected_candidate(constraints, 200)
    rational_proposal = [Fraction(value).limit_denominator(10_000) for value in proposal]
    direct_verification = verify_formula(rational_proposal, constraints)
    return {
        "scope": {
            "widths": list(range(3, 9)),
            "discovery_widths": [3, 4, 5, 6],
            "held_out_widths": [7, 8],
            "transitions": "complete reachable source at every listed width",
            "arithmetic": "Fraction only after integer difference-potential synthesis",
            "claim_limit": (
                "an exact conflict blocks linear representation of the canonical "
                "shortest lookup potential, not every possible feasible potential"
            ),
        },
        "basis": {
            "attempted_formula": (
                "Phi(s) = C[phase,boundary,reserve] + sum_i a_i statistic_i(s); "
                "required locally: Phi(out)-Phi(in) <= n+3-3|F_row|, with "
                "Phi(initial)=0 and terminal Phi>=2 (>=4 in residue zero)"
            ),
            "piecewise_constants": "one constant per (phase, boundary mode, saturated reserve)",
            "additive_terms": list(NUMERIC_NAMES),
            "hinges": list(HINGE_NAMES),
        },
        "experiments": experiments,
        "direct_transition_system": {
            "basis_terms": len(names),
            "deduplicated_halfspaces": len(constraints),
            "floating_method": "200 cyclic orthogonal-projection passes",
            "rationalization_denominator_limit": 10_000,
            "exact_fraction_replay": direct_verification,
            "status": "unresolved-no-exact-candidate-and-no-exact-infeasibility-certificate",
            "diagnostic_limit": (
                "the failed rational proposal and floating dual behavior are not "
                "evidence of mathematical infeasibility"
            ),
        },
        "conclusion": (
            "the interaction basis does not reproduce the canonical lookup; direct "
            "transition-inequality feasibility remains unresolved"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
