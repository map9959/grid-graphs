#!/usr/bin/env python3
"""Bounded structural frontier-word potential synthesis at n=5 and n=8 only.

This is a diagnostic finite experiment, not an arbitrary-width certificate.  It
uses no cumulative U, rank, cycle, distance, or curvature feature.

Regeneration creates a very large sparse LP and requires an explicit CLI opt-in.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from collections import Counter
from fractions import Fraction
from pathlib import Path

from analysis.transport.equality_corridor import EqualityCorridor, build_equality_corridor, structural_key
from analysis.residue_certificates.residue_two_cap_merge_potential import cap_phase
from analysis.residue_certificates.residue_two_obligation5_potential import _rref_solve
from analysis.residue_certificates.residue_two_silent_hull_language import (
    SilentHullAtom,
    classify_silent_hull_frontier,
)
from analysis.tiles.tile_grammar import FrontierState, advance_row
from analysis._paths import analysis_path


WIDTHS = (5, 8)
STAGES = ("atom-sum", "adjacent-bigrams", "finite-parser")
SCHEMA = "grid-graphs.residue-two-silent-hull-potential-experiment.v7"
DEFAULT_OUTPUT = analysis_path("residue_two_silent_hull_potential_experiment.json")
MAX_COUNTEREXAMPLES = 8
PROJECTION_UPDATE_BOUND = 2_000_000
PROJECTION_PASS_BOUND = 200
RATIONAL_DENOMINATOR_LIMITS = (1_000, 10_000, 1_000_000)
HIGHS_RATIONAL_DENOMINATOR_LIMITS = (1_000, 10_000, 1_000_000, 1_000_000_000)
HIGHS = Path("/tmp/opencode/bin/highs")
HIGHS_WORK = Path("/tmp/opencode")


def _fraction_json(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def _state_json(state: FrontierState) -> dict:
    return {
        "row": state.row_index,
        "previous_mask": f"0b{state.previous_u_mask:0{state.n}b}",
        "partition": list(state.partition),
    }


def _atom_name(atom: SilentHullAtom) -> str:
    value = [
        atom.previous_word,
        list(atom.rooted_restriction),
        [
            [role.local_label, int(role.carries_in), int(role.carries_out)]
            for role in atom.roles
        ],
        int(atom.silent_carry),
    ]
    return "atom:" + json.dumps(value, separators=(",", ":"))


def _hull_status(atom: SilentHullAtom) -> tuple[bool, bool]:
    incoming = atom.silent_carry or any(role.carries_in for role in atom.roles)
    outgoing = atom.silent_carry or any(role.carries_out for role in atom.roles)
    return incoming, outgoing


def structural_terms(state: FrontierState, stage: str = "atom-sum") -> Counter[str]:
    """Return only finite-control terms and SilentHullAtom occurrence counts."""
    if stage not in STAGES:
        raise ValueError(f"unknown refinement stage: {stage}")
    decision = classify_silent_hull_frontier(state)
    if not decision.accepted or decision.encoded is None:
        raise ValueError(decision.reason or "state is outside the silent-hull language")
    encoded = decision.encoded
    phase = cap_phase(state.n, state.row_index)
    cap = f"{encoded.previous_cap_bits[0]}{encoded.previous_cap_bits[1]}"
    terms = Counter(
        {
            f"cap:{cap}": 1,
            f"phase:{phase}": 1,
            f"left-role:{encoded.left_face_role}": 1,
            f"cap-phase-left-role:{cap}:{phase}:{encoded.left_face_role}": 1,
        }
    )
    atoms = tuple(_atom_name(atom) for atom in encoded.atoms)
    terms.update(atoms)
    if STAGES.index(stage) >= STAGES.index("adjacent-bigrams"):
        left_boundary = json.dumps(
            ["left", cap, phase, encoded.left_face_role], separators=(",", ":")
        )
        right_boundary = json.dumps(
            ["right", cap, phase], separators=(",", ":")
        )
        word = (left_boundary, *atoms, right_boundary)
        terms.update(
            "bigram:" + json.dumps([left, right], separators=(",", ":"))
            for left, right in zip(word, word[1:])
        )
    if stage == "finite-parser":
        active = encoded.left_face_role == "open"
        previous_boundary_bits = encoded.previous_cap_bits
        for atom, atom_name in zip(encoded.atoms, atoms):
            incoming, outgoing = _hull_status(atom)
            if incoming != active:
                raise AssertionError("silent-hull word has inconsistent parser activity")
            current_boundary_bits = (atom.previous_word & 1, (atom.previous_word >> 2) & 1)
            terms[
                "parser-transition:"
                + json.dumps(
                    [
                        phase,
                        int(active),
                        list(previous_boundary_bits),
                        atom_name,
                        int(outgoing),
                        list(current_boundary_bits),
                    ],
                    separators=(",", ":"),
                )
            ] += 1
            active = outgoing
            previous_boundary_bits = current_boundary_bits
        terms[
            "parser-accept:"
            + json.dumps(
                [phase, int(active), list(previous_boundary_bits), encoded.previous_cap_bits[1]],
                separators=(",", ":"),
            )
        ] += 1
    return terms


def _potential(terms: Counter[str], coefficients: dict[str, Fraction]) -> Fraction:
    return sum((coefficients.get(name, Fraction(0)) * count for name, count in terms.items()), Fraction(0))


def _edge_weight(incoming: FrontierState, mask: int, outgoing: FrontierState) -> int:
    source_components = len(set(incoming.partition)) - 1
    target_components = len(set(outgoing.partition)) - 1
    new_faces = 0 if outgoing.row_index == outgoing.n else outgoing.n - 1
    rank = new_faces + source_components - target_components
    return 3 * mask.bit_count() - 2 * rank - 1


def _training(corridors: dict[int, EqualityCorridor], stage: str):
    observations = []
    names = set()
    for n in WIDTHS:
        corridor = corridors[n]
        for row, keys in enumerate(corridor.corridor_states):
            for key in sorted(keys):
                state = corridor.layers[row][key]
                terms = structural_terms(state, stage)
                names.update(terms)
                observations.append((n, state, terms, Fraction(-corridor.forward[row][key])))
    ordered_names = tuple(sorted(names))
    rows = [
        [Fraction(terms.get(name, 0)) for name in ordered_names]
        for _, _, terms, _ in observations
    ]
    rhs = [target for _, _, _, target in observations]
    return ordered_names, rows, rhs, observations


def _inconsistency_certificate(rows: list[list[Fraction]], rhs: list[Fraction]) -> dict:
    """Return an exact row dependence proving 0 = 1."""
    basis: dict[int, tuple[list[Fraction], Fraction, dict[int, Fraction]]] = {}
    for equation, (original_row, original_rhs) in enumerate(zip(rows, rhs)):
        row = original_row[:]
        value = original_rhs
        combination = {equation: Fraction(1)}
        for pivot in sorted(basis):
            if not row[pivot]:
                continue
            basis_row, basis_rhs, basis_combination = basis[pivot]
            factor = row[pivot]
            row = [left - factor * right for left, right in zip(row, basis_row)]
            value -= factor * basis_rhs
            for index, coefficient in basis_combination.items():
                combination[index] = combination.get(index, Fraction(0)) - factor * coefficient
                if not combination[index]:
                    del combination[index]
        pivot = next((index for index, coefficient in enumerate(row) if coefficient), None)
        if pivot is None:
            if not value:
                continue
            scale = value
            normalized = {
                index: coefficient / scale for index, coefficient in combination.items()
            }
            if any(
                sum((normalized.get(index, Fraction(0)) * rows[index][column] for index in normalized), Fraction(0))
                for column in range(len(row))
            ):
                raise AssertionError("invalid inconsistency certificate left side")
            if sum((normalized[index] * rhs[index] for index in normalized), Fraction(0)) != 1:
                raise AssertionError("invalid inconsistency certificate right side")
            return {
                "relation": "the listed equation multipliers sum to 0 = 1",
                "equation_multipliers": [
                    [index, *_fraction_json(coefficient)]
                    for index, coefficient in sorted(normalized.items())
                ],
                "left_side": [0, 1],
                "right_side": [1, 1],
            }
        scale = row[pivot]
        basis[pivot] = (
            [coefficient / scale for coefficient in row],
            value / scale,
            {index: coefficient / scale for index, coefficient in combination.items()},
        )
    raise AssertionError("system was reported inconsistent but no dependence was found")


def _affine_rref(
    rows: list[list[Fraction]], rhs: list[Fraction]
) -> tuple[
    list[Fraction],
    list[tuple[Fraction, dict[int, Fraction]]],
    list[int],
    dict[int, tuple[list[Fraction], Fraction, dict[int, Fraction]]],
    dict,
]:
    """Return a particular solution and coefficient-wise nullspace coordinates."""
    matrix = [row[:] + [value] for row, value in zip(rows, rhs)]
    provenance = [{index: Fraction(1)} for index in range(len(rows))]
    columns = len(rows[0])
    pivot_row = 0
    pivots = []
    for column in range(columns):
        pivot = next((r for r in range(pivot_row, len(matrix)) if matrix[r][column]), None)
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        provenance[pivot_row], provenance[pivot] = provenance[pivot], provenance[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        provenance[pivot_row] = {
            index: value / scale for index, value in provenance[pivot_row].items()
        }
        for row in range(len(matrix)):
            if row == pivot_row or not matrix[row][column]:
                continue
            scale = matrix[row][column]
            matrix[row] = [
                left - scale * right
                for left, right in zip(matrix[row], matrix[pivot_row])
            ]
            for index, value in provenance[pivot_row].items():
                provenance[row][index] = provenance[row].get(index, Fraction(0)) - scale * value
                if not provenance[row][index]:
                    del provenance[row][index]
        pivots.append(column)
        pivot_row += 1
    if any(not any(row[:columns]) and row[columns] for row in matrix):
        raise ValueError("cannot parameterize an inconsistent equality system")
    free_columns = [column for column in range(columns) if column not in set(pivots)]
    free_indexes = {column: index for index, column in enumerate(free_columns)}
    pivot_rows = {column: row for row, column in enumerate(pivots)}
    particular = [Fraction(0) for _ in range(columns)]
    forms: list[tuple[Fraction, dict[int, Fraction]]] = []
    for column in range(columns):
        if column in free_indexes:
            forms.append((Fraction(0), {free_indexes[column]: Fraction(1)}))
            continue
        row = pivot_rows[column]
        particular[column] = matrix[row][columns]
        forms.append(
            (
                matrix[row][columns],
                {
                    free_indexes[free]: -matrix[row][free]
                    for free in free_columns
                    if matrix[row][free]
                },
            )
        )
    row_basis = {
        column: (matrix[row][:columns], matrix[row][columns], provenance[row])
        for row, column in enumerate(pivots)
    }
    return particular, forms, free_columns, row_basis, {
        "rank": len(pivots),
        "variables": columns,
        "nullity": len(free_columns),
        "nullspace_basis_vectors": len(free_columns),
        "basis_construction": "one exact RREF nullspace vector per free column",
        "particular_and_basis_arithmetic": "fractions.Fraction",
    }


def _state_affine(
    terms: Counter[str], indexes: dict[str, int], forms: list[tuple[Fraction, dict[int, Fraction]]]
) -> tuple[Fraction, dict[int, Fraction]]:
    constant = Fraction(0)
    vector: dict[int, Fraction] = {}
    for name, count in terms.items():
        index = indexes.get(name)
        if index is None:
            continue
        term_constant, term_vector = forms[index]
        constant += count * term_constant
        for free, coefficient in term_vector.items():
            vector[free] = vector.get(free, Fraction(0)) + count * coefficient
            if not vector[free]:
                del vector[free]
    return constant, vector


def _difference_affine(
    constant: Fraction,
    positive: tuple[Fraction, dict[int, Fraction]],
    negative: tuple[Fraction, dict[int, Fraction]] | None = None,
) -> tuple[Fraction, tuple[tuple[int, Fraction], ...]]:
    result = dict(positive[1])
    value = constant + positive[0]
    if negative is not None:
        value -= negative[0]
        for free, coefficient in negative[1].items():
            result[free] = result.get(free, Fraction(0)) - coefficient
            if not result[free]:
                del result[free]
    return value, tuple(sorted(result.items()))


def _transformed_constraints(
    corridors: dict[int, EqualityCorridor],
    stage: str,
    names: tuple[str, ...],
    forms: list[tuple[Fraction, dict[int, Fraction]]],
) -> tuple[list[tuple[Fraction, tuple[tuple[int, Fraction], ...]]], dict, dict | None]:
    indexes = {name: index for index, name in enumerate(names)}
    unique = set()
    obstruction = None
    edge_constraints = terminal_constraints = 0
    for n in WIDTHS:
        corridor = corridors[n]
        state_forms = {}
        for row, layer in enumerate(corridor.layers):
            for key, state in layer.items():
                if key not in corridor.backward[row]:
                    continue
                try:
                    terms = structural_terms(state, stage)
                except ValueError:
                    state_forms[key] = None
                else:
                    state_forms[key] = _state_affine(terms, indexes, forms)
        for row in range(n):
            for incoming_key, incoming in corridor.layers[row].items():
                for mask in range(1 << n):
                    outgoing = advance_row(incoming, mask)
                    if outgoing is None:
                        continue
                    outgoing_key = structural_key(outgoing)
                    if outgoing_key not in corridor.backward[row + 1]:
                        continue
                    source = state_forms[incoming_key]
                    target = state_forms[outgoing_key]
                    if source is None or target is None:
                        continue
                    unique.add(
                        transformed := _difference_affine(
                            Fraction(_edge_weight(incoming, mask, outgoing)), target, source
                        )
                    )
                    if transformed[0] < 0 and not transformed[1] and obstruction is None:
                        source_terms = structural_terms(incoming, stage)
                        target_terms = structural_terms(outgoing, stage)
                        normal = Counter(target_terms)
                        normal.subtract(source_terms)
                        obstruction = {
                            "kind": "edge",
                            "width": n,
                            "offset": Fraction(_edge_weight(incoming, mask, outgoing)),
                            "normal": {
                                indexes[name]: Fraction(value)
                                for name, value in normal.items()
                                if value and name in indexes
                            },
                            "incoming": _state_json(incoming),
                            "mask": f"0b{mask:0{n}b}",
                            "outgoing": _state_json(outgoing),
                        }
                    edge_constraints += 1
        for key in corridor.layers[n]:
            form = state_forms[key]
            if form is None:
                raise AssertionError("terminal state is outside the silent-hull language")
            transformed = _difference_affine(
                Fraction(-corridor.minimum_weight),
                (-form[0], {i: -v for i, v in form[1].items()}),
            )
            unique.add(transformed)
            if transformed[0] < 0 and not transformed[1] and obstruction is None:
                state = corridor.layers[n][key]
                terms = structural_terms(state, stage)
                obstruction = {
                    "kind": "terminal",
                    "width": n,
                    "offset": Fraction(-corridor.minimum_weight),
                    "normal": {
                        indexes[name]: Fraction(-value)
                        for name, value in terms.items()
                        if value and name in indexes
                    },
                    "terminal": _state_json(state),
                }
            terminal_constraints += 1
    return sorted(unique, key=repr), {
        "codec_supported_edge_constraints": edge_constraints,
        "terminal_constraints": terminal_constraints,
        "unique_transformed_halfspaces": len(unique),
    }, obstruction


def _farkas_certificate(
    obstruction: dict,
    names: tuple[str, ...],
    rows: list[list[Fraction]],
    rhs: list[Fraction],
    observations,
    row_basis: dict[int, tuple[list[Fraction], Fraction, dict[int, Fraction]]],
) -> dict:
    """Express one violated inequality normal in the equality row space exactly."""
    normal = obstruction["normal"]
    residual = {index: value for index, value in normal.items() if value}
    multipliers: dict[int, Fraction] = {}
    for pivot in sorted(row_basis):
        factor = residual.get(pivot, Fraction(0))
        if not factor:
            continue
        basis_row, _, provenance = row_basis[pivot]
        for column, value in enumerate(basis_row):
            if not value:
                continue
            residual[column] = residual.get(column, Fraction(0)) - factor * value
            if not residual[column]:
                del residual[column]
        for equation, value in provenance.items():
            multipliers[equation] = multipliers.get(equation, Fraction(0)) + factor * value
            if not multipliers[equation]:
                del multipliers[equation]
    if residual:
        raise AssertionError("zero-normal transformed constraint is not in the equality row space")
    reconstructed = [
        sum((multipliers.get(equation, Fraction(0)) * rows[equation][column] for equation in multipliers), Fraction(0))
        for column in range(len(names))
    ]
    expected = [normal.get(column, Fraction(0)) for column in range(len(names))]
    if reconstructed != expected:
        raise AssertionError("Farkas normal reconstruction failed")
    contradiction = obstruction["offset"] + sum(
        (value * rhs[equation] for equation, value in multipliers.items()), Fraction(0)
    )
    if contradiction >= 0:
        raise AssertionError("Farkas combination does not contradict the inequality")
    equations = []
    for equation, multiplier in sorted(multipliers.items()):
        n, state, _, target = observations[equation]
        equations.append(
            {
                "index": equation,
                "multiplier": _fraction_json(multiplier),
                "width": n,
                "state": _state_json(state),
                "required_potential": _fraction_json(target),
            }
        )
    source = {
        key: value
        for key, value in obstruction.items()
        if key not in ("normal", "offset")
    }
    return {
        "claim": (
            "every adjacent-bigram coefficient vector satisfying all listed tight "
            "equality-corridor state anchors violates this inequality"
        ),
        "constraint": {
            **source,
            "offset": _fraction_json(obstruction["offset"]),
            "normal": [
                [names[index], *_fraction_json(value)]
                for index, value in sorted(normal.items())
            ],
            "required_relation": "offset + normal dot coefficients >= 0",
        },
        "equality_combination": equations,
        "verification": {
            "coefficient_normal_reconstructed_exactly": True,
            "remaining_scalar": _fraction_json(contradiction),
            "contradiction": f"{contradiction} >= 0",
            "arithmetic": "fractions.Fraction",
        },
    }


def _projection_candidate(
    constraints: list[tuple[Fraction, tuple[tuple[int, Fraction], ...]]], nullity: int
) -> tuple[list[Fraction], dict]:
    floating_constraints = [
        (float(constant), tuple((index, float(coefficient)) for index, coefficient in vector))
        for constant, vector in constraints
    ]
    values = [0.0] * nullity
    updates = 0
    passes = 0
    telemetry = []
    zero_vector_conflict = None
    converged = False
    for pass_number in range(1, PROJECTION_PASS_BOUND + 1):
        passes = pass_number
        changed = False
        pass_updates = 0
        minimum_encountered_slack = 0.0
        maximum_projection_step = 0.0
        for constraint_index, (constant, vector) in enumerate(floating_constraints):
            slack = constant + sum(coefficient * values[index] for index, coefficient in vector)
            minimum_encountered_slack = min(minimum_encountered_slack, slack)
            if slack >= -1e-10:
                continue
            norm = sum(coefficient**2 for _, coefficient in vector)
            if not norm:
                zero_vector_conflict = _fraction_json(constraints[constraint_index][0])
                break
            step = -slack / norm
            for index, coefficient in vector:
                values[index] += step * coefficient
            updates += 1
            pass_updates += 1
            maximum_projection_step = max(maximum_projection_step, step)
            changed = True
            if updates >= PROJECTION_UPDATE_BOUND:
                break
        telemetry.append(
            {
                "pass": pass_number,
                "updates": pass_updates,
                "cumulative_updates": updates,
                "minimum_encountered_slack": minimum_encountered_slack,
                "maximum_projection_step": maximum_projection_step,
            }
        )
        if zero_vector_conflict is not None or updates >= PROJECTION_UPDATE_BOUND:
            break
        if not changed:
            converged = True
            break

    attempts = []
    candidates = []
    for denominator_limit in RATIONAL_DENOMINATOR_LIMITS:
        rational = [Fraction(value).limit_denominator(denominator_limit) for value in values]
        slacks = [
            constant
            + sum((coefficient * rational[index] for index, coefficient in vector), Fraction(0))
            for constant, vector in constraints
        ]
        violations = sum(slack < 0 for slack in slacks)
        minimum = min(slacks)
        attempts.append(
            {
                "denominator_limit": denominator_limit,
                "exact_violations": violations,
                "exact_minimum_slack": _fraction_json(minimum),
            }
        )
        candidates.append((violations, -minimum, denominator_limit, rational))
        if not violations:
            break
    _, _, selected_limit, selected = min(candidates, key=lambda item: item[:3])
    return selected, {
        "method": "deterministic cyclic Euclidean halfspace projection",
        "ordering": "fixed lexicographic transformed-halfspace order",
        "solver_or_lp_library_used": False,
        "pass_bound": PROJECTION_PASS_BOUND,
        "update_bound": PROJECTION_UPDATE_BOUND,
        "passes_completed": passes,
        "projection_updates": updates,
        "floating_projection_converged": converged,
        "pass_telemetry": telemetry,
        "rationalization_attempts": attempts,
        "selected_rational_denominator_limit": selected_limit,
        "exact_feasible_rationalization_found": not min(item[0] for item in candidates),
        "zero_vector_exact_conflict": zero_vector_conflict,
    }


def _lift_candidate(
    forms: list[tuple[Fraction, dict[int, Fraction]]], free_values: list[Fraction]
) -> list[Fraction]:
    return [
        constant
        + sum((coefficient * free_values[index] for index, coefficient in vector.items()), Fraction(0))
        for constant, vector in forms
    ]


def _write_highs_lp(
    path: Path,
    constraints: list[tuple[Fraction, tuple[tuple[int, Fraction], ...]]],
    nullity: int,
) -> dict:
    nonzeros = 0
    rows = 0
    with path.open("w") as output:
        output.write("Minimize\n obj: 0\nSubject To\n")
        for constant, vector in constraints:
            if not vector:
                if constant < 0:
                    raise AssertionError("negative zero-normal row reached HiGHS export")
                continue
            scale = max(abs(float(constant)), *(abs(float(value)) for _, value in vector), 1.0)
            pieces = []
            for index, value in vector:
                coefficient = float(value) / scale
                pieces.append(f"{coefficient:+.17g} x{index}")
            rhs = -float(constant) / scale
            output.write(f" c{rows}: {' '.join(pieces)} >= {rhs:.17g}\n")
            nonzeros += len(vector)
            rows += 1
        output.write("Bounds\n")
        for index in range(nullity):
            output.write(f" x{index} free\n")
        output.write("End\n")
    return {"exported_rows": rows, "exported_nonzeros": nonzeros, "free_variables": nullity}


def _read_highs_solution(path: Path, nullity: int) -> list[float]:
    values = [0.0] * nullity
    in_columns = False
    for line in path.read_text().splitlines():
        if line.startswith("# Columns"):
            in_columns = True
            continue
        if line.startswith("# Rows"):
            break
        if not in_columns or not line or line.startswith("#"):
            continue
        name, value = line.split()
        if name.startswith("x"):
            values[int(name[1:])] = float(value)
    return values


def _read_highs_dual_row_support(path: Path, threshold: float) -> list[int]:
    in_dual = False
    in_rows = False
    support = []
    for line in path.read_text().splitlines():
        if line == "# Dual solution values":
            in_dual = True
            continue
        if not in_dual:
            continue
        if line.startswith("# Rows"):
            in_rows = True
            continue
        if in_rows and line.startswith("# Basis"):
            break
        if not in_rows or not line or line.startswith("#"):
            continue
        name, value = line.split()
        if name.startswith("c") and float(value) > threshold:
            support.append(int(name[1:]))
    return support


def _exact_farkas_from_dual_support(
    constraints: list[tuple[Fraction, tuple[tuple[int, Fraction], ...]]],
    dual_solution: Path,
    nullity: int,
) -> dict | None:
    exported = [(constant, dict(vector)) for constant, vector in constraints if vector]
    attempts = []
    for threshold in (1e-7, 1e-9, 1e-11, 0.0, -1.0):
        support = _read_highs_dual_row_support(dual_solution, threshold)
        if not support or max(support) >= len(exported):
            attempts.append({"threshold": threshold, "support": len(support), "result": "invalid-row-index"})
            continue
        rows = [
            [exported[row][1].get(column, Fraction(0)) for row in support]
            for column in range(nullity)
        ]
        rows.append([exported[row][0] for row in support])
        rhs = [Fraction(0) for _ in range(nullity)] + [Fraction(-1)]
        multipliers, diagnostics = _rref_solve(rows, rhs)
        if multipliers is None:
            attempts.append(
                {"threshold": threshold, "support": len(support), "result": "exact-system-inconsistent", **diagnostics}
            )
            continue
        negative = sum(value < 0 for value in multipliers)
        cancellation = [
            sum(
                (multipliers[index] * exported[row][1].get(column, Fraction(0)) for index, row in enumerate(support)),
                Fraction(0),
            )
            for column in range(nullity)
        ]
        constant = sum(
            (multipliers[index] * exported[row][0] for index, row in enumerate(support)),
            Fraction(0),
        )
        valid = not negative and not any(cancellation) and constant == -1
        attempts.append(
            {
                "threshold": threshold,
                "support": len(support),
                "result": "exact-certificate" if valid else "negative-multipliers",
                "negative_multipliers": negative,
                **diagnostics,
            }
        )
        if valid:
            return {
                "claim": "a nonnegative exact combination of finite-parser halfspaces gives -1 >= 0",
                "source": "HiGHS presolve-off dual support, recomputed exactly rather than trusting floating values",
                "dual_support_threshold": threshold,
                "multipliers": [
                    [row, *_fraction_json(value)]
                    for row, value in zip(support, multipliers)
                    if value
                ],
                "verification": {
                    "nonnegative_multipliers": True,
                    "free_variable_coefficients_cancel": True,
                    "remaining_constant": [-1, 1],
                    "contradiction": "-1 >= 0",
                    "arithmetic": "fractions.Fraction",
                },
                "support_attempts": attempts,
            }
    return {"status": "no-exact-certificate", "support_attempts": attempts}


def _read_highs_lp_rows(path: Path) -> tuple[list[str], list[tuple[int, str]], list[str]]:
    prefix = []
    rows = []
    suffix = []
    section = "prefix"
    for line in path.read_text().splitlines(keepends=True):
        stripped = line.strip()
        if stripped in ("st", "Subject To"):
            prefix.append(line)
            section = "rows"
            continue
        if stripped in ("bounds", "Bounds"):
            suffix.append(line)
            section = "suffix"
            continue
        if section == "prefix":
            prefix.append(line)
        elif section == "rows":
            name = stripped.split(":", 1)[0]
            if name.startswith("c"):
                rows.append((int(name[1:]), line))
        else:
            suffix.append(line)
    return prefix, rows, suffix


def _write_highs_lp_row_subset(
    path: Path, prefix: list[str], rows: list[tuple[int, str]], suffix: list[str]
) -> None:
    path.write_text("".join((*prefix, *(line for _, line in rows), *suffix)))


def _highs_reports_infeasible(model: Path, time_limit: int = 120) -> bool:
    completed = subprocess.run(
        [str(HIGHS), "--presolve", "on", "--time_limit", str(time_limit), str(model)],
        check=False,
        capture_output=True,
        text=True,
        cwd=HIGHS_WORK,
        timeout=time_limit + 30,
    )
    return "Model status        : Infeasible" in completed.stdout


def _deterministic_iis_deletion_filter(source: Path, output: Path) -> dict:
    prefix, rows, suffix = _read_highs_lp_rows(source)
    work = HIGHS_WORK / "grid-graphs-finite-parser-deletion-work.lp"
    solves = 0
    block = max(1, len(rows) // 16)
    while True:
        changed = False
        start = 0
        while start < len(rows):
            candidate = rows[:start] + rows[start + block :]
            if not candidate:
                start += block
                continue
            _write_highs_lp_row_subset(work, prefix, candidate, suffix)
            solves += 1
            if _highs_reports_infeasible(work):
                rows = candidate
                changed = True
            else:
                start += block
        if block == 1:
            if not changed:
                break
        else:
            block = max(1, block // 2)
    _write_highs_lp_row_subset(output, prefix, rows, suffix)
    return {"input_rows": len(_read_highs_lp_rows(source)[1]), "output_rows": len(rows), "highs_solves": solves}


def _highs_nonnegative_ray_attempt(
    constraints: list[tuple[Fraction, tuple[tuple[int, Fraction], ...]]],
    iis_model: Path | None,
    nullity: int,
) -> dict:
    exported = [(constant, dict(vector)) for constant, vector in constraints if vector]
    row_ids = (
        list(range(len(exported)))
        if iis_model is None
        else [row for row, _ in _read_highs_lp_rows(iis_model)[1]]
    )
    model = HIGHS_WORK / "grid-graphs-finite-parser-farkas.lp"
    solution = HIGHS_WORK / "grid-graphs-finite-parser-farkas.sol"
    with model.open("w") as output:
        output.write("Minimize\n obj: 0\nSubject To\n")
        for column in range(nullity):
            pieces = [
                f"{float(exported[row][1].get(column, Fraction(0))):+.17g} l{row}"
                for row in row_ids
                if exported[row][1].get(column, Fraction(0))
            ]
            if pieces:
                output.write(f" e{column}: {' '.join(pieces)} = 0\n")
        pieces = [f"{float(exported[row][0]):+.17g} l{row}" for row in row_ids]
        output.write(f" normalization: {' '.join(pieces)} = -1\nEnd\n")
    solution.unlink(missing_ok=True)
    command = [
        str(HIGHS),
        "--solver",
        "simplex",
        "--presolve",
        "on",
        "--solution_file",
        str(solution),
        str(model),
    ]
    completed = subprocess.run(
        command, check=False, capture_output=True, text=True, cwd=HIGHS_WORK, timeout=600
    )
    if "Model status        : Optimal" not in completed.stdout or not solution.exists():
        return {"status": "auxiliary-ray-lp-did-not-solve", "command": command}
    floating = {}
    in_columns = False
    for line in solution.read_text().splitlines():
        if line.startswith("# Columns"):
            in_columns = True
            continue
        if line.startswith("# Rows"):
            break
        if not in_columns or not line or line.startswith("#"):
            continue
        name, value = line.split()
        if name.startswith("l") and float(value) > 1e-9:
            floating[int(name[1:])] = float(value)
    support = sorted(floating)
    rows = [
        [exported[row][1].get(column, Fraction(0)) for row in support]
        for column in range(nullity)
    ]
    rows.append([exported[row][0] for row in support])
    multipliers, diagnostics = _rref_solve(
        rows, [Fraction(0) for _ in range(nullity)] + [Fraction(-1)]
    )
    if multipliers is None:
        return {
            "status": "floating-support-not-exactly-dependent",
            "command": command,
            "floating_support": len(support),
            **diagnostics,
        }
    negative = sum(value < 0 for value in multipliers)
    valid = not negative
    exact_multipliers = [
        (row, value) for row, value in zip(support, multipliers) if value
    ]
    return {
        "status": "exact-certificate" if valid else "exact-support-solve-has-negative-multipliers",
        "method": "HiGHS auxiliary nonnegative-ray LP followed by exact support elimination",
        "command": command,
        "floating_support": len(support),
        "negative_multipliers": negative,
        "multipliers": (
            [[row, *_fraction_json(value)] for row, value in exact_multipliers]
            if valid else []
        ),
        "inequalities": (
            [
                {
                    "row": row,
                    "multiplier": _fraction_json(value),
                    "constant": _fraction_json(exported[row][0]),
                    "normal": [
                        [index, *_fraction_json(coefficient)]
                        for index, coefficient in sorted(exported[row][1].items())
                    ],
                }
                for row, value in exact_multipliers
            ]
            if valid else []
        ),
        "verification": (
            {
                "nonnegative_multipliers": True,
                "free_variable_coefficients_cancel": True,
                "remaining_constant": [-1, 1],
                "contradiction": "-1 >= 0",
                "arithmetic": "fractions.Fraction",
            }
            if valid
            else None
        ),
        **diagnostics,
    }


def _highs_candidate(
    constraints: list[tuple[Fraction, tuple[tuple[int, Fraction], ...]]],
    nullity: int,
) -> tuple[list[Fraction] | None, dict]:
    model = HIGHS_WORK / "grid-graphs-finite-parser-halfspaces.lp"
    solution_file = HIGHS_WORK / "grid-graphs-finite-parser-halfspaces.sol"
    options_file = HIGHS_WORK / "grid-graphs-finite-parser-highs.options"
    export = _write_highs_lp(model, constraints, nullity)
    runs = []
    selected = None
    for tolerance in (1e-9, 1e-10):
        options_file.write_text(
            "solver = simplex\n"
            "presolve = on\n"
            "parallel = off\n"
            "threads = 1\n"
            f"primal_feasibility_tolerance = {tolerance:.1e}\n"
            f"dual_feasibility_tolerance = {tolerance:.1e}\n"
        )
        solution_file.unlink(missing_ok=True)
        command = [
            str(HIGHS),
            "--options_file",
            str(options_file),
            "--solution_file",
            str(solution_file),
            str(model),
        ]
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            cwd=HIGHS_WORK,
            timeout=3600,
        )
        stdout = completed.stdout
        if "Model status        : Optimal" in stdout:
            status = "optimal"
        elif "Model status        : Infeasible" in stdout:
            status = "infeasible-diagnostic-only"
        else:
            status = "other"
        run = {
            "command": command,
            "returncode": completed.returncode,
            "primal_and_dual_feasibility_tolerance": tolerance,
            "solver_status": status,
            "rationalization_attempts": [],
        }
        if status == "optimal" and solution_file.exists():
            floating = _read_highs_solution(solution_file, nullity)
            for limit in HIGHS_RATIONAL_DENOMINATOR_LIMITS:
                rational = [Fraction(value).limit_denominator(limit) for value in floating]
                slacks = [
                    constant
                    + sum(
                        (coefficient * rational[index] for index, coefficient in vector),
                        Fraction(0),
                    )
                    for constant, vector in constraints
                ]
                violations = sum(slack < 0 for slack in slacks)
                run["rationalization_attempts"].append(
                    {
                        "denominator_limit": limit,
                        "exact_violations": violations,
                        "exact_minimum_slack": _fraction_json(min(slacks)),
                    }
                )
                if not violations:
                    selected = rational
                    run["selected_denominator_limit"] = limit
                    break
        runs.append(run)
        if selected is not None or status != "optimal":
            break
    return selected, {
        "binary": str(HIGHS),
        "version": "1.15.1",
        "lp": str(model),
        "solution_file": str(solution_file),
        "options_file": str(options_file),
        "objective": "constant zero feasibility objective",
        "gauge": "none; all 608 RREF free variables are explicitly free",
        "uniform_margin_not_used_reason": (
            "tight equality-corridor edges force zero-slack halfspaces, so the maximum uniform margin is zero"
        ),
        **export,
        "runs": runs,
        "exact_feasible_rational_candidate_found": selected is not None,
        "infeasible_status_policy": "diagnostic only without an exactly verified Farkas certificate",
    }


def _fit_stage(corridors: dict[int, EqualityCorridor], stage: str):
    names, rows, rhs, observations = _training(corridors, stage)
    solution, diagnostics = _rref_solve(rows, rhs)
    if solution is None:
        by_terms: dict[tuple, tuple[int, FrontierState, Fraction]] = {}
        counterexamples = []
        for n, state, terms, target in observations:
            signature = tuple(sorted(terms.items()))
            previous = by_terms.get(signature)
            if previous is not None and previous[2] != target:
                counterexamples.append(
                    {
                        "shared_structural_terms": [[name, count] for name, count in signature],
                        "first": {
                            "width": previous[0],
                            "state": _state_json(previous[1]),
                            "required_potential": _fraction_json(previous[2]),
                        },
                        "second": {
                            "width": n,
                            "state": _state_json(state),
                            "required_potential": _fraction_json(target),
                        },
                    }
                )
                if len(counterexamples) == MAX_COUNTEREXAMPLES:
                    break
            else:
                by_terms[signature] = (n, state, target)
        certificate = _inconsistency_certificate(rows, rhs)
        certificate["equations"] = [
            {
                "index": index,
                "multiplier": [numerator, denominator],
                "width": observations[index][0],
                "state": _state_json(observations[index][1]),
                "required_potential": _fraction_json(observations[index][3]),
            }
            for index, numerator, denominator in certificate["equation_multipliers"]
        ]
        return names, None, observations, {
            **diagnostics,
            "free_variables": None,
            "exact_equalities_satisfied": False,
            "equal-feature_different-target_counterexamples": counterexamples,
            "exact_linear_inconsistency_certificate": certificate,
        }
    residuals = [
        sum((coefficient * value for coefficient, value in zip(solution, row)), Fraction(0)) - target
        for row, target in zip(rows, rhs)
    ]
    if any(residuals):
        raise AssertionError("RREF solution did not reproduce its exact training system")
    return names, solution, observations, {
        **diagnostics,
        "free_variables": len(names) - diagnostics["rank"],
        "free_variable_policy": "all nonpivot and all training-unseen atom weights are zero",
        "exact_equalities_satisfied": True,
    }


def synthesize(corridors: dict[int, EqualityCorridor]):
    """Fit every declared structural parser refinement exactly."""
    transcript = []
    fits = []
    for stage in STAGES:
        names, solution, observations, diagnostics = _fit_stage(corridors, stage)
        transcript.append(
            {
                "stage": stage,
                "terms_observed_in_training": len(names),
                "target": "Psi(state) = -forward_distance(state)",
                "states": len(observations),
                **diagnostics,
            }
        )
        fits.append((stage, names, solution, observations))
    return fits, transcript


def _unsupported_witness(state: FrontierState) -> dict:
    decision = classify_silent_hull_frontier(state)
    return {
        "state": _state_json(state),
        "maximum_face_cut_width": decision.maximum_face_cut_width,
        "reason": decision.reason,
    }


def evaluate_width(
    corridor: EqualityCorridor, coefficients: dict[str, Fraction], stage: str
) -> dict:
    term_cache: dict[tuple, Counter[str] | None] = {}
    unsupported_states = []
    completable_states = 0
    for row, layer in enumerate(corridor.layers):
        for key, state in layer.items():
            if key not in corridor.backward[row]:
                continue
            completable_states += 1
            try:
                term_cache[key] = structural_terms(state, stage)
            except ValueError:
                term_cache[key] = None
                if len(unsupported_states) < MAX_COUNTEREXAMPLES:
                    unsupported_states.append(_unsupported_witness(state))

    inspected = evaluable = valid = violating = 0
    minimum_slack: Fraction | None = None
    counterexamples = []
    unsupported_edges = []
    for row in range(corridor.n):
        for incoming_key, incoming in corridor.layers[row].items():
            for mask in range(1 << corridor.n):
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                outgoing_key = structural_key(outgoing)
                if outgoing_key not in corridor.backward[row + 1]:
                    continue
                inspected += 1
                incoming_terms = term_cache[incoming_key]
                outgoing_terms = term_cache[outgoing_key]
                if incoming_terms is None or outgoing_terms is None:
                    if len(unsupported_edges) < MAX_COUNTEREXAMPLES:
                        unsupported_edges.append(
                            {
                                "incoming": _state_json(incoming),
                                "mask": f"0b{mask:0{corridor.n}b}",
                                "outgoing": _state_json(outgoing),
                                "unsupported_endpoint": (
                                    "both" if incoming_terms is None and outgoing_terms is None
                                    else "incoming" if incoming_terms is None else "outgoing"
                                ),
                            }
                        )
                    continue
                evaluable += 1
                weight = _edge_weight(incoming, mask, outgoing)
                incoming_value = _potential(incoming_terms, coefficients)
                outgoing_value = _potential(outgoing_terms, coefficients)
                slack = Fraction(weight) + outgoing_value - incoming_value
                minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
                if slack >= 0:
                    valid += 1
                else:
                    violating += 1
                    witness = {
                        "incoming": _state_json(incoming),
                        "mask": f"0b{mask:0{corridor.n}b}",
                        "outgoing": _state_json(outgoing),
                        "weight": weight,
                        "incoming_potential": _fraction_json(incoming_value),
                        "outgoing_potential": _fraction_json(outgoing_value),
                        "slack": _fraction_json(slack),
                    }
                    counterexamples.append(witness)
                    counterexamples.sort(key=lambda item: (Fraction(*item["slack"]), repr(item)))
                    del counterexamples[MAX_COUNTEREXAMPLES:]

    terminal_values = Counter()
    terminal_violations = []
    violating_terminals = 0
    for key, state in corridor.layers[corridor.n].items():
        terms = term_cache[key]
        if terms is None:
            raise AssertionError("terminal state is outside the silent-hull language")
        value = _potential(terms, coefficients)
        terminal_values[str(value)] += 1
        if value > -corridor.minimum_weight:
            violating_terminals += 1
            if len(terminal_violations) < MAX_COUNTEREXAMPLES:
                terminal_violations.append(
                    {"state": _state_json(state), "potential": _fraction_json(value)}
                )

    return {
        "completable_states": completable_states,
        "representable_states": completable_states - sum(value is None for value in term_cache.values()),
        "unsupported_state_counterexamples": unsupported_states,
        "completable_edges_inspected": inspected,
        "evaluable_edges": evaluable,
        "unsupported_edges": inspected - evaluable,
        "unsupported_edge_counterexamples": unsupported_edges,
        "inequality_convention": "weight + Psi(out) - Psi(in) >= 0",
        "valid_evaluable_edges": valid,
        "violating_evaluable_edges": violating,
        "minimum_evaluable_slack": None if minimum_slack is None else _fraction_json(minimum_slack),
        "inequality_counterexamples": counterexamples,
        "terminal_states": len(corridor.layers[corridor.n]),
        "terminal_value_histogram": dict(sorted(terminal_values.items())),
        "terminal_requirement": f"Psi(terminal) <= {-corridor.minimum_weight}",
        "violating_terminal_states": violating_terminals,
        "terminal_violations": terminal_violations,
    }


def _analyze_feasible_stage(
    corridors: dict[int, EqualityCorridor],
    stage: str,
    names: tuple[str, ...],
    solution: list[Fraction],
    observations,
) -> dict:
    rows, rhs, _ = _training(corridors, stage)[1:]
    particular, forms, free_columns, row_basis, affine_diagnostics = _affine_rref(rows, rhs)
    if particular != solution:
        raise AssertionError("affine RREF particular solution changed the pivot convention")
    constraints, constraint_diagnostics, obstruction = _transformed_constraints(
        corridors, stage, names, forms
    )
    exact_certificate = (
        None
        if obstruction is None
        else _farkas_certificate(obstruction, names, rows, rhs, observations, row_basis)
    )
    base = {
        "stage": stage,
        "affine_solution_space": affine_diagnostics,
        **constraint_diagnostics,
        "exact_equalities_rechecked": len(rows),
        "exact_equality_violations": 0,
        "exact_infeasibility_certificate": exact_certificate,
    }
    if exact_certificate is not None:
        result = {
            **base,
            "status": "exactly-infeasible-under-tight-equality-anchors",
            "projection_search": {
                "performed": False,
                "reason": "an exact zero-normal transformed contradiction was found first",
            },
            "evaluation": None,
        }
        if stage == "finite-parser":
            result["suggested_additional_structural_context"] = {
                "kind": "one-step incoming-transition parser context",
                "fields": [
                    "source parser boundary state",
                    "current row action cap bits and packet words",
                    "target parser boundary state",
                ],
                "reason": (
                    "The obstructing edge has slack fixed by the tight state anchors, so another "
                    "state-word refinement cannot change it; the smallest noncumulative escape is "
                    "to distinguish the local predecessor/action occurrence of the frontier."
                ),
                "cumulative_features_added": False,
            }
        return result

    highs_values = None
    highs_search = None
    if stage == "finite-parser":
        highs_values, highs_search = _highs_candidate(constraints, len(free_columns))
        if (
            highs_values is None
            and highs_search["runs"]
            and highs_search["runs"][-1]["solver_status"] == "infeasible-diagnostic-only"
        ):
            ray = _highs_nonnegative_ray_attempt(constraints, None, len(free_columns))
            highs_search["exact_ray_extraction"] = ray
            if ray["status"] == "exact-certificate":
                return {
                    **base,
                    "status": "exactly-infeasible-under-tight-equality-anchors",
                    "highs_search": highs_search,
                    "projection_search": {
                        "performed": False,
                        "reason": "an exact nonnegative Farkas combination was reconstructed",
                    },
                    "exact_infeasibility_certificate": ray,
                    "evaluation": None,
                    "suggested_additional_structural_context": {
                        "kind": "one-step incoming-transition parser context",
                        "fields": [
                            "source parser boundary state",
                            "current row action cap bits and packet words",
                            "target parser boundary state",
                        ],
                        "reason": (
                            "The finite-parser state-only halfspaces are exactly inconsistent; "
                            "the smallest noncumulative refinement suggested is local entry context."
                        ),
                        "cumulative_features_added": False,
                    },
                }
    if highs_values is not None:
        free_values = highs_values
        search = {
            "performed": False,
            "reason": "HiGHS candidate passed exact transformed-halfspace verification",
        }
    else:
        free_values, search = _projection_candidate(constraints, len(free_columns))
    candidate = _lift_candidate(forms, free_values)
    equality_residuals = [
        sum((coefficient * value for coefficient, value in zip(candidate, row)), Fraction(0))
        - target
        for row, target in zip(rows, rhs)
    ]
    if any(equality_residuals):
        raise AssertionError("lifted affine candidate violates an exact training equality")
    transformed_slacks = [
        constant
        + sum((coefficient * free_values[index] for index, coefficient in vector), Fraction(0))
        for constant, vector in constraints
    ]
    search.update(
        {
            "exact_violating_unique_halfspaces": sum(slack < 0 for slack in transformed_slacks),
            "exact_minimum_unique_halfspace_slack": _fraction_json(min(transformed_slacks)),
            "farkas_certificate_extracted": False,
            "logical_result": "heuristic failure only",
        }
    )
    coefficients = {
        name: coefficient for name, coefficient in zip(names, candidate) if coefficient
    }
    evaluation = {
        str(n): evaluate_width(corridors[n], coefficients, stage) for n in WIDTHS
    }
    has_violations = any(
        report["violating_evaluable_edges"] or report["terminal_violations"]
        for report in evaluation.values()
    )
    highs_diagnostic_infeasible = bool(
        highs_search
        and highs_search["runs"]
        and highs_search["runs"][-1]["solver_status"] == "infeasible-diagnostic-only"
    )
    return {
        **base,
        "status": (
            "highs-infeasible-diagnostic-only-and-heuristic-search-failed"
            if has_violations and highs_diagnostic_infeasible
            else "heuristic-feasibility-search-failed"
            if has_violations
            else "bounded-rational-feasible-candidate-found"
        ),
        "highs_search": highs_search,
        "projection_search": search,
        "candidate": {
            "selection": "rationalized deterministic projection point in the exact RREF affine space",
            "nonzero_coefficients": len(coefficients),
            "coefficients": {
                name: _fraction_json(value) for name, value in sorted(coefficients.items())
            },
        },
        "evaluation": evaluation,
    }


def build_artifact() -> dict:
    corridors = {n: build_equality_corridor(n) for n in WIDTHS}
    fits, transcript = synthesize(corridors)
    stage_results = {}
    for stage, names, solution, observations in fits:
        if solution is None:
            stage_results[stage] = {
                "stage": stage,
                "status": "equality-system-inconsistent",
                "exact_inconsistency_certificate": next(
                    item["exact_linear_inconsistency_certificate"]
                    for item in transcript
                    if item["stage"] == stage
                ),
            }
        else:
            stage_results[stage] = _analyze_feasible_stage(
                corridors, stage, names, solution, observations
            )
    result = {
        "schema": SCHEMA,
        "scope": {
            "semantics": "bounded-explicitly-finite-diagnostic-only",
            "complete_equality_training_widths": list(WIDTHS),
            "complete_reachable_and_completable_evaluation_widths": list(WIDTHS),
            "larger_widths_used": False,
            "annulus_data_used": False,
            "arbitrary_width_coverage_claimed": False,
            "tight_equality_corridor_edges_assumed": True,
            "infeasibility_conclusion": "reported separately for each declared feature class",
        },
        "model": {
            "formula": "finite boundary/parser terms + weighted SilentHullAtom frontier word",
            "refinement_order": list(STAGES),
            "feature_families": [
                "cap",
                "phase",
                "left-role",
                "joint cap-phase-left-role",
                "SilentHullAtom occurrence",
                "adjacent atom/boundary bigram",
                "finite hull-active and previous-boundary-bit parser transition",
            ],
            "excluded_features": ["cumulative U", "cumulative rank", "cumulative K", "forward distance"],
            "arithmetic": "exact Fraction RREF, transformation, and verification; floating projection proposes only",
            "stages_analyzed": list(STAGES),
        },
        "exact_equality_fit_stages": transcript,
        "stage_results": stage_results,
    }
    finite_status = stage_results["finite-parser"]["status"]
    result["status"] = f"finite-parser:{finite_status}"
    result["interpretation"] = (
        "Each status is limited to its named feature class at n=5,8 under tight equality-corridor "
        "state anchors; none is an arbitrary-width theorem."
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--allow-large-lp",
        action="store_true",
        help="acknowledge the high memory cost of regenerating the finite-parser LP",
    )
    args = parser.parse_args()
    if not args.allow_large_lp:
        parser.error("regeneration requires --allow-large-lp")
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"silent-hull potential experiment matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
