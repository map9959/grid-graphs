#!/usr/bin/env python3
"""Exact width-independent accounting identity for obligation 5.

The training equations are the complete n=5 and n=8 equality corridors.  A
candidate is accepted only when its named linear formula also satisfies every
stable affine rule coefficientwise for every packet length at least seven.
The resulting formula is the negative accumulated row curvature, so it verifies
counter arithmetic but does not prove a positive lower bound.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from pathlib import Path

from analysis.transport.equality_corridor import build_equality_corridor
from analysis.residue_certificates.residue_two_affine_motif_grammar import BoundaryDefectAtom
from analysis.residue_certificates.residue_two_attachment_skeleton import linear_frontier_metric
from analysis.residue_certificates.residue_two_cap_merge_potential import cap_phase
from analysis.residue_certificates.residue_two_carrier_grammar import recognize_state
from analysis.residue_certificates.residue_two_compact_transition import ActionKey, ControlKey
from analysis.residue_certificates.residue_two_stable_counter_certificate import (
    action_u,
    boundary_values,
    frontier_debt,
    horizontal_edges,
    stable_rule_certificates,
    vertical_edges,
)
from analysis.tiles.tile_grammar import FrontierState
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_obligation5_potential.json"
SCHEMA = "grid-graphs.residue-two-obligation5-accounting.v2"


@dataclass(frozen=True, slots=True)
class Affine:
    slope: Fraction = Fraction(0)
    constant: Fraction = Fraction(0)

    def __add__(self, other: "Affine") -> "Affine":
        return Affine(self.slope + other.slope, self.constant + other.constant)

    def __sub__(self, other: "Affine") -> "Affine":
        return Affine(self.slope - other.slope, self.constant - other.constant)

    def scale(self, value: Fraction) -> "Affine":
        return Affine(value * self.slope, value * self.constant)


def _runs(mask: int) -> int:
    return (mask & ~(mask << 1)).bit_count()


def _hull_carrier(state: FrontierState) -> int:
    """Maximum non-OUT occurrence-hull width at an adjacent-face cut."""
    if len(state.partition) == 1:
        return 0
    out = state.partition[0]
    intervals = []
    for label in set(state.partition[1:]) - {out}:
        slots = [i for i, value in enumerate(state.partition[1:]) if value == label]
        intervals.append((slots[0], slots[-1]))
    return max(
        (sum(left <= cut < right for left, right in intervals)
         for cut in range(max(0, state.n - 2))),
        default=0,
    )


def state_coordinates(state: FrontierState) -> dict[str, int]:
    """Interpretable state coordinates; none identifies a concrete state."""
    metric = linear_frontier_metric(state.partition)
    out = state.partition[0]
    faces = state.partition[1:]
    active = state.n - 1 if 0 < state.row_index < state.n else 0
    phase = cap_phase(state.n, state.row_index)
    phase = phase if phase in ("top", "bottom-2", "bottom-1", "terminal") else f"bulk-{state.row_index % 3}"
    return {
        "bias": 1,
        "counter_u": state.u_cost,
        "counter_rank": 0,
        "counter_cycles": state.cycle_excess,
        "counter_row": state.row_index,
        "counter_faces": min(state.row_index, state.n - 1) * (state.n - 1),
        "row_u": state.previous_u_mask.bit_count(),
        "row_runs": _runs(state.previous_u_mask),
        "left_u": int(bool(state.previous_u_mask & 1)),
        "right_u": int(bool(state.previous_u_mask & (1 << (state.n - 1)))),
        "out_faces": sum(label == out for label in faces),
        "out_runs": sum(
            label == out and (index == 0 or faces[index - 1] != out)
            for index, label in enumerate(faces)
        ),
        "left_out": int(bool(faces) and faces[0] == out),
        "right_out": int(bool(faces) and faces[-1] == out),
        "debt": metric["attachment_debt"],
        "branch_cost": metric["branch_cost"],
        "nonout_runs": metric["attachment_debt"] + metric["branch_cost"],
        "silent_slots": metric["silent_face_slots"],
        "hull_carrier": _hull_carrier(state),
        "carrier_events": len(recognize_state(state).record.carriers),
        "active_faces": active,
        **{f"phase:{name}": int(phase == name) for name in PHASES},
    }


PHASES = ("top", "bulk-0", "bulk-1", "bulk-2", "bottom-2", "bottom-1", "terminal")
BASIC = (
    "bias", "counter_u", "counter_cycles", "counter_row", "counter_faces",
    "row_u", "row_runs",
    "out_faces", "hull_carrier",
)
REFINEMENTS = (
    ("cap_phase", tuple(f"phase:{phase}" for phase in PHASES)),
    ("out_rooted_debt", ("debt",)),
    ("root_and_run_boundaries", (
        "left_u", "right_u", "out_runs", "left_out", "right_out",
        "nonout_runs", "carrier_events",
    )),
    ("silent_and_branch", ("silent_slots", "branch_cost")),
    ("active_affine_counter", ("active_faces",)),
)


def _rref_solve(rows: list[list[Fraction]], rhs: list[Fraction]) -> tuple[list[Fraction] | None, dict]:
    """Solve an exact rectangular system, choosing zero for free variables."""
    if not rows:
        return [], {"rank": 0, "equations": 0}
    matrix = [row[:] + [value] for row, value in zip(rows, rhs)]
    columns = len(rows[0])
    pivot_row = 0
    pivots = []
    for column in range(columns):
        pivot = next((r for r in range(pivot_row, len(matrix)) if matrix[r][column]), None)
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        for row in range(len(matrix)):
            if row == pivot_row or not matrix[row][column]:
                continue
            scale = matrix[row][column]
            matrix[row] = [left - scale * right for left, right in zip(matrix[row], matrix[pivot_row])]
        pivots.append(column)
        pivot_row += 1
    conflicts = [
        index for index, row in enumerate(matrix)
        if not any(row[:columns]) and row[columns]
    ]
    diagnostics = {"rank": len(pivots), "equations": len(rows), "conflicts": conflicts[:8]}
    if conflicts:
        return None, diagnostics
    solution = [Fraction(0) for _ in range(columns)]
    for row, column in enumerate(pivots):
        solution[column] = matrix[row][columns]
    return solution, diagnostics


@cache
def _training_data() -> tuple[tuple[dict[str, int], Fraction, dict], ...]:
    observations = []
    for n in (5, 8):
        corridor = build_equality_corridor(n)
        initial = next(iter(corridor.corridor_states[0]))
        histories: list[dict[tuple, set[tuple[int, int, int]]]] = [
            {} for _ in range(n + 1)
        ]
        histories[0][initial] = {(0, 0, 0)}
        for layer in range(n):
            for edge in corridor.corridor_edges[layer]:
                for u, rank, cycles in histories[layer].get(edge.incoming, ()):
                    histories[layer + 1].setdefault(edge.outgoing, set()).add((
                        u + edge.d_u,
                        rank + edge.d_rank,
                        cycles + edge.d_cycles,
                    ))
        for layer, keys in enumerate(corridor.corridor_states):
            for key in keys:
                state = corridor.layers[layer][key]
                for u, rank, cycles in histories[layer][key]:
                    coordinates = state_coordinates(state)
                    coordinates.update(
                        counter_u=u, counter_rank=rank, counter_cycles=cycles
                    )
                    target = Fraction(-(3 * u - 2 * rank - layer))
                    observations.append((
                        coordinates,
                        target,
                        {"width": n, "layer": layer, "state": repr(key), "u": u, "rank": rank},
                    ))
    return tuple(observations)


def _training(names: tuple[str, ...]) -> tuple[list[list[Fraction]], list[Fraction], list[dict]]:
    rows: list[list[Fraction]] = []
    rhs: list[Fraction] = []
    records = []
    for coordinates, target, record in _training_data():
        rows.append([Fraction(coordinates[name]) for name in names])
        rhs.append(target)
        records.append(record)
    return rows, rhs, records


def synthesize() -> tuple[tuple[str, ...], list[Fraction], list[dict]]:
    """Counterexample-guided refinement through the declared feature groups."""
    names = BASIC
    transcript = []
    for added, terms in (("basic", ()), *REFINEMENTS):
        names = (*names, *terms)
        rows, rhs, records = _training(names)
        solution, diagnostics = _rref_solve(rows, rhs)
        entry = {"stage": added, "terms": list(names), **diagnostics, "feasible": solution is not None}
        if solution is None and diagnostics["conflicts"]:
            entry["counterexample_states"] = [records[index] for index in diagnostics["conflicts"][:2]]
        transcript.append(entry)
        if solution is not None:
            return names, solution, transcript
    raise AssertionError("declared interpretable feature refinements are insufficient")


def _point_sum(dominant, exceptions, score) -> Affine:
    left, right = boundary_values(dominant, exceptions)
    base = score(dominant)
    return Affine(Fraction(base), Fraction(sum(score(value) for value in (*left, *right)) - 6 * base))


def _control_words(control: ControlKey) -> tuple[int, tuple[tuple[str, int], ...]]:
    return control.dominant.previous_word, tuple(
        (item.endpoint, item.atom.previous_word) for item in control.exceptions
    )


def _word_runs(control: ControlKey | ActionKey) -> Affine:
    if isinstance(control, ControlKey):
        dominant, exceptions = _control_words(control)
        caps = control.previous_cap_bits
    else:
        dominant, exceptions, caps = control.dominant_packet, control.exceptions, control.cap_bits
    action = ActionKey(caps, dominant, exceptions)
    # E_h = U - runs for a binary path.
    u = action_u(action)
    horizontal = horizontal_edges(action)
    return Affine(u.packet_coefficient - horizontal.packet_coefficient, u.constant - horizontal.constant)


def _control_atom_sum(control: ControlKey, score) -> Affine:
    return _point_sum(
        control.dominant,
        tuple((item.endpoint, item.atom) for item in control.exceptions),
        score,
    )


def _out_runs(control: ControlKey) -> Affine:
    """Count OUT runs in the left-face plus packet face word."""
    exceptions = tuple((item.endpoint, item.atom) for item in control.exceptions)

    def bits(atom: BoundaryDefectAtom) -> tuple[int, int, int]:
        return tuple(int(label == 0) for label in atom.rooted_restriction) or (0, 0, 0)

    def ones(atom: BoundaryDefectAtom) -> int:
        return sum(bits(atom))

    def internal(atom: BoundaryDefectAtom) -> int:
        value = bits(atom)
        return value[0] * value[1] + value[1] * value[2]

    left, right = boundary_values(control.dominant, exceptions)
    dominant = control.dominant
    crossing = lambda first, second: bits(first)[2] * bits(second)[0]
    adjacent = Affine(
        Fraction(internal(dominant) + crossing(dominant, dominant)),
        Fraction(
            sum(internal(value) for value in (*left, *right))
            - 6 * internal(dominant)
            - 7 * crossing(dominant, dominant)
            + sum(crossing(first, second) for first, second in zip(
                (left[0], left[1], dominant, right[0], *right[1:]),
                (left[1], dominant, right[0], *right[1:]),
            ))
        ),
    )
    left_out = int(control.left_face_role == "out")
    adjacent = adjacent + Affine(constant=Fraction(left_out * bits(left[0])[0]))
    ones_value = _point_sum(dominant, exceptions, ones) + Affine(constant=Fraction(left_out))
    return ones_value - adjacent


def _control_coordinate(control: ControlKey, name: str) -> Affine:
    if name == "row_u":
        dominant, exceptions = _control_words(control)
        value = action_u(ActionKey(control.previous_cap_bits, dominant, exceptions))
        return Affine(Fraction(value.packet_coefficient), Fraction(value.constant))
    if name == "row_runs":
        return _word_runs(control)
    if name == "left_u":
        return Affine(constant=Fraction(control.previous_cap_bits[0]))
    if name == "right_u":
        return Affine(constant=Fraction(control.previous_cap_bits[1]))
    if name == "debt":
        value = frontier_debt(control)
        return Affine(Fraction(value.packet_coefficient), Fraction(value.constant))
    if name == "out_faces":
        non_out = _control_atom_sum(
            control, lambda atom: sum(bool(label) for label in atom.rooted_restriction)
        )
        active = Affine(Fraction(3), Fraction(1)) if control.cap_mode not in ("top", "closed") else Affine()
        return active - non_out
    if name == "out_runs":
        return _out_runs(control)
    if name == "left_out":
        return Affine(constant=Fraction(control.left_face_role == "out"))
    if name == "right_out":
        if control.cap_mode in ("top", "closed"):
            return Affine()
        exceptions = tuple((item.endpoint, item.atom) for item in control.exceptions)
        _, right = boundary_values(control.dominant, exceptions)
        labels = right[-1].rooted_restriction
        return Affine(constant=Fraction(bool(labels) and labels[-1] == 0))
    if name == "nonout_runs":
        debt = frontier_debt(control)
        branch = _control_atom_sum(
            control,
            lambda atom: max(len(atom.rooted_restriction) - len(set(atom.rooted_restriction)), 0),
        )
        return Affine(Fraction(debt.packet_coefficient), Fraction(debt.constant)) + branch
    if name == "carrier_events":
        return _control_atom_sum(
            control, lambda atom: sum(role.carries_in for role in atom.carrier_roles)
        )
    if name == "hull_carrier":
        carrying = any(role.carries_in or role.carries_out for role in control.dominant.carrier_roles)
        carrying |= any(
            role.carries_in or role.carries_out
            for item in control.exceptions for role in item.atom.carrier_roles
        )
        return Affine(constant=Fraction(int(carrying)))
    if name == "active_faces":
        return Affine(Fraction(3), Fraction(1)) if control.cap_mode not in ("top", "closed") else Affine()
    if name == "branch_cost":
        return _control_atom_sum(
            control,
            lambda atom: max(len(atom.rooted_restriction) - len(set(atom.rooted_restriction)), 0),
        )
    if name == "silent_slots":
        return Affine()  # Silent passage is represented by carrier roles, not charged support.
    if name.startswith("phase:"):
        requested = name.split(":", 1)[1]
        if control.cap_mode == "top":
            phase = "top"
        elif control.cap_mode == "closed":
            phase = "terminal"
        elif control.cap_mode == "bottom":
            phase = "bottom-1"
        else:
            phase = f"bulk-{control.row_phase}"
        return Affine(constant=Fraction(phase == requested))
    if name == "bias":
        return Affine(constant=Fraction(1))
    raise KeyError(name)


def verify_symbolic(names: tuple[str, ...], coefficients: list[Fraction]) -> dict:
    """Verify each stable rule as an affine inequality on all lengths >= 7."""
    slacks = []
    records = []
    for index, certificate in enumerate(stable_rule_certificates()):
        source, action, target = certificate.source, certificate.action, certificate.target
        delta = Affine()
        for name, coefficient in zip(names, coefficients):
            if not coefficient:
                continue
            if name == "counter_u":
                value = certificate.deltas.u
                term = Affine(Fraction(value.packet_coefficient), Fraction(value.constant))
            elif name == "counter_rank":
                cycles = certificate.deltas.cycles
                edges = horizontal_edges(action)
                vertical = vertical_edges(source, action)
                term = Affine(
                    Fraction(edges.packet_coefficient + vertical.packet_coefficient - cycles.packet_coefficient),
                    Fraction(edges.constant + vertical.constant - cycles.constant),
                )
            elif name == "counter_cycles":
                value = certificate.deltas.cycles
                term = Affine(Fraction(value.packet_coefficient), Fraction(value.constant))
            elif name == "counter_row":
                term = Affine(constant=Fraction(1))
            elif name == "counter_faces":
                term = (
                    Affine()
                    if source.cap_mode == "bottom"
                    else Affine(Fraction(3), Fraction(1))
                )
            else:
                term = _control_coordinate(target, name) - _control_coordinate(source, name)
            delta = delta + term.scale(coefficient)
        edges = horizontal_edges(action)
        vertical = vertical_edges(source, action)
        cycles = certificate.deltas.cycles
        weight = Affine(
            Fraction(3 * certificate.deltas.u.packet_coefficient - 2 * (edges.packet_coefficient + vertical.packet_coefficient - cycles.packet_coefficient)),
            Fraction(3 * certificate.deltas.u.constant - 2 * (edges.constant + vertical.constant - cycles.constant) - 1),
        )
        slack = weight + delta
        valid = slack.slope >= 0 and slack.slope * 7 + slack.constant >= 0
        if not valid:
            raise AssertionError(f"symbolic rule {index} fails: {slack}")
        slacks.append(slack)
        records.append({
            "rule": index,
            "slack_slope": _fraction_json(slack.slope),
            "slack_at_minimum_length": _fraction_json(slack.slope * 7 + slack.constant),
        })
    exact_identity = all(not item.slope and not item.constant for item in slacks)
    return {
        "rules": len(records),
        "minimum_packet_length": 7,
        "coefficientwise_verified": True,
        "negative_slope_rules": sum(item.slope < 0 for item in slacks),
        "minimum_slack_at_length_7": _fraction_json(min(item.slope * 7 + item.constant for item in slacks)),
        "all_rules_are_zero_slack_identities": exact_identity,
        "rule_ledger": records,
    }


def _fraction_json(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def build_artifact() -> dict:
    names, solution, transcript = synthesize()
    coefficients = {name: value for name, value in zip(names, solution) if value}
    symbolic = verify_symbolic(names, solution)
    rows, rhs, _ = _training(names)
    residuals = [sum(value * coefficient for value, coefficient in zip(row, solution)) - target for row, target in zip(rows, rhs)]
    if any(residuals):
        raise AssertionError("exact training verification failed")
    initials = [
        int(target) for _, target, record in _training_data() if record["layer"] == 0
    ]
    terminals = [
        int(target) for _, target, record in _training_data()
        if record["layer"] == record["width"]
    ]
    if set(initials) != {0} or set(terminals) != {-5}:
        raise AssertionError("baseline accounting evaluations changed")
    if not symbolic["all_rules_are_zero_slack_identities"]:
        raise AssertionError("the accounting formula ceased to be an exact identity")
    return {
        "schema": SCHEMA,
        "scope": {
            "complete_training_widths": [5, 8],
            "symbolic_stable_packet_lengths": "all integers >= 7",
            "arbitrary_packet_length_certificate": True,
            "low_curvature_language_coverage_claimed": False,
            "lower_bound_claimed": False,
        },
        "potential": {
            "kind": "exact accounting antiderivative, not a coercive potential",
            "formula": " + ".join(
                f"{value}*{name}" for name, value in coefficients.items()
            ) or "0",
            "coefficients": {name: _fraction_json(value) for name, value in coefficients.items()},
            "transition_identity": "weight + Phi(out) - Phi(in) = 0",
            "path_identity": "Phi = -3U+row+2*graphic_rank = - accumulated charged curvature",
            "silent_carrier_policy": "hull crossings may pass through unoccupied packets; contiguous occupied support is not a feature",
        },
        "cegar": transcript,
        "exact_training_verification": {
            "states": len(rows),
            "all_state_potentials_reproduced": True,
            "arithmetic": "fractions.Fraction Gaussian elimination; no floating point or external solver",
        },
        "symbolic_rule_verification": symbolic,
        "baseline_evaluation": {
            "width": "n=3k+2",
            "baseline_u": "6k^2+5k+3",
            "terminal_potential": "-3U+2(n-1)^2+n",
            "exact_reduction_at_baseline": -5,
            "extra_u_effect": "each additional U lowers the terminal potential by 3",
            "logical_status": "substitution at K=5; not an independently proved terminal bound",
        },
        "terminal_accounting_identity": {
            "connected_terminal_value": "Phi=-K(U)",
            "telescoped_consequence": "K(U)+Phi_terminal=0",
            "lower_bound_consequence": "none without an independent terminal-control theorem",
        },
        "interpretation": {
            "cap_phase": list(PHASES),
            "row": ["previous-row U count", "previous-row U runs"],
            "rooting": "OUT-rooted face count and non-OUT attachment debt",
            "carrier": "maximum occurrence-hull crossing width; silent slots are permitted",
            "affine_counters": ["cumulative U", "cycle excess", "completed rows", "active face count"],
        },
        "limitations": [
            "The formula is universally tight accounting and supplies no positive lower bound.",
            "Evaluating Phi=-5 at the old baseline is equivalent to substituting K=5.",
            "The symbolic rule theorem applies to the 19 established stable affine-family rules.",
            "It does not prove that every obligation-5 frontier is represented by those rules.",
            "Finite n=5,n=8 completeness supplies exact anchors, not arbitrary-width language coverage.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_obligation5_potential.py",
            "command": ["python3", "-B", "analysis/residue_certificates/residue_two_obligation5_potential.py", "--output", "analysis/residue_two_obligation5_potential.json"],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"obligation-5 potential certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
