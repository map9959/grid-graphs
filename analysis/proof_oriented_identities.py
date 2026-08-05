#!/usr/bin/env python3
"""Executable identities and finite frontier-inequality certificates.

This is a proof-oriented prototype, not a proof of the residue-two theorem.
Certificates establish their inequality only for the transitions explicitly
listed in the certificate.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Sequence


CERTIFICATE_SCHEMA = "grid-graphs.frontier-inequality.v1"
DEMO_CERTIFICATE = Path(__file__).with_name("frontier_inequality_demo_certificate.json")


class CertificateError(ValueError):
    """A finite certificate is malformed or contains a failed inequality."""


class InfeasiblePotentialError(CertificateError):
    """The transition difference constraints contain a negative cycle."""


class _DSU:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))

    def find(self, vertex: int) -> int:
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def union(self, left: int, right: int) -> bool:
        left = self.find(left)
        right = self.find(right)
        if left == right:
            return False
        self.parent[right] = left
        return True


@dataclass(frozen=True)
class PatternIdentities:
    rows: int
    columns: int
    u_count: int
    row_runs: int
    column_runs: int
    run_sum: int
    dual_vertices: int
    dual_edges: int
    graphic_rank: int
    components: int
    cycle_rank: int
    component_excess: int
    identity_constant: int


@dataclass(frozen=True)
class TileRowDeltas:
    u_count: int
    horizontal_runs: int
    vertical_edges: int
    cycle_delta: int
    edge_delta: int
    rank_delta: int


@dataclass(frozen=True)
class PathTelescope:
    """Exact totals obtained by summing transition inequalities along a path."""

    initial_state: str
    terminal_state: str
    initial_potential: Fraction
    terminal_potential: Fraction
    total_u: int
    total_rank: int
    total_charge: int
    total_slack: Fraction

    @property
    def transition_total(self) -> Fraction:
        return Fraction(3 * self.total_u - 2 * self.total_rank)

    @property
    def telescoped_total(self) -> Fraction:
        return (
            self.terminal_potential
            - self.initial_potential
            + self.total_charge
            + self.total_slack
        )


def _validate_pattern(pattern: list[str]) -> tuple[int, int]:
    if not pattern or not pattern[0]:
        raise ValueError("pattern must be a nonempty rectangle")
    columns = len(pattern[0])
    if len(pattern) < 2 or columns < 2:
        raise ValueError("dual-grid identities require at least two rows and columns")
    if any(len(row) != columns or set(row) - {"U", "."} for row in pattern):
        raise ValueError("pattern must be a rectangular array of U and .")
    return len(pattern), columns


def _run_count(lines: Iterable[str]) -> int:
    return sum(
        value == "U" and (index == 0 or line[index - 1] != "U")
        for line in lines
        for index, value in enumerate(line)
    )


def _dual_edges(pattern: list[str]) -> tuple[int, list[tuple[int, int]]]:
    rows, columns = _validate_pattern(pattern)
    face_columns = columns - 1

    def face(row: int, column: int) -> int:
        return 1 + row * face_columns + column

    edges: list[tuple[int, int]] = []
    for row in range(rows):
        for column in range(columns - 1):
            if pattern[row][column] == pattern[row][column + 1] == "U":
                edges.append(
                    (
                        0 if row == 0 else face(row - 1, column),
                        0 if row + 1 == rows else face(row, column),
                    )
                )
    for row in range(rows - 1):
        for column in range(columns):
            if pattern[row][column] == pattern[row + 1][column] == "U":
                edges.append(
                    (
                        0 if column == 0 else face(row, column - 1),
                        0 if column + 1 == columns else face(row, column),
                    )
                )
    return 1 + (rows - 1) * (columns - 1), edges


def check_pattern_identities(pattern: list[str]) -> PatternIdentities:
    """Compute and assert the run/rank/component/cycle identities."""
    rows, columns = _validate_pattern(pattern)
    u_count = sum(row.count("U") for row in pattern)
    row_runs = _run_count(pattern)
    transposed = ["".join(pattern[row][column] for row in range(rows)) for column in range(columns)]
    column_runs = _run_count(transposed)
    run_sum = row_runs + column_runs
    dual_vertices, edges = _dual_edges(pattern)

    dsu = _DSU(dual_vertices)
    graphic_rank = sum(dsu.union(left, right) for left, right in edges)
    components = len({dsu.find(vertex) for vertex in range(dual_vertices)})
    cycle_rank = len(edges) - graphic_rank
    component_excess = components - 1
    identity_constant = 2 * u_count - dual_vertices + 1

    identities = {
        "edge/run": len(edges) == 2 * u_count - run_sum,
        "rank/component": graphic_rank == dual_vertices - components,
        "cycle/nullity": cycle_rank == len(edges) - dual_vertices + components,
        "rank+cycle=edge": graphic_rank + cycle_rank == len(edges),
        "component excess": run_sum + cycle_rank - identity_constant == component_excess,
        "three-U/two-rank": (
            3 * u_count - 2 * graphic_rank
            == 2 * run_sum + 2 * cycle_rank - u_count
        ),
    }
    failed = [name for name, valid in identities.items() if not valid]
    if failed:
        raise AssertionError(f"identity checks failed: {', '.join(failed)}")

    return PatternIdentities(
        rows=rows,
        columns=columns,
        u_count=u_count,
        row_runs=row_runs,
        column_runs=column_runs,
        run_sum=run_sum,
        dual_vertices=dual_vertices,
        dual_edges=len(edges),
        graphic_rank=graphic_rank,
        components=components,
        cycle_rank=cycle_rank,
        component_excess=component_excess,
        identity_constant=identity_constant,
    )


def check_n17_178_identity(pattern: list[str]) -> PatternIdentities:
    """Check delta = R + beta - 100 for one 17x17, 178-U pattern."""
    result = check_pattern_identities(pattern)
    if (result.rows, result.columns, result.u_count) != (17, 17, 178):
        raise ValueError("the specialized identity requires a 17x17 pattern with 178 U")
    if result.identity_constant != 100:
        raise AssertionError("17x17 specialization did not produce constant 100")
    if result.component_excess != result.run_sum + result.cycle_rank - 100:
        raise AssertionError("delta = R + beta - 100 failed")
    return result


def _rational(value: Any, context: str) -> Fraction:
    if (
        not isinstance(value, list)
        or len(value) != 2
        or type(value[0]) is not int
        or type(value[1]) is not int
    ):
        raise CertificateError(f"{context} must be [integer numerator, integer denominator]")
    numerator, denominator = value
    if denominator <= 0 or math.gcd(numerator, denominator) != 1:
        raise CertificateError(f"{context} must be reduced with positive denominator")
    return Fraction(numerator, denominator)


def _exact_fraction(value: Any, context: str) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if type(value) is int:
        return Fraction(value)
    raise CertificateError(f"{context} must be an integer or Fraction")


def transition_slack(
    transition: dict[str, Any], potentials: dict[str, Fraction]
) -> Fraction:
    """Return the exact slack in one certificate-like transition inequality."""
    if not isinstance(transition, dict):
        raise CertificateError("transition must be an object")
    if not isinstance(potentials, dict):
        raise CertificateError("potentials must be a state-to-potential map")
    transition_id = transition.get("id", "?")
    incoming = transition.get("in")
    outgoing = transition.get("out")
    if not isinstance(incoming, str) or not isinstance(outgoing, str):
        raise CertificateError(f"transition {transition_id!r} needs string in/out states")
    if incoming not in potentials or outgoing not in potentials:
        raise CertificateError(f"transition {transition_id!r} references an unknown state")
    integer_fields = ("dU", "dRank", "charge")
    if any(type(transition.get(field)) is not int for field in integer_fields):
        raise CertificateError(f"transition {transition_id!r} deltas and charge must be integers")
    if transition["dU"] < 0 or transition["dRank"] < 0:
        raise CertificateError(f"transition {transition_id!r} has a negative monotone delta")
    incoming_potential = _exact_fraction(
        potentials[incoming], f"state {incoming!r} potential"
    )
    outgoing_potential = _exact_fraction(
        potentials[outgoing], f"state {outgoing!r} potential"
    )
    return (
        Fraction(3 * transition["dU"] - 2 * transition["dRank"])
        - outgoing_potential
        + incoming_potential
        - transition["charge"]
    )


def verify_path_telescope(
    transitions: Iterable[dict[str, Any]], potentials: dict[str, Fraction]
) -> PathTelescope:
    """Verify a nonempty contiguous path and exactly telescope its inequalities."""
    path = tuple(transitions)
    if not path:
        raise CertificateError("transition path must be nonempty")
    if not isinstance(potentials, dict):
        raise CertificateError("potentials must be a state-to-potential map")

    initial_state = path[0].get("in") if isinstance(path[0], dict) else None
    previous_outgoing: str | None = None
    total_u = total_rank = total_charge = 0
    total_slack = Fraction(0)
    for index, transition in enumerate(path):
        if not isinstance(transition, dict):
            raise CertificateError(f"path transition {index} must be an object")
        if previous_outgoing is not None and transition.get("in") != previous_outgoing:
            raise CertificateError(f"transition path is not contiguous at index {index}")
        slack = transition_slack(transition, potentials)
        if slack < 0:
            raise CertificateError(
                f"transition {transition.get('id', '?')!r} has negative slack {slack}"
            )
        total_u += transition["dU"]
        total_rank += transition["dRank"]
        total_charge += transition["charge"]
        total_slack += slack
        previous_outgoing = transition["out"]

    if not isinstance(initial_state, str) or previous_outgoing is None:
        raise AssertionError("validated path has invalid endpoints")
    result = PathTelescope(
        initial_state=initial_state,
        terminal_state=previous_outgoing,
        initial_potential=_exact_fraction(
            potentials[initial_state], f"state {initial_state!r} potential"
        ),
        terminal_potential=_exact_fraction(
            potentials[previous_outgoing], f"state {previous_outgoing!r} potential"
        ),
        total_u=total_u,
        total_rank=total_rank,
        total_charge=total_charge,
        total_slack=total_slack,
    )
    if result.transition_total != result.telescoped_total:
        raise AssertionError("transition totals did not telescope")
    return result


def check_residue_two_terminal_algebra(
    n: int, terminal_constant: Fraction = Fraction(5)
) -> int:
    """Check `(2(n-1)^2+n+5)/3 = 6k^2+5k+3` for `n=3k+2`."""
    if type(n) is not int or n < 2 or n % 3 != 2:
        raise ValueError("n must have the form 3k+2 with k >= 0")
    constant = _exact_fraction(terminal_constant, "terminal constant")
    if constant != 5:
        raise ValueError("residue-two equality algebra requires terminal constant 5")
    k = (n - 2) // 3
    exact_bound = (2 * (n - 1) ** 2 + n + constant) / 3
    expected = Fraction(6 * k * k + 5 * k + 3)
    if exact_bound != expected:
        raise AssertionError("residue-two terminal algebra failed")
    return expected.numerator


def verify_frontier_certificate(certificate: Any) -> dict[str, int]:
    """Exactly verify all explicitly enumerated transition inequalities.

    Semantics for each transition t are
      3*dU(t) - 2*dRank(t) >= Phi(out(t)) - Phi(in(t)) + charge(t).
    All deltas and charges are integers. Potentials are exact reduced rationals.
    """
    if not isinstance(certificate, dict):
        raise CertificateError("certificate must be a JSON object")
    if certificate.get("schema") != CERTIFICATE_SCHEMA:
        raise CertificateError("unknown certificate schema")
    scope = certificate.get("scope")
    if not isinstance(scope, dict) or scope.get("semantics") != "enumerated-transitions-only":
        raise CertificateError("scope must declare enumerated-transitions-only semantics")
    if type(scope.get("complete_for_source")) is not bool:
        raise CertificateError("scope.complete_for_source must be boolean")

    states = certificate.get("states")
    transitions = certificate.get("transitions")
    if not isinstance(states, list) or not isinstance(transitions, list):
        raise CertificateError("states and transitions must be arrays")
    potentials: dict[str, Fraction] = {}
    for index, state in enumerate(states):
        if not isinstance(state, dict) or not isinstance(state.get("id"), str):
            raise CertificateError(f"state {index} needs a string id")
        state_id = state["id"]
        if state_id in potentials:
            raise CertificateError(f"duplicate state id {state_id!r}")
        potentials[state_id] = _rational(state.get("potential"), f"state {state_id!r} potential")

    transition_ids: set[str] = set()
    tight = 0
    for index, transition in enumerate(transitions):
        if not isinstance(transition, dict) or not isinstance(transition.get("id"), str):
            raise CertificateError(f"transition {index} needs a string id")
        transition_id = transition["id"]
        if transition_id in transition_ids:
            raise CertificateError(f"duplicate transition id {transition_id!r}")
        transition_ids.add(transition_id)
        incoming = transition.get("in")
        outgoing = transition.get("out")
        if incoming not in potentials or outgoing not in potentials:
            raise CertificateError(f"transition {transition_id!r} references an unknown state")
        integer_fields = ("dU", "dRank", "charge")
        if any(type(transition.get(field)) is not int for field in integer_fields):
            raise CertificateError(f"transition {transition_id!r} deltas and charge must be integers")
        if transition["dU"] < 0 or transition["dRank"] < 0:
            raise CertificateError(f"transition {transition_id!r} has a negative monotone delta")
        left = Fraction(3 * transition["dU"] - 2 * transition["dRank"])
        right = potentials[outgoing] - potentials[incoming] + transition["charge"]
        if left < right:
            raise CertificateError(
                f"transition {transition_id!r} fails: {left} < {right}"
            )
        tight += left == right
    return {"states": len(states), "transitions": len(transitions), "tight": tight}


def tile_grammar_transition_record(
    transition_id: str,
    incoming_state: Any,
    outgoing_state: Any,
    row_masks: Iterable[int],
    incoming_id: str,
    outgoing_id: str,
    charge: int,
) -> dict[str, Any]:
    """Convert an exact tile_grammar row/band transition to certificate data.

    `cycle_excess` counts dependent dual edges, so dRank = dEdges-dCycles.
    The adapter is intentionally duck-typed to keep this checker independent of
    tile_grammar's implementation.
    """
    masks = tuple(row_masks)
    n = incoming_state.n
    if outgoing_state.n != n or outgoing_state.row_index != incoming_state.row_index + len(masks):
        raise ValueError("states and row masks do not describe one contiguous transition")
    if any(type(mask) is not int or mask < 0 or mask >= 1 << n for mask in masks):
        raise ValueError("row mask does not fit the tile-grammar width")
    previous = incoming_state.previous_u_mask
    edge_delta = 0
    for mask in masks:
        edge_delta += (previous & mask).bit_count()
        edge_delta += (mask & (mask >> 1)).bit_count()
        previous = mask
    if masks and outgoing_state.previous_u_mask != masks[-1]:
        raise ValueError("outgoing previous_u_mask disagrees with the transition")
    d_u = outgoing_state.u_cost - incoming_state.u_cost
    d_cycles = outgoing_state.cycle_excess - incoming_state.cycle_excess
    d_rank = edge_delta - d_cycles
    if d_u != sum(mask.bit_count() for mask in masks):
        raise ValueError("outgoing U cost disagrees with row masks")
    if d_cycles < 0 or not 0 <= d_rank <= edge_delta:
        raise ValueError("cycle excess does not define a valid graphic-rank increment")
    return {
        "id": transition_id,
        "in": incoming_id,
        "out": outgoing_id,
        "dU": d_u,
        "dRank": d_rank,
        "charge": charge,
        "metadata": {"row_masks": list(masks), "dEdges": edge_delta, "dCycles": d_cycles},
    }


def tile_grammar_row_deltas(
    incoming_state: Any, current_u_mask: int, outgoing_state: Any
) -> TileRowDeltas:
    """Compute the exact curvature terms for one accepted row transition."""
    n = incoming_state.n
    if (
        outgoing_state.n != n
        or outgoing_state.row_index != incoming_state.row_index + 1
        or type(current_u_mask) is not int
        or not 0 <= current_u_mask < 1 << n
    ):
        raise ValueError("states and mask do not describe one row transition")
    if outgoing_state.previous_u_mask != current_u_mask:
        raise ValueError("outgoing previous_u_mask disagrees with the row mask")

    u_count = current_u_mask.bit_count()
    horizontal_runs = (current_u_mask & ~(current_u_mask << 1)).bit_count()
    vertical_edges = (incoming_state.previous_u_mask & current_u_mask).bit_count()
    cycle_delta = outgoing_state.cycle_excess - incoming_state.cycle_excess
    edge_delta = u_count - horizontal_runs + vertical_edges
    rank_delta = edge_delta - cycle_delta
    if outgoing_state.u_cost - incoming_state.u_cost != u_count:
        raise ValueError("outgoing U cost disagrees with the row mask")
    if cycle_delta < 0 or not 0 <= rank_delta <= edge_delta:
        raise ValueError("cycle excess does not define a valid graphic-rank increment")
    if 3 * u_count - 2 * rank_delta != (
        u_count + 2 * horizontal_runs - 2 * vertical_edges + 2 * cycle_delta
    ):
        raise AssertionError("row curvature identity failed")
    return TileRowDeltas(
        u_count=u_count,
        horizontal_runs=horizontal_runs,
        vertical_edges=vertical_edges,
        cycle_delta=cycle_delta,
        edge_delta=edge_delta,
        rank_delta=rank_delta,
    )


def _frontier_key(state: Any) -> tuple[int, int, tuple[int, ...]]:
    return state.row_index, state.previous_u_mask, state.partition


def _frontier_id(key: tuple[int, int, tuple[int, ...]]) -> str:
    row, mask, partition = key
    labels = ".".join(map(str, partition))
    return f"r{row}:m{mask}:p{labels}"


def export_complete_tile_row_source(n: int = 3, charge: int = 0) -> dict[str, Any]:
    """Exhaust the declared reachable tile_grammar row source for n in 2..6.

    The source quotient is exactly `(row_index, previous_u_mask, partition)`.
    Every width-n mask is attempted at every reachable nonterminal quotient
    state. This is completeness for that operational finite source only.
    """
    if n not in range(2, 7):
        raise ValueError("the prototype declares complete sources only for n=2..6")
    if type(charge) is not int:
        raise TypeError("uniform charge must be an integer")
    from tile_grammar import advance_row, initial_state

    initial = initial_state(n)
    representatives = {_frontier_key(initial): initial}
    all_representatives = dict(representatives)
    transitions: list[dict[str, Any]] = []
    layer_counts = [1]
    attempted = 0
    for _ in range(n):
        children: dict[tuple[int, int, tuple[int, ...]], Any] = {}
        for incoming_key in sorted(representatives):
            incoming = representatives[incoming_key]
            incoming_id = _frontier_id(incoming_key)
            for mask in range(1 << n):
                attempted += 1
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                outgoing_key = _frontier_key(outgoing)
                outgoing_id = _frontier_id(outgoing_key)
                transition_id = f"{incoming_id}->m{mask}->{outgoing_id}"
                transitions.append(
                    tile_grammar_transition_record(
                        transition_id,
                        incoming,
                        outgoing,
                        [mask],
                        incoming_id,
                        outgoing_id,
                        charge,
                    )
                )
                children.setdefault(outgoing_key, outgoing)
                all_representatives.setdefault(outgoing_key, outgoing)
        representatives = children
        layer_counts.append(len(representatives))

    states = []
    for key in sorted(all_representatives):
        row, mask, partition = key
        states.append(
            {
                "id": _frontier_id(key),
                "metadata": {
                    "row_index": row,
                    "previous_u_mask": mask,
                    "partition": list(partition),
                },
            }
        )
    return {
        "n": n,
        "charge": charge,
        "initial_id": _frontier_id(_frontier_key(initial)),
        "states": states,
        "transitions": transitions,
        "attempted": attempted,
        "accepted": len(transitions),
        "rejected": attempted - len(transitions),
        "reachable_states_by_row": layer_counts,
    }


def _mask_run_count(mask: int) -> int:
    return (mask & ~(mask << 1)).bit_count()


def _interval_count(labels: Sequence[int], target: int) -> int:
    return sum(
        label == target and (index == 0 or labels[index - 1] != target)
        for index, label in enumerate(labels)
    )


def frontier_feature_signature(n: int, metadata: dict[str, Any], level: str) -> tuple:
    """Project an exact frontier onto an exploratory OUT-aware feature state."""
    if level not in ("coarse", "runs", "out", "profiles", "partition", "exact"):
        raise ValueError("unknown feature level")
    row = metadata["row_index"]
    mask = metadata["previous_u_mask"]
    partition = tuple(metadata["partition"])
    if not 0 <= row <= n or not partition:
        raise ValueError("invalid frontier metadata")

    if row == 0:
        boundary_mode = "top"
    elif row == n:
        boundary_mode = "terminal"
    elif row + 1 == n:
        boundary_mode = "bottom"
    else:
        boundary_mode = "bulk"

    out_label = partition[0]
    faces = partition[1:]
    non_out_labels = sorted(set(faces) - {out_label})
    base = (
        row % 3,
        boundary_mode,
        mask.bit_count(),
        bool(mask & 1),
        bool(mask & (1 << (n - 1))),
        sum(label == out_label for label in faces),
        len(non_out_labels),
        bool(faces and faces[0] == out_label),
        bool(faces and faces[-1] == out_label),
    )
    if level == "coarse":
        return base
    if level == "runs":
        return (*base, _mask_run_count(mask))
    if level == "out":
        return (*base, _mask_run_count(mask), _interval_count(faces, out_label))
    if level == "partition":
        return (*base, _mask_run_count(mask), partition)
    if level == "exact":
        return (row % 3, boundary_mode, mask, partition)

    profiles = []
    for label in non_out_labels:
        slots = [index for index, observed in enumerate(faces) if observed == label]
        profiles.append(
            (
                len(slots),
                _interval_count(faces, label),
                bool(slots and slots[0] == 0),
                bool(slots and slots[-1] + 1 == len(faces)),
            )
        )
    return (
        *base,
        _mask_run_count(mask),
        _interval_count(faces, out_label),
        tuple(sorted(profiles)),
    )


def _feature_id(feature: tuple) -> str:
    return json.dumps(feature, separators=(",", ":"), ensure_ascii=True)


def build_pooled_frontier_feature_experiment(
    widths: Sequence[int] = tuple(range(3, 7)), level: str = "coarse", charge: int = 1
) -> dict[str, Any]:
    """Test one feature potential against every transition in small exact sources.

    This is a CEGAR experiment over enumerated widths, not a uniform proof. For
    parallel projected edges only the smallest weight is needed: satisfying it
    implies every weaker concrete constraint with the same endpoints.
    """
    normalized_widths = tuple(sorted(set(widths)))
    if not normalized_widths or any(n not in range(2, 7) for n in normalized_widths):
        raise ValueError("pooled experiment widths must be a nonempty subset of 2..6")
    if type(charge) is not int:
        raise TypeError("charge must be an integer")
    from tile_grammar import advance_row, initial_state, row_mask

    sources = {n: export_complete_tile_row_source(n, charge) for n in normalized_widths}
    state_features: dict[tuple[int, str], tuple] = {}
    all_features: set[tuple] = set()
    for n, source in sources.items():
        for state in source["states"]:
            feature = frontier_feature_signature(n, state["metadata"], level)
            state_features[(n, state["id"])] = feature
            all_features.add(feature)

    pooled_by_pair: dict[tuple[str, str], dict[str, Any]] = {}
    concrete_records = []
    for n, source in sources.items():
        for transition in source["transitions"]:
            incoming = _feature_id(state_features[(n, transition["in"])])
            outgoing = _feature_id(state_features[(n, transition["out"])])
            projected = {
                "id": f"n{n}:{transition['id']}",
                "in": incoming,
                "out": outgoing,
                "dU": transition["dU"],
                "dRank": transition["dRank"],
                "charge": transition["charge"],
                "metadata": {"width": n, "source_transition": transition["id"]},
            }
            concrete_records.append(projected)
            pair = (incoming, outgoing)
            retained = pooled_by_pair.get(pair)
            if retained is None or _constraint_weight(projected) < _constraint_weight(retained):
                pooled_by_pair[pair] = projected

    state_ids = sorted(_feature_id(feature) for feature in all_features)
    transitions = sorted(pooled_by_pair.values(), key=lambda item: (item["in"], item["out"]))
    anchor_features = {
        state_features[(n, sources[n]["initial_id"])] for n in normalized_widths
    }
    if len(anchor_features) != 1:
        raise AssertionError("initial frontiers did not share one feature state")
    anchor = _feature_id(anchor_features.pop())
    potentials = synthesize_difference_potentials(state_ids, transitions, anchor)

    tight_concrete = 0
    for transition in concrete_records:
        left = Fraction(3 * transition["dU"] - 2 * transition["dRank"])
        right = (
            potentials[transition["out"]]
            - potentials[transition["in"]]
            + transition["charge"]
        )
        if left < right:
            raise AssertionError("pooled potential failed a concrete transition")
        tight_concrete += left == right

    exact_constants = {}
    pooled_constants = {}
    witness_tightness = {}
    terminal_features_by_phase: dict[int, set[str]] = defaultdict(set)
    for n, source in sources.items():
        exact = build_complete_tile_certificate(n, charge)
        exact_constants[str(n)] = exact["analysis"]["minimum_terminal_potential"][0]
        terminal_ids = [
            state["id"]
            for state in source["states"]
            if state["metadata"]["row_index"] == n
        ]
        projected_terminals = {
            _feature_id(state_features[(n, state_id)]) for state_id in terminal_ids
        }
        pooled_constants[str(n)] = min(potentials[state_id] for state_id in projected_terminals)
        terminal_features_by_phase[n % 3].update(projected_terminals)

        state = initial_state(n)
        tight_rows = 0
        total_slack = Fraction(0)
        for row in exact["analysis"]["tight_witness_rows"]:
            mask = row_mask(row)
            outgoing = advance_row(state, mask)
            if outgoing is None:
                raise AssertionError("exact tight witness failed pooled replay")
            deltas = tile_grammar_row_deltas(state, mask, outgoing)
            incoming_feature = frontier_feature_signature(
                n,
                {
                    "row_index": state.row_index,
                    "previous_u_mask": state.previous_u_mask,
                    "partition": state.partition,
                },
                level,
            )
            outgoing_feature = frontier_feature_signature(
                n,
                {
                    "row_index": outgoing.row_index,
                    "previous_u_mask": outgoing.previous_u_mask,
                    "partition": outgoing.partition,
                },
                level,
            )
            slack = (
                Fraction(3 * deltas.u_count - 2 * deltas.rank_delta - charge)
                - potentials[_feature_id(outgoing_feature)]
                + potentials[_feature_id(incoming_feature)]
            )
            if slack < 0:
                raise AssertionError("pooled potential failed a tight witness row")
            tight_rows += slack == 0
            total_slack += slack
            state = outgoing
        witness_tightness[str(n)] = {
            "rows": n,
            "tight_rows": tight_rows,
            "total_slack": _fraction_json(total_slack),
        }
    phase_constants = {
        str(phase): min(potentials[state_id] for state_id in terminal_ids)
        for phase, terminal_ids in sorted(terminal_features_by_phase.items())
    }

    return {
        "scope": {
            "semantics": "enumerated-width-feature-projection-only",
            "widths": list(normalized_widths),
            "feature_level": level,
            "uniform_row_charge": charge,
        },
        "census": {
            "concrete_states": sum(len(source["states"]) for source in sources.values()),
            "feature_states": len(state_ids),
            "concrete_transitions": len(concrete_records),
            "pooled_transitions": len(transitions),
            "tight_concrete_transitions": tight_concrete,
        },
        "analysis": {
            "exact_width_terminal_constants": exact_constants,
            "pooled_width_terminal_constants": {
                n: _fraction_json(value) for n, value in pooled_constants.items()
            },
            "pooled_phase_terminal_constants": {
                phase: _fraction_json(value) for phase, value in phase_constants.items()
            },
            "desired_phase_constants": {"0": 4, "1": 2, "2": 5} if charge == 1 else None,
            "exact_minimum_witness_tightness": witness_tightness,
        },
    }


def _constraint_weight(transition: dict[str, Any]) -> Fraction:
    integer_fields = ("dU", "dRank", "charge")
    if any(type(transition.get(field)) is not int for field in integer_fields):
        raise CertificateError("difference-constraint deltas and charge must be integers")
    return Fraction(
        3 * transition["dU"] - 2 * transition["dRank"] - transition["charge"]
    )


def synthesize_difference_potentials(
    state_ids: Sequence[str], transitions: Sequence[dict[str, Any]], anchor: str
) -> dict[str, Fraction]:
    """Return exact shortest-path potentials, or detect a negative cycle."""
    if len(set(state_ids)) != len(state_ids) or anchor not in state_ids:
        raise CertificateError("potential synthesis needs unique states and a known anchor")
    known = set(state_ids)
    edges: list[tuple[str, str, Fraction, str]] = []
    for transition in transitions:
        incoming = transition.get("in")
        outgoing = transition.get("out")
        if incoming not in known or outgoing not in known:
            raise CertificateError("potential synthesis transition references an unknown state")
        edges.append((incoming, outgoing, _constraint_weight(transition), transition.get("id", "?")))

    # A zero-distance super-source reaches every state. An update on pass |V|
    # is exactly the Bellman-Ford negative-cycle criterion.
    super_dist = {state_id: Fraction(0) for state_id in state_ids}
    for iteration in range(len(state_ids)):
        updated_by: str | None = None
        for incoming, outgoing, weight, transition_id in edges:
            candidate = super_dist[incoming] + weight
            if candidate < super_dist[outgoing]:
                super_dist[outgoing] = candidate
                updated_by = transition_id
        if updated_by is None:
            break
        if iteration + 1 == len(state_ids):
            raise InfeasiblePotentialError(
                f"negative cycle detected through transition {updated_by!r}"
            )

    infinity: Fraction | None = None
    distances: dict[str, Fraction | None] = {state_id: infinity for state_id in state_ids}
    distances[anchor] = Fraction(0)
    for _ in range(max(0, len(state_ids) - 1)):
        changed = False
        for incoming, outgoing, weight, _ in edges:
            if distances[incoming] is None:
                continue
            candidate = distances[incoming] + weight
            if distances[outgoing] is None or candidate < distances[outgoing]:
                distances[outgoing] = candidate
                changed = True
        if not changed:
            break
    unreachable = [state_id for state_id, value in distances.items() if value is None]
    if unreachable:
        raise CertificateError(f"states are unreachable from anchor: {unreachable[:3]}")
    return {state_id: value for state_id, value in distances.items() if value is not None}


def _fraction_json(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def _ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def _tight_witness_rows(
    source: dict[str, Any], potentials: dict[str, Fraction], minimum_terminal: Fraction
) -> list[str]:
    reachable = {source["initial_id"]}
    predecessor: dict[str, tuple[str, int]] = {}
    for transition in source["transitions"]:
        incoming = transition["in"]
        outgoing = transition["out"]
        if (
            incoming in reachable
            and potentials[outgoing] == potentials[incoming] + _constraint_weight(transition)
        ):
            reachable.add(outgoing)
            predecessor.setdefault(
                outgoing, (incoming, transition["metadata"]["row_masks"][0])
            )

    n = source["n"]
    terminal = min(
        state["id"]
        for state in source["states"]
        if state["metadata"]["row_index"] == n
        and potentials[state["id"]] == minimum_terminal
        and state["id"] in reachable
    )
    masks = []
    while terminal != source["initial_id"]:
        terminal, mask = predecessor[terminal]
        masks.append(mask)
    masks.reverse()
    return ["".join("U" if mask & (1 << column) else "." for column in range(n)) for mask in masks]


def build_complete_tile_certificate(n: int = 3, charge: int = 0) -> dict[str, Any]:
    """Export, synthesize, and independently inequality-check a finite source."""
    source = export_complete_tile_row_source(n, charge)
    state_ids = [state["id"] for state in source["states"]]
    potentials = synthesize_difference_potentials(
        state_ids, source["transitions"], source["initial_id"]
    )
    states = [
        {**state, "potential": _fraction_json(potentials[state["id"]])}
        for state in source["states"]
    ]
    terminals = [
        state["id"]
        for state in source["states"]
        if state["metadata"]["row_index"] == n
    ]
    terminal_values = [potentials[state_id] for state_id in terminals]
    minimum_terminal = min(terminal_values)
    maximum_terminal = max(terminal_values)
    final_rank = (n - 1) ** 2
    implied_u = _ceil_fraction((minimum_terminal + 2 * final_rank) / 3)

    certificate = {
        "schema": CERTIFICATE_SCHEMA,
        "scope": {
            "semantics": "enumerated-transitions-only",
            "complete_for_source": True,
            "source": {
                "kind": "tile_grammar.reachable-row-quotient.v1",
                "n": n,
                "rows": n,
                "state_key": ["row_index", "previous_u_mask", "partition"],
                "mask_domain": [0, 1 << n],
                "uniform_charge": charge,
                "attempted": source["attempted"],
                "accepted": source["accepted"],
                "rejected": source["rejected"],
                "reachable_states_by_row": source["reachable_states_by_row"],
                "coverage": (
                    "all masks in mask_domain are passed to advance_row from every "
                    "reachable nonterminal quotient state; None results are rejected"
                ),
            },
        },
        "states": states,
        "transitions": source["transitions"],
        "analysis": {
            "initial_state": source["initial_id"],
            "terminal_states": len(terminals),
            "minimum_terminal_potential": _fraction_json(minimum_terminal),
            "maximum_terminal_potential": _fraction_json(maximum_terminal),
            "connected_final_graphic_rank": final_rank,
            "implied_u_lower_bound": implied_u,
            "tight_witness_rows": _tight_witness_rows(source, potentials, minimum_terminal),
        },
    }
    verification = verify_frontier_certificate(certificate)
    tight_by_row: dict[int, int] = defaultdict(int)
    potential_lookup = {state_id: potentials[state_id] for state_id in state_ids}
    row_lookup = {state["id"]: state["metadata"]["row_index"] for state in states}
    for transition in source["transitions"]:
        slack = (
            _constraint_weight(transition)
            - potential_lookup[transition["out"]]
            + potential_lookup[transition["in"]]
        )
        if slack == 0:
            tight_by_row[row_lookup[transition["out"]]] += 1
    certificate["analysis"].update(
        {
            "tight_transitions": verification["tight"],
            "tight_transitions_by_destination_row": {
                str(row): tight_by_row[row] for row in range(1, n + 1)
            },
            "zero_charge_assessment": (
                f"positive and sharp for this finite source: 3|U|-2rank >= "
                f"{minimum_terminal}, hence |U| >= {implied_u} at final rank {final_rank}"
                if charge == 0 and minimum_terminal > 0
                else "no positive zero-charge terminal bound established"
            ),
        }
    )
    return certificate


def reverify_complete_tile_certificate(certificate: Any) -> dict[str, int]:
    """Regenerate the declared tile source and compare the complete certificate."""
    verification = verify_frontier_certificate(certificate)
    try:
        source = certificate["scope"]["source"]
        n = source["n"]
        charge = source["uniform_charge"]
    except (KeyError, TypeError) as error:
        raise CertificateError("missing complete tile source declaration") from error
    rebuilt = build_complete_tile_certificate(n, charge)
    if rebuilt != certificate:
        raise CertificateError("certificate differs from regenerated complete tile source")
    return verification


def _read_pattern(path: Path) -> list[str]:
    rows = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    pattern_parser = subparsers.add_parser("pattern", help="check identities for a U/. pattern")
    pattern_parser.add_argument("path", type=Path)
    pattern_parser.add_argument("--n17-178", action="store_true")
    certificate_parser = subparsers.add_parser("certificate", help="verify a finite JSON certificate")
    certificate_parser.add_argument("path", type=Path)
    subparsers.add_parser("demo", help="verify the bundled tiny certificate")
    export_parser = subparsers.add_parser(
        "export-small", help="export and reverify a complete small tile-row source"
    )
    export_parser.add_argument("--n", type=int, choices=range(2, 7), default=3)
    export_parser.add_argument("--charge", type=int, default=0)
    export_parser.add_argument("--output", type=Path, required=True)
    pooled_parser = subparsers.add_parser(
        "pool-features", help="run the small-width OUT-aware feature experiment"
    )
    pooled_parser.add_argument(
        "--level",
        choices=("coarse", "runs", "out", "profiles", "partition", "exact"),
        default="coarse",
    )
    pooled_parser.add_argument("--min-n", type=int, choices=range(2, 7), default=3)
    pooled_parser.add_argument("--max-n", type=int, choices=range(2, 7), default=6)
    pooled_parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.command == "pattern":
        rows = _read_pattern(args.path)
        result = check_n17_178_identity(rows) if args.n17_178 else check_pattern_identities(rows)
        print(json.dumps(asdict(result), indent=2))
    elif args.command in ("certificate", "demo"):
        path = DEMO_CERTIFICATE if args.command == "demo" else args.path
        result = verify_frontier_certificate(json.loads(path.read_text()))
        print(json.dumps(result, indent=2))
    elif args.command == "export-small":
        certificate = build_complete_tile_certificate(args.n, args.charge)
        args.output.write_text(json.dumps(certificate, indent=2) + "\n")
        loaded = json.loads(args.output.read_text())
        verification = reverify_complete_tile_certificate(loaded)
        print(json.dumps({**verification, **loaded["analysis"]}, indent=2))
    else:
        if args.min_n > args.max_n:
            parser.error("--min-n must not exceed --max-n")
        result = build_pooled_frontier_feature_experiment(
            tuple(range(args.min_n, args.max_n + 1)), args.level
        )
        rendered = json.dumps(result, indent=2) + "\n"
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
