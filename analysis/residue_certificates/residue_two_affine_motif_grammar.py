#!/usr/bin/env python3
"""Exact boundary-defect packet words for the residue-two affine family.

The codec in this module is lossless, but deliberately partial: a packet word
is accepted only when every non-dominant atom occurs in the first two or last
four packets.  ``BoundaryDefectFrontier`` retains a separate lossless
``CarrierRecord``.  Under the checked one-carrier discipline,
``CompactBoundaryDefectFrontier`` instead reconstructs global names from the
left-face mode and packet-local carrier roles.

The generated report is finite evidence about the listed corridors and
traces.  In particular, affine-family closure is not equality-language
coverage.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.residue_certificates.residue_two_carrier_grammar import (
    CarrierEvent,
    CarrierRecord,
    canonical_rooted_partition,
    expand_carrier_record,
    recognize_state,
)
from analysis.tiles.symbolic_packet_frontier import encode_frontier
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    row_mask,
)
from analysis.transport.equality_corridor import (
    EqualityCorridor,
    build_equality_corridor,
)

SCHEMA = "grid-graphs.residue-two-affine-motif-grammar.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_affine_motif_grammar.json")
CORRIDOR_WIDTHS = (5, 8)
FIXED_EQUALITY_WIDTHS = (11, 14)
AFFINE_WIDTHS = tuple(range(17, 120, 3))
ROLES = ("single", "open", "carry", "close")


@dataclass(frozen=True, order=True, slots=True)
class PacketCarrierRole:
    """Anonymous packet-local component role, rooted by local label."""

    local_label: int
    role: str
    carries_in: bool
    carries_out: bool


@dataclass(frozen=True, order=True, slots=True)
class BoundaryDefectAtom:
    """One constant-size packet observation."""

    previous_word: int
    rooted_restriction: tuple[int, ...]
    carrier_roles: tuple[PacketCarrierRole, ...]

    def __post_init__(self) -> None:
        if type(self.previous_word) is not int or not 0 <= self.previous_word < 8:
            raise ValueError("previous packet word must be a three-bit integer")
        if len(self.rooted_restriction) not in (0, 3):
            raise ValueError("rooted packet restriction must be empty or have three labels")
        if any(type(label) is not int or label < 0 for label in self.rooted_restriction):
            raise ValueError("rooted packet labels must be nonnegative integers")
        if self.rooted_restriction:
            seen = {0}
            for label in self.rooted_restriction:
                if label > len(seen) or (label not in seen and label != len(seen)):
                    raise ValueError("packet restriction is not canonically rooted")
                seen.add(label)
        local_components = set(self.rooted_restriction) - {0}
        if tuple(sorted(self.carrier_roles)) != self.carrier_roles:
            raise ValueError("packet carrier roles must be sorted")
        if (
            len(self.carrier_roles) != len(local_components)
            or {item.local_label for item in self.carrier_roles} != local_components
        ):
            raise ValueError("packet carrier roles must describe each local non-OUT component")
        if any(item.role not in ROLES for item in self.carrier_roles):
            raise ValueError("unknown packet carrier role")


@dataclass(frozen=True, slots=True)
class BoundaryDefectWord:
    """Canonical dominant atom, bounded boundary exceptions, and packet count."""

    length: int
    dominant: BoundaryDefectAtom
    exceptions: tuple[tuple[int, BoundaryDefectAtom], ...]


class InteriorDefectError(ValueError):
    """Raised when an exact atom word is outside the boundary-defect grammar."""

    def __init__(self, indices: tuple[int, ...]):
        self.indices = indices
        super().__init__(f"non-dominant atoms at interior packet indices {indices}")


@dataclass(frozen=True, slots=True)
class BoundaryDefectFrontier:
    """Exact symbolic state: bounded atom word plus lossless global carrier data."""

    row_index: int
    previous_cap_bits: tuple[int, int]
    word: BoundaryDefectWord
    carrier_record: CarrierRecord
    u_cost: int
    cycle_excess: int


@dataclass(frozen=True, slots=True)
class CompactBoundaryDefectFrontier:
    """Constant-control frontier for one-carrier boundary-defect words."""

    row_index: int
    previous_cap_bits: tuple[int, int]
    left_face_role: str
    word: BoundaryDefectWord
    u_cost: int
    cycle_excess: int


def boundary_indices(length: int) -> frozenset[int]:
    """Return the first two and final four valid packet indices."""
    if type(length) is not int or length < 1:
        raise ValueError("boundary-defect words require positive length")
    return frozenset({*range(min(2, length)), *range(max(0, length - 4), length)})


def canonical_dominant(atoms: Sequence[BoundaryDefectAtom]) -> BoundaryDefectAtom:
    """Choose maximum multiplicity, breaking ties by the atom's total order."""
    if not atoms:
        raise ValueError("cannot choose a dominant atom from an empty word")
    counts = Counter(atoms)
    maximum = max(counts.values())
    return min(atom for atom, count in counts.items() if count == maximum)


def interior_violation_indices(atoms: Sequence[BoundaryDefectAtom]) -> tuple[int, ...]:
    """Return all non-dominant indices not covered by the boundary allowance."""
    values = tuple(atoms)
    dominant = canonical_dominant(values)
    allowed = boundary_indices(len(values))
    return tuple(index for index, atom in enumerate(values) if atom != dominant and index not in allowed)


def encode_boundary_defect_word(
    atoms: Sequence[BoundaryDefectAtom],
) -> BoundaryDefectWord:
    """Canonically encode an accepted arbitrary atom sequence, or reject it."""
    values = tuple(atoms)
    dominant = canonical_dominant(values)
    violations = interior_violation_indices(values)
    if violations:
        raise InteriorDefectError(violations)
    return BoundaryDefectWord(
        len(values),
        dominant,
        tuple((index, atom) for index, atom in enumerate(values) if atom != dominant),
    )


def expand_boundary_defect_word(word: BoundaryDefectWord) -> tuple[BoundaryDefectAtom, ...]:
    """Validate canonical form and expand exactly to the original atom sequence."""
    if not isinstance(word, BoundaryDefectWord):
        raise TypeError("word must be a BoundaryDefectWord")
    allowed = boundary_indices(word.length)
    indices = tuple(index for index, _ in word.exceptions)
    if indices != tuple(sorted(set(indices))) or any(index not in allowed for index in indices):
        raise ValueError("exceptions must be unique, sorted boundary indices")
    if any(atom == word.dominant for _, atom in word.exceptions):
        raise ValueError("an exception cannot equal the dominant atom")
    atoms = [word.dominant] * word.length
    for index, atom in word.exceptions:
        atoms[index] = atom
    values = tuple(atoms)
    if canonical_dominant(values) != word.dominant:
        raise ValueError("stored dominant atom is not canonical")
    return values


def _root_packet(labels: tuple[int, int, int]) -> tuple[tuple[int, int, int], dict[int, int]]:
    renaming = {0: 0}
    rooted = []
    for label in labels:
        renaming.setdefault(label, len(renaming))
        rooted.append(renaming[label])
    return tuple(rooted), renaming


def packet_atoms(state: FrontierState) -> tuple[BoundaryDefectAtom, ...]:
    """Extract exact local atom observations from a canonical frontier."""
    symbolic = encode_frontier(state)
    recognition = recognize_state(state)
    events = {(event.group, event.component): event for event in recognition.record.events}
    carriers = {(event.cut, event.component) for event in recognition.record.carriers}
    atoms = []
    for packet, previous_word in enumerate(symbolic.previous_packet_words):
        if symbolic.packet_face_labels:
            global_labels = symbolic.packet_face_labels[packet]
            restriction, local = _root_packet(global_labels)
            group = packet + 1
            roles = tuple(sorted(
                PacketCarrierRole(
                    local[component],
                    events[(group, component)].role,
                    (group - 1, component) in carriers,
                    (group, component) in carriers,
                )
                for component in sorted(set(global_labels) - {0})
            ))
        else:
            restriction = ()
            roles = ()
        atoms.append(BoundaryDefectAtom(previous_word, restriction, roles))
    return tuple(atoms)


def encode_boundary_defect_frontier(state: FrontierState) -> BoundaryDefectFrontier:
    """Encode one accepted state, retaining a separate lossless carrier record."""
    symbolic = encode_frontier(state)
    recognition = recognize_state(state)
    return BoundaryDefectFrontier(
        state.row_index,
        symbolic.previous_cap_bits,
        encode_boundary_defect_word(packet_atoms(state)),
        recognition.record,
        state.u_cost,
        state.cycle_excess,
    )


def expand_boundary_defect_frontier(encoded: BoundaryDefectFrontier) -> FrontierState:
    """Validate both channels and reconstruct the exact canonical frontier."""
    if not isinstance(encoded, BoundaryDefectFrontier):
        raise TypeError("encoded must be a BoundaryDefectFrontier")
    atoms = expand_boundary_defect_word(encoded.word)
    partition = expand_carrier_record(encoded.carrier_record)
    n = 3 * encoded.word.length + 2
    if encoded.carrier_record.width != n:
        raise ValueError("carrier width and boundary word length disagree")
    if (
        len(encoded.previous_cap_bits) != 2
        or any(type(bit) is not int or bit not in (0, 1) for bit in encoded.previous_cap_bits)
    ):
        raise ValueError("previous cap bits must be a pair of bits")
    mask = encoded.previous_cap_bits[0]
    for packet, atom in enumerate(atoms):
        mask |= atom.previous_word << (1 + 3 * packet)
    mask |= encoded.previous_cap_bits[1] << (n - 1)
    state = FrontierState(
        n, encoded.row_index, mask, partition, encoded.u_cost, encoded.cycle_excess
    )
    if packet_atoms(state) != atoms:
        raise ValueError("packet atoms disagree with the lossless carrier record")
    return state


def _left_face_role(state: FrontierState, record: CarrierRecord) -> str:
    if len(state.partition) == 1:
        return "absent"
    component = state.partition[1]
    if component == 0:
        return "out"
    if CarrierEvent(0, component) in record.carriers:
        return "open"
    return "single"


def _expand_compact_partition(
    length: int,
    left_face_role: str,
    atoms: tuple[BoundaryDefectAtom, ...],
) -> tuple[int, ...]:
    if left_face_role == "absent":
        if any(atom.rooted_restriction or atom.carrier_roles for atom in atoms):
            raise ValueError("an absent frontier cannot contain packet face labels")
        return (0,)
    if left_face_role not in ("out", "single", "open"):
        raise ValueError("unknown left-face role")

    next_label = 1
    active: int | None = None
    if left_face_role == "out":
        faces = [0]
    else:
        faces = [next_label]
        active = next_label if left_face_role == "open" else None
        next_label += 1

    for atom in atoms:
        if len(atom.rooted_restriction) != 3:
            raise ValueError("an open frontier requires three labels per packet")
        roles = {item.local_label: item for item in atom.carrier_roles}
        entering = active
        mapping = {0: 0}
        outgoing: int | None = None
        for local_label in atom.rooted_restriction:
            if local_label in mapping:
                continue
            role = roles[local_label]
            if role.carries_in:
                if entering is None:
                    raise ValueError("packet expects a missing incoming carrier")
                global_label = entering
            else:
                global_label = next_label
                next_label += 1
            mapping[local_label] = global_label
            if role.carries_out:
                if outgoing is not None and outgoing != global_label:
                    raise ValueError("packet creates concurrent outgoing carriers")
                outgoing = global_label
        if entering is not None and not any(
            role.carries_in for role in atom.carrier_roles
        ):
            raise ValueError("incoming carrier is absent from the packet")
        if any(role.carries_in for role in atom.carrier_roles) and not any(
            role.local_label in mapping and mapping[role.local_label] == entering
            for role in atom.carrier_roles
            if role.carries_in
        ):
            raise ValueError("incoming carrier role is inconsistent")
        faces.extend(mapping[label] for label in atom.rooted_restriction)
        active = outgoing
    if active is not None:
        raise ValueError("carrier remains open beyond the final packet")
    if len(faces) != 3 * length + 1:
        raise AssertionError("compact packet expansion has the wrong face count")
    return canonical_rooted_partition((0, *faces))


def encode_compact_boundary_defect_frontier(
    state: FrontierState,
) -> CompactBoundaryDefectFrontier:
    """Encode a state using bounded atom defects and one active carrier."""
    symbolic = encode_frontier(state)
    recognition = recognize_state(state)
    if not recognition.accepted:
        raise ValueError("compact encoding requires the one-carrier grammar")
    encoded = CompactBoundaryDefectFrontier(
        row_index=state.row_index,
        previous_cap_bits=symbolic.previous_cap_bits,
        left_face_role=_left_face_role(state, recognition.record),
        word=encode_boundary_defect_word(packet_atoms(state)),
        u_cost=state.u_cost,
        cycle_excess=state.cycle_excess,
    )
    if expand_compact_boundary_defect_frontier(encoded) != state:
        raise AssertionError("compact boundary-defect frontier did not round trip")
    return encoded


def expand_compact_boundary_defect_frontier(
    encoded: CompactBoundaryDefectFrontier,
) -> FrontierState:
    """Expand the exact one-carrier word without a global CarrierRecord."""
    if not isinstance(encoded, CompactBoundaryDefectFrontier):
        raise TypeError("encoded must be a CompactBoundaryDefectFrontier")
    atoms = expand_boundary_defect_word(encoded.word)
    n = 3 * encoded.word.length + 2
    partition = _expand_compact_partition(
        encoded.word.length, encoded.left_face_role, atoms
    )
    mask = encoded.previous_cap_bits[0]
    for packet, atom in enumerate(atoms):
        mask |= atom.previous_word << (1 + 3 * packet)
    mask |= encoded.previous_cap_bits[1] << (n - 1)
    state = FrontierState(
        n,
        encoded.row_index,
        mask,
        partition,
        encoded.u_cost,
        encoded.cycle_excess,
    )
    if packet_atoms(state) != atoms or not recognize_state(state).accepted:
        raise ValueError("compact atom roles do not reconstruct the frontier")
    return state


def replay_trace(rows: Sequence[str]) -> list[FrontierState]:
    n = len(rows)
    state = initial_state(n)
    states = [state]
    for index, row in enumerate(rows):
        state = advance_row(state, row_mask(row))
        if state is None:
            raise ValueError(f"trace failed frontier expansion at row {index}")
        states.append(state)
    return states


def equality_states(corridor: EqualityCorridor) -> list[FrontierState]:
    return [
        corridor.layers[row][key]
        for row, keys in enumerate(corridor.corridor_states)
        for key in keys
    ]


def _atom_id(atom: BoundaryDefectAtom) -> str:
    roles = ",".join(
        f"{role.local_label}:{role.role}:{int(role.carries_in)}{int(role.carries_out)}"
        for role in atom.carrier_roles
    )
    restriction = "-" if not atom.rooted_restriction else "".join(map(str, atom.rooted_restriction))
    return f"{atom.previous_word}|{restriction}|{roles or '-'}"


def census_states(states: Iterable[FrontierState]) -> dict:
    """Report exact acceptance, defects, and motif/control observations."""
    values = list(states)
    accepted = round_trips = 0
    exception_counts = []
    violations = Counter()
    dominant = Counter()
    controls = Counter()
    carrier_accepted = compact_round_trips = 0
    for state in values:
        atoms = packet_atoms(state)
        motif = canonical_dominant(atoms)
        dominant[motif] += 1
        bad = interior_violation_indices(atoms)
        violations.update(bad)
        carrier_accepted += recognize_state(state).accepted
        if bad:
            continue
        encoded = encode_boundary_defect_frontier(state)
        accepted += 1
        exception_counts.append(len(encoded.word.exceptions))
        controls.update(atom for _, atom in encoded.word.exceptions)
        if expand_boundary_defect_frontier(encoded) != state:
            raise AssertionError("boundary-defect frontier failed exact round trip")
        round_trips += 1
        if recognize_state(state).accepted:
            compact = encode_compact_boundary_defect_frontier(state)
            if expand_compact_boundary_defect_frontier(compact) != state:
                raise AssertionError("compact boundary-defect frontier failed exact round trip")
            compact_round_trips += 1
    return {
        "states": len(values),
        "accepted": accepted,
        "excluded": len(values) - accepted,
        "acceptance": accepted == len(values),
        "lossless_round_trips": round_trips,
        "carrier_grammar_accepted": carrier_accepted,
        "compact_one_carrier_round_trips": compact_round_trips,
        "maximum_exception_count": max(exception_counts, default=0),
        "interior_violation_occurrences": sum(violations.values()),
        "interior_violation_indices": {str(index): count for index, count in sorted(violations.items())},
        "motif_control_counts": {
            "distinct_dominant_motifs": len(dominant),
            "dominant_state_occurrences": sum(dominant.values()),
            "distinct_boundary_controls": len(controls),
            "boundary_control_occurrences": sum(controls.values()),
        },
        "dominant_motifs": {_atom_id(atom): count for atom, count in sorted(dominant.items())},
        "boundary_controls": {_atom_id(atom): count for atom, count in sorted(controls.items())},
    }


def _affine_transition_closure(traces: dict[int, list[FrontierState]]) -> dict:
    """Census finite adjacent-width row edges whose endpoints stay in grammar."""
    pairs = {}
    all_closed = True
    for source in AFFINE_WIDTHS[:-1]:
        target = source + 3
        source_states = traces[source]
        target_states = traces[target]
        source_acceptance = [
            not interior_violation_indices(packet_atoms(state)) for state in source_states
        ]
        target_acceptance = [
            not interior_violation_indices(packet_atoms(state)) for state in target_states
        ]
        source_closed_edges = sum(
            left and right for left, right in zip(source_acceptance, source_acceptance[1:])
        )
        target_closed_edges = sum(
            left and right for left, right in zip(target_acceptance, target_acceptance[1:])
        )
        closed = source_closed_edges == source and target_closed_edges == target
        all_closed &= closed
        pairs[f"n{source}-to-n{target}"] = {
            "source_row_edges_with_accepted_endpoints": source_closed_edges,
            "source_row_edges": source,
            "target_row_edges_with_accepted_endpoints": target_closed_edges,
            "target_row_edges": target,
            "finite_endpoint_closure": closed,
        }
    return {
        "definition": "for each generated adjacent-width pair, every fixed affine row edge has both endpoint packet words accepted",
        "all_observed_adjacent_width_pairs_closed": all_closed,
        "pairs": pairs,
    }


def build_artifact() -> dict:
    corridors = {width: build_equality_corridor(width) for width in CORRIDOR_WIDTHS}
    affine_traces = {
        width: replay_trace(residue_two_affine_pattern(width)) for width in AFFINE_WIDTHS
    }
    sources = {
        f"n{width}-complete-equality-corridor": census_states(equality_states(corridor))
        for width, corridor in corridors.items()
    }
    for width in FIXED_EQUALITY_WIDTHS:
        sources[f"n{width}-fixed-equality-trace"] = census_states(
            replay_trace(residue_two_explicit_pattern(width))
        )
    sources["n17-fixed-near-equality-179-U-trace"] = census_states(affine_traces[17])
    affine_sources = {
        f"n{width}-affine-generated-trace": census_states(states)
        for width, states in affine_traces.items()
    }
    all_affine_accepted = all(item["acceptance"] for item in affine_sources.values())
    return {
        "schema": SCHEMA,
        "scope": {
            "exact_codec": True,
            "complete_equality_corridors": list(CORRIDOR_WIDTHS),
            "fixed_equality_traces": list(FIXED_EQUALITY_WIDTHS),
            "near_equality_control": {"width": 17, "u_count": 179},
            "affine_generated_widths": list(AFFINE_WIDTHS),
            "affine_family_finite_closure_observed": all_affine_accepted,
            "equality_language_coverage_proved": False,
            "theorem_or_zero_slack_certificate": False,
        },
        "definitions": {
            "atom": "previous three-bit packet word, independently OUT-rooted three-face restriction, and local component single/open/carry/close plus carry-in/carry-out flags",
            "global_channel": "a separate canonical lossless CarrierRecord retains global component labels, exact face slots, and checked cut carriers",
            "compact_global_channel": "under the one-carrier rule, left-face mode and packet open/carry/close roles reconstruct global labels without storing CarrierRecord",
            "dominant": "maximum atom multiplicity with lexicographically least deterministic tie break",
            "boundary_exceptions": "non-dominant atoms are permitted only at the first two and final four packet indices",
            "constant_bound": "at most six exception positions, independent of width",
            "acceptance": "the canonical atom word has no non-dominant occurrence outside the permitted boundary positions",
        },
        "sources": sources,
        "affine_family": {
            "all_generated_traces_accepted": all_affine_accepted,
            "maximum_exception_count": max(
                item["maximum_exception_count"] for item in affine_sources.values()
            ),
            "interior_violation_occurrences": sum(
                item["interior_violation_occurrences"] for item in affine_sources.values()
            ),
            "states": sum(item["states"] for item in affine_sources.values()),
            "traces": affine_sources,
        },
        "row_transition_closure": _affine_transition_closure(affine_traces),
        "claims": {
            "exact_codec_and_carrier_round_trip": "proved by validation for every accepted input and exercised on every listed state",
            "affine_family_closure": "every generated state at n=17..119 is accepted, with no interior violations; this is finite generator evidence, not an arbitrary-width induction",
            "equality_language_coverage": "unproved; only n=5 and n=8 are complete equality corridors, while n=11 and n=14 are fixed traces",
        },
        "limitations": [
            "Outside the checked one-carrier discipline, the bounded atom word requires the separate carrier record (or equivalent global labels) for exact frontier expansion.",
            "The affine census stops at n=119; its zero interior violations do not prove arbitrary-width closure.",
            "Complete equality-language coverage is not claimed beyond the enumerated n=5 and n=8 corridors.",
            "Adjacent-width row closure is an endpoint census of fixed generated traces, not a language-level transition induction.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_affine_motif_grammar.py",
            "command": [
                "python3", "-B", "-m",
                                 'analysis.residue_certificates.residue_two_affine_motif_grammar',
                "--output", "analysis/residue_two_affine_motif_grammar.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if args.output is None or not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"affine boundary-defect grammar matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


__all__ = [
    "AFFINE_WIDTHS",
    "BoundaryDefectAtom",
    "BoundaryDefectFrontier",
    "BoundaryDefectWord",
    "CompactBoundaryDefectFrontier",
    "InteriorDefectError",
    "PacketCarrierRole",
    "boundary_indices",
    "build_artifact",
    "canonical_dominant",
    "census_states",
    "encode_boundary_defect_frontier",
    "encode_boundary_defect_word",
    "encode_compact_boundary_defect_frontier",
    "expand_boundary_defect_frontier",
    "expand_boundary_defect_word",
    "expand_compact_boundary_defect_frontier",
    "interior_violation_indices",
    "packet_atoms",
    "replay_trace",
]


if __name__ == "__main__":
    main()
