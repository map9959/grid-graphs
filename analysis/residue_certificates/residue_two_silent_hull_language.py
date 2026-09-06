#!/usr/bin/env python3
"""Width-independent one-hull packet language with silent carrier passage.

The codec is lossless for every residue-two frontier whose non-OUT occurrence
hulls have face-cut width at most one.  Its word scan has finite control: one
active carrier, a finite packet atom, and fresh-component/cost counters.  This
is a conditional structural coverage theorem, not a proof that low-curvature
frontiers have hull width one.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Sequence

from analysis.residue_certificates.residue_two_local_motif_grammar import (
    maximum_face_cut_open_width,
)
from analysis.tiles.symbolic_packet_frontier import encode_frontier
from analysis.tiles.tile_grammar import FrontierState, advance_row


@dataclass(frozen=True, order=True, slots=True)
class HullRole:
    local_label: int
    carries_in: bool
    carries_out: bool


@dataclass(frozen=True, order=True, slots=True)
class SilentHullAtom:
    """Finite packet symbol; ``silent_carry`` preserves an absent hull."""

    previous_word: int
    rooted_restriction: tuple[int, ...]
    roles: tuple[HullRole, ...]
    silent_carry: bool = False

    def __post_init__(self) -> None:
        if type(self.previous_word) is not int or not 0 <= self.previous_word < 8:
            raise ValueError("previous packet word must be a three-bit integer")
        if len(self.rooted_restriction) not in (0, 3):
            raise ValueError("a packet restriction must be empty or have three labels")
        seen = {0}
        for label in self.rooted_restriction:
            if type(label) is not int or label < 0:
                raise ValueError("packet labels must be nonnegative integers")
            if label not in seen:
                if label != len(seen):
                    raise ValueError("packet restriction is not canonically rooted")
                seen.add(label)
        local = set(self.rooted_restriction) - {0}
        if tuple(sorted(self.roles)) != self.roles or {
            role.local_label for role in self.roles
        } != local:
            raise ValueError("roles must describe every local non-OUT component")
        if any(role.local_label <= 0 for role in self.roles):
            raise ValueError("OUT cannot have a hull role")
        incoming = sum(role.carries_in for role in self.roles) + self.silent_carry
        outgoing = sum(role.carries_out for role in self.roles) + self.silent_carry
        if incoming > 1 or outgoing > 1:
            raise ValueError("an atom cannot carry concurrent hulls")
        if self.silent_carry and any(
            role.carries_in or role.carries_out for role in self.roles
        ):
            raise ValueError("a silent carrier cannot also occur in the packet")


@dataclass(frozen=True, slots=True)
class SilentHullFrontier:
    row_index: int
    previous_cap_bits: tuple[int, int]
    left_face_role: str
    atoms: tuple[SilentHullAtom, ...]
    u_cost: int
    cycle_excess: int

    @property
    def packet_length(self) -> int:
        return len(self.atoms)

    @property
    def width(self) -> int:
        return 3 * self.packet_length + 2


@dataclass(frozen=True, slots=True)
class AffineRowCounters:
    """Exact row deltas, each obtained by sums of finite local observations."""

    packets: int
    u: int
    horizontal_edges: int
    vertical_edges: int
    source_components: int
    target_components: int
    rank: int
    cycles: int
    weight: int


@dataclass(frozen=True, slots=True)
class SilentHullCodecDecision:
    """Structured result for the exact conditional frontier codec."""

    accepted: bool
    maximum_face_cut_width: int
    encoded: SilentHullFrontier | None
    reason: str | None


def _root(labels: tuple[int, int, int]) -> tuple[tuple[int, int, int], dict[int, int]]:
    names = {0: 0}
    rooted = []
    for label in labels:
        names.setdefault(label, len(names))
        rooted.append(names[label])
    return tuple(rooted), names


def encode_silent_hull_frontier(state: FrontierState) -> SilentHullFrontier:
    """Encode exactly, provided occurrence hulls never overlap at a face cut."""
    symbolic = encode_frontier(state)
    if maximum_face_cut_open_width(state) > 1:
        raise ValueError("frontier has concurrent occurrence hulls")
    if len(state.partition) == 1:
        return SilentHullFrontier(
            state.row_index,
            symbolic.previous_cap_bits,
            "absent",
            tuple(SilentHullAtom(word, (), ()) for word in symbolic.previous_packet_words),
            state.u_cost,
            state.cycle_excess,
        )

    faces = state.partition[1:]
    positions = {
        component: tuple(index for index, value in enumerate(faces) if value == component)
        for component in set(faces) - {0}
    }
    left_component = faces[0]
    if left_component == 0:
        left_role = "out"
    elif positions[left_component][-1] > 0:
        left_role = "open"
    else:
        left_role = "single"

    atoms = []
    for packet, (word, labels) in enumerate(
        zip(symbolic.previous_packet_words, symbolic.packet_face_labels)
    ):
        start = 1 + 3 * packet
        end = start + 2
        restriction, local = _root(labels)
        roles = tuple(
            sorted(
                HullRole(
                    local[component],
                    positions[component][0] < start,
                    positions[component][-1] > end,
                )
                for component in set(labels) - {0}
            )
        )
        silent = any(
            slots[0] < start and slots[-1] > end and component not in labels
            for component, slots in positions.items()
        )
        atoms.append(SilentHullAtom(word, restriction, roles, silent))
    encoded = SilentHullFrontier(
        state.row_index,
        symbolic.previous_cap_bits,
        left_role,
        tuple(atoms),
        state.u_cost,
        state.cycle_excess,
    )
    if decode_silent_hull_frontier(encoded) != state:
        raise AssertionError("silent-hull encoding failed its exact round trip")
    return encoded


def classify_silent_hull_frontier(state: FrontierState) -> SilentHullCodecDecision:
    """Classify the sole current codec boundary without parsing exceptions."""
    width = maximum_face_cut_open_width(state)
    if width > 1:
        return SilentHullCodecDecision(
            False, width, None, "concurrent occurrence hulls"
        )
    return SilentHullCodecDecision(
        True, width, encode_silent_hull_frontier(state), None
    )


def decode_silent_hull_frontier(encoded: SilentHullFrontier) -> FrontierState:
    """Expand using one active-carrier bit and an affine fresh-label counter."""
    if not isinstance(encoded, SilentHullFrontier) or encoded.packet_length < 1:
        raise ValueError("silent-hull frontier requires at least one packet")
    n = encoded.width
    if not 0 <= encoded.row_index <= n:
        raise ValueError("row index does not fit the encoded width")
    terminal_shape = encoded.row_index in (0, n)
    if (encoded.left_face_role == "absent") != terminal_shape:
        raise ValueError("frontier face presence disagrees with the row index")
    if len(encoded.previous_cap_bits) != 2 or any(
        type(bit) is not int or bit not in (0, 1) for bit in encoded.previous_cap_bits
    ):
        raise ValueError("previous cap bits must be bits")
    if encoded.left_face_role == "absent":
        if any(atom.rooted_restriction or atom.roles or atom.silent_carry for atom in encoded.atoms):
            raise ValueError("an absent frontier cannot carry face components")
        partition = (0,)
    else:
        if encoded.left_face_role not in ("out", "single", "open"):
            raise ValueError("unknown left-face role")
        next_label = 1
        if encoded.left_face_role == "out":
            faces = [0]
            active = None
        else:
            faces = [next_label]
            active = next_label if encoded.left_face_role == "open" else None
            next_label += 1
        for atom in encoded.atoms:
            if len(atom.rooted_restriction) != 3:
                raise ValueError("an open frontier needs three labels per packet")
            incoming = [role for role in atom.roles if role.carries_in]
            if atom.silent_carry:
                if active is None:
                    raise ValueError("silent packet has no incoming hull")
                faces.extend(0 if label == 0 else next_label + label - 1 for label in atom.rooted_restriction)
                next_label += len(set(atom.rooted_restriction) - {0})
                continue
            if bool(incoming) != (active is not None):
                raise ValueError("packet incoming role disagrees with active hull")
            role_by_label = {role.local_label: role for role in atom.roles}
            names = {0: 0}
            outgoing = None
            for label in atom.rooted_restriction:
                if label not in names:
                    role = role_by_label[label]
                    if role.carries_in:
                        names[label] = active
                    else:
                        names[label] = next_label
                        next_label += 1
                    if role.carries_out:
                        outgoing = names[label]
                faces.append(names[label])
            active = outgoing
        if active is not None:
            raise ValueError("a hull remains active after the final packet")
        partition = (0, *faces)

    mask = encoded.previous_cap_bits[0]
    for packet, atom in enumerate(encoded.atoms):
        mask |= atom.previous_word << (1 + 3 * packet)
    mask |= encoded.previous_cap_bits[1] << (n - 1)
    return FrontierState(
        n,
        encoded.row_index,
        mask,
        partition,
        encoded.u_cost,
        encoded.cycle_excess,
    )


def _mask(cap_bits: tuple[int, int], packets: Sequence[int]) -> int:
    n = 3 * len(packets) + 2
    value = cap_bits[0]
    for index, packet in enumerate(packets):
        if type(packet) is not int or not 0 <= packet < 8:
            raise ValueError("action packets must be three-bit integers")
        value |= packet << (1 + 3 * index)
    return value | (cap_bits[1] << (n - 1))


def certify_silent_hull_transition(
    source: SilentHullFrontier,
    action_cap_bits: tuple[int, int],
    action_packets: Sequence[int],
    target: SilentHullFrontier,
) -> AffineRowCounters:
    """Check an exact row edge and return its local-sum affine counters."""
    packets = tuple(action_packets)
    if len(packets) != source.packet_length or target.packet_length != source.packet_length:
        raise ValueError("source, action, and target packet lengths differ")
    if len(action_cap_bits) != 2 or any(bit not in (0, 1) for bit in action_cap_bits):
        raise ValueError("action cap bits must be bits")
    incoming = decode_silent_hull_frontier(source)
    outgoing = decode_silent_hull_frontier(target)
    action = _mask(action_cap_bits, packets)
    actual = advance_row(incoming, action)
    if actual is None or actual != outgoing:
        raise ValueError("claimed target is not the exact row successor")

    bits = (action_cap_bits[0], *(bit for packet in packets for bit in (
        packet & 1, (packet >> 1) & 1, (packet >> 2) & 1
    )), action_cap_bits[1])
    previous_bits = tuple((incoming.previous_u_mask >> index) & 1 for index in range(incoming.n))
    u = sum(bits)
    horizontal = sum(left * right for left, right in zip(bits, bits[1:]))
    vertical = sum(left * right for left, right in zip(previous_bits, bits))
    source_components = len(set(incoming.partition)) - 1
    target_components = len(set(outgoing.partition)) - 1
    new_faces = 0 if outgoing.row_index == outgoing.n else outgoing.n - 1
    rank = new_faces + source_components - target_components
    cycles = horizontal + vertical - rank
    counters = AffineRowCounters(
        len(packets), u, horizontal, vertical, source_components,
        target_components, rank, cycles, 3 * u - 2 * rank - 1,
    )
    if cycles != outgoing.cycle_excess - incoming.cycle_excess:
        raise AssertionError("local affine counters disagree with exact cycle semantics")
    return counters


def finite_structural_atom_alphabet() -> frozenset[SilentHullAtom]:
    """Enumerate the finite structural alphabet, including previous-row bits."""
    restrictions = [()]
    words = [()]
    for _ in range(3):
        words = [(*word, label) for word in words for label in range(max(word, default=0) + 2)]
    restrictions.extend(words)
    atoms = set()
    for previous, restriction in product(range(8), restrictions):
        labels = sorted(set(restriction) - {0})
        for flags in product(product((False, True), repeat=2), repeat=len(labels)):
            roles = tuple(HullRole(label, *flag) for label, flag in zip(labels, flags))
            for silent in (False, True):
                try:
                    atoms.add(SilentHullAtom(previous, restriction, roles, silent))
                except ValueError:
                    pass
    return frozenset(atoms)


__all__ = [
    "AffineRowCounters",
    "HullRole",
    "SilentHullAtom",
    "SilentHullCodecDecision",
    "SilentHullFrontier",
    "certify_silent_hull_transition",
    "classify_silent_hull_frontier",
    "decode_silent_hull_frontier",
    "encode_silent_hull_frontier",
    "finite_structural_atom_alphabet",
]
