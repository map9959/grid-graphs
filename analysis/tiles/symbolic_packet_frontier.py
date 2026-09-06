"""Exact variable-length symbolic words for residue-two row frontiers.

This is a lossless, variable-length word/right-congruence representation of
``FrontierState``.  It is not bounded finite control, and it does not provide
the missing lower-bound potential: both the packet word and rooted component
word grow with the grid width.

For width ``n = 3k + 2``, OUT is the implicit rooted component label 0.  The
remaining ``n - 1`` face labels are stored as one left-face label followed by
``k`` ordered groups of three labels.  Previous-row U bits use the analogous
two cap bits and ``k`` ordered three-bit packet words.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from analysis.tiles.row_packet_transition import verify_packet_row
from analysis.tiles.tile_grammar import FrontierState


ALL_THREE_BIT_PACKETS = {
    f"P{value}": "".join(
        "U" if value & (1 << offset) else "." for offset in range(3)
    )
    for value in range(8)
}


def _is_canonical_rooted(labels: tuple[int, ...]) -> bool:
    if not labels or labels[0] != 0:
        return False
    renaming: dict[int, int] = {}
    canonical = []
    for label in labels:
        if type(label) is not int or label < 0:
            return False
        if label not in renaming:
            renaming[label] = len(renaming)
        canonical.append(renaming[label])
    return tuple(canonical) == labels


@dataclass(frozen=True, slots=True)
class SymbolicPacketFrontier:
    """Immutable exact frontier encoded as ordered cap, packet, and label words."""

    row_index: int
    previous_cap_bits: tuple[int, int]
    previous_packet_words: tuple[int, ...]
    left_face_label: int | None
    packet_face_labels: tuple[tuple[int, int, int], ...]
    u_cost: int
    cycle_excess: int

    def __post_init__(self) -> None:
        if type(self.row_index) is not int or not 0 <= self.row_index <= self.width:
            raise ValueError("row index does not fit the derived width")
        if (
            not isinstance(self.previous_cap_bits, tuple)
            or len(self.previous_cap_bits) != 2
            or any(type(bit) is not int or bit not in (0, 1) for bit in self.previous_cap_bits)
        ):
            raise ValueError("previous cap bits must be an ordered pair of bits")
        if not isinstance(self.previous_packet_words, tuple) or any(
            type(word) is not int or not 0 <= word < 8
            for word in self.previous_packet_words
        ):
            raise ValueError("previous packet words must be immutable three-bit values")
        if not isinstance(self.packet_face_labels, tuple) or any(
            not isinstance(group, tuple) or len(group) != 3
            for group in self.packet_face_labels
        ):
            raise ValueError("packet face labels must be immutable three-face groups")
        if type(self.u_cost) is not int or self.u_cost < 0:
            raise ValueError("U cost must be a nonnegative integer")
        if type(self.cycle_excess) is not int or self.cycle_excess < 0:
            raise ValueError("cycle excess must be a nonnegative integer")

        has_faces = 0 < self.row_index < self.width
        if has_faces:
            if type(self.left_face_label) is not int:
                raise ValueError("an open frontier requires a left-face label")
            if len(self.packet_face_labels) != self.packet_count:
                raise ValueError("face-label groups do not match the packet count")
            labels = (0, self.left_face_label, *self.face_labels_after_left)
            if not _is_canonical_rooted(labels):
                raise ValueError("rooted component labels are not canonical")
        elif self.left_face_label is not None or self.packet_face_labels:
            raise ValueError("initial and terminal frontiers cannot contain face labels")

        if self.row_index == 0:
            if any(self.previous_cap_bits) or any(self.previous_packet_words):
                raise ValueError("initial frontier previous-row bits must be zero")
            if self.u_cost or self.cycle_excess:
                raise ValueError("initial frontier cumulative values must be zero")

    @property
    def packet_count(self) -> int:
        return len(self.previous_packet_words)

    @property
    def width(self) -> int:
        return 3 * self.packet_count + 2

    @property
    def face_labels_after_left(self) -> tuple[int, ...]:
        return tuple(label for group in self.packet_face_labels for label in group)


def encode_frontier(state: FrontierState) -> SymbolicPacketFrontier:
    """Encode a canonical residue-two frontier without losing any field."""

    if type(state.n) is not int or state.n < 2 or state.n % 3 != 2:
        raise ValueError("frontier width must have the form n = 3k + 2")
    if type(state.row_index) is not int or not 0 <= state.row_index <= state.n:
        raise ValueError("frontier row index does not fit its width")
    if type(state.previous_u_mask) is not int or not 0 <= state.previous_u_mask < 1 << state.n:
        raise ValueError("previous-row mask does not fit the frontier width")
    expected_labels = 1 if state.row_index in (0, state.n) else state.n
    if len(state.partition) != expected_labels:
        raise ValueError("frontier partition has the wrong size")
    if not _is_canonical_rooted(state.partition):
        raise ValueError("frontier partition is not canonically rooted at OUT")

    packet_count = (state.n - 2) // 3
    cap_bits = (state.previous_u_mask & 1, (state.previous_u_mask >> (state.n - 1)) & 1)
    packet_words = tuple(
        (state.previous_u_mask >> (1 + 3 * packet)) & 0b111
        for packet in range(packet_count)
    )
    if state.row_index in (0, state.n):
        left_label = None
        label_groups: tuple[tuple[int, int, int], ...] = ()
    else:
        left_label = state.partition[1]
        label_groups = tuple(
            state.partition[2 + 3 * packet : 5 + 3 * packet]
            for packet in range(packet_count)
        )
    return SymbolicPacketFrontier(
        row_index=state.row_index,
        previous_cap_bits=cap_bits,
        previous_packet_words=packet_words,
        left_face_label=left_label,
        packet_face_labels=label_groups,
        u_cost=state.u_cost,
        cycle_excess=state.cycle_excess,
    )


def decode_frontier(symbolic: SymbolicPacketFrontier) -> FrontierState:
    """Decode the exact ``FrontierState`` represented by ``symbolic``."""

    if not isinstance(symbolic, SymbolicPacketFrontier):
        raise TypeError("symbolic must be a SymbolicPacketFrontier")
    mask = symbolic.previous_cap_bits[0]
    for packet, word in enumerate(symbolic.previous_packet_words):
        mask |= word << (1 + 3 * packet)
    mask |= symbolic.previous_cap_bits[1] << (symbolic.width - 1)
    partition = (
        (0, symbolic.left_face_label, *symbolic.face_labels_after_left)
        if 0 < symbolic.row_index < symbolic.width
        else (0,)
    )
    return FrontierState(
        n=symbolic.width,
        row_index=symbolic.row_index,
        previous_u_mask=mask,
        partition=partition,
        u_cost=symbolic.u_cost,
        cycle_excess=symbolic.cycle_excess,
    )


def advance_symbolic_row(
    symbolic: SymbolicPacketFrontier,
    left_bit: int,
    packet_words: Sequence[int],
    right_bit: int,
) -> SymbolicPacketFrontier | None:
    """Advance one exact symbolic row through all-eight-value packet replay."""

    if type(left_bit) is not int or left_bit not in (0, 1):
        raise ValueError("left cap must be a bit")
    if type(right_bit) is not int or right_bit not in (0, 1):
        raise ValueError("right cap must be a bit")
    words = tuple(packet_words)
    if len(words) != symbolic.packet_count:
        raise ValueError("current packet count does not match the symbolic width")
    if any(type(word) is not int or not 0 <= word < 8 for word in words):
        raise ValueError("current packet words must be three-bit values")

    names = tuple(f"P{word}" for word in words)
    _, transition = verify_packet_row(
        decode_frontier(symbolic),
        "U" if left_bit else ".",
        names,
        "U" if right_bit else ".",
        ALL_THREE_BIT_PACKETS,
    )
    return None if transition is None else encode_frontier(transition.outgoing)


__all__ = [
    "ALL_THREE_BIT_PACKETS",
    "SymbolicPacketFrontier",
    "advance_symbolic_row",
    "decode_frontier",
    "encode_frontier",
]
