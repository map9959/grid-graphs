"""Public packet-by-packet cursor for exact row frontier transitions."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from analysis.tiles.tile_grammar import (
    ROW_PACKET_ALPHABET,
    FrontierState,
    PartialRowState,
    RowPacketTransition,
    _append_row_bits,
    _initial_partial_row,
    _partial_row_has_sealed_component,
    _row_node_order,
    canonical_partition,
    dsu_from_partition,
)


@dataclass(frozen=True, slots=True)
class PacketRowCursor:
    """Immutable exact state at a packet boundary within one row."""

    incoming: FrontierState
    partial: PartialRowState

    @property
    def u_cost(self) -> int:
        """Cumulative U-cost, including rows preceding this cursor."""

        return self.incoming.u_cost + self.partial.row_u_cost

    @property
    def cycle_excess(self) -> int:
        """Cumulative cycle excess, including rows preceding this cursor."""

        return self.incoming.cycle_excess + self.partial.cycle_excess


def start_row(incoming: FrontierState, prefix: str) -> PacketRowCursor | None:
    """Start a row and consume its fixed prefix."""

    if incoming.finished:
        raise ValueError("cannot advance a finished frontier")
    partial = _append_row_bits(incoming, _initial_partial_row(incoming), prefix)
    if _partial_row_has_sealed_component(incoming, partial):
        return None
    return PacketRowCursor(incoming, partial)


def append_packet(
    cursor: PacketRowCursor,
    name: str,
    packet_alphabet: Mapping[str, str] = ROW_PACKET_ALPHABET,
) -> PacketRowCursor | None:
    """Consume one named packet, preserving its row-local metadata."""

    if name not in packet_alphabet:
        raise ValueError(f"unknown packet name: {name!r}")
    value = packet_alphabet[name]
    child = _append_row_bits(cursor.incoming, cursor.partial, value)
    child = PartialRowState(
        columns=child.columns,
        right_u=child.right_u,
        row_mask=child.row_mask,
        row_u_cost=child.row_u_cost,
        packet_charge=cursor.partial.packet_charge + value.count("U") - 2,
        h_count=cursor.partial.h_count + (value.count("U") == 3),
        partition=child.partition,
        cycle_excess=child.cycle_excess,
        packet_names=(*cursor.partial.packet_names, name),
    )
    if _partial_row_has_sealed_component(cursor.incoming, child):
        return None
    return PacketRowCursor(cursor.incoming, child)


def finish_row(cursor: PacketRowCursor, suffix: str) -> RowPacketTransition | None:
    """Consume the fixed suffix and construct the exact outgoing frontier."""

    child = _append_row_bits(cursor.incoming, cursor.partial, suffix)
    if child.columns != cursor.incoming.n:
        raise ValueError("row does not span the grid width")
    if _partial_row_has_sealed_component(cursor.incoming, child):
        return None

    order, _, new = _row_node_order(cursor.incoming)
    dsu = dsu_from_partition(order, child.partition)
    partition = canonical_partition(dsu, [("out", 0), *new])
    if cursor.incoming.row_index + 1 == cursor.incoming.n and partition != (0,):
        return None

    outgoing = FrontierState(
        n=cursor.incoming.n,
        row_index=cursor.incoming.row_index + 1,
        previous_u_mask=child.row_mask,
        partition=partition,
        u_cost=cursor.incoming.u_cost + child.row_u_cost,
        cycle_excess=cursor.incoming.cycle_excess + child.cycle_excess,
    )
    return RowPacketTransition(
        outgoing=outgoing,
        row_mask=child.row_mask,
        packet_names=child.packet_names,
        packet_charge=child.packet_charge,
        h_count=child.h_count,
    )


def verify_packet_row(
    incoming: FrontierState,
    prefix: str,
    packet_names: Sequence[str],
    suffix: str,
    packet_alphabet: Mapping[str, str] = ROW_PACKET_ALPHABET,
) -> tuple[tuple[PacketRowCursor, ...], RowPacketTransition | None]:
    """Replay a named packet row and return all reachable cursor checkpoints."""

    unknown = [name for name in packet_names if name not in packet_alphabet]
    if unknown:
        raise ValueError(f"unknown packet names: {unknown!r}")
    values = tuple(packet_alphabet[name] for name in packet_names)
    if any(bit not in ".U" for bits in (prefix, *values, suffix) for bit in bits):
        raise ValueError("fixed bits and packet values must contain only '.' and 'U'")
    if len(prefix) + sum(map(len, values)) + len(suffix) != incoming.n:
        raise ValueError("fixed bits and packets do not span the grid width")

    cursor = start_row(incoming, prefix)
    if cursor is None:
        return (), None
    checkpoints = [cursor]
    for name in packet_names:
        cursor = append_packet(cursor, name, packet_alphabet)
        if cursor is None:
            return tuple(checkpoints), None
        checkpoints.append(cursor)
    return tuple(checkpoints), finish_row(cursor, suffix)


__all__ = [
    "PacketRowCursor",
    "append_packet",
    "finish_row",
    "start_row",
    "verify_packet_row",
]
