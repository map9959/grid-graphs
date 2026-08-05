"""Exact weight and working-debt certificates for streamed packet rows."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction

from proof_oriented_identities import tile_grammar_row_deltas
from row_packet_transition import PacketRowCursor, finish_row
from tile_grammar import (
    ROW_PACKET_ALPHABET,
    FrontierState,
    _append_row_bits,
    _initial_partial_row,
    _partial_row_has_sealed_component,
    advance_row,
)


@dataclass(frozen=True, slots=True)
class PacketSegmentDeltas:
    """Exact additive channels contributed by one contiguous row segment."""

    dU: int
    dHorizontal: int
    dVertical: int
    dEdges: int
    dCycles: int
    dRank: int
    new_faces: int
    working_debt_delta: int
    weight: Fraction


@dataclass(frozen=True, slots=True)
class PacketStep:
    """An immutable accepted segment and its resulting packet cursor."""

    before: PacketRowCursor
    cursor: PacketRowCursor
    bits: str
    kind: str
    name: str | None
    charge: Fraction
    deltas: PacketSegmentDeltas

    @property
    def after(self) -> PacketRowCursor:
        return self.cursor


def _exact_charge(value: Fraction) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if type(value) is int:
        return Fraction(value)
    raise TypeError("charge must be an integer or Fraction")


def _frontier_debt(state: FrontierState) -> int:
    """Number of live frontier components not containing OUT."""

    return len(set(state.partition)) - 1


def begin_row(incoming: FrontierState) -> PacketRowCursor:
    """Return the exact zero-column cursor for a new row."""

    if incoming.finished:
        raise ValueError("cannot advance a finished frontier")
    return PacketRowCursor(incoming, _initial_partial_row(incoming))


def append_segment_exact(
    cursor: PacketRowCursor,
    bits: str,
    kind: str,
    name: str | None = None,
    charge: Fraction = Fraction(0),
) -> PacketStep | None:
    """Consume a segment and return all exact local deltas, or reject sealing.

    Ordinary prefix, packet, and suffix segments have zero charge.  A row-close
    event is a zero-width segment at the completed row and has charge one.
    """

    charge = _exact_charge(charge)
    if not kind:
        raise ValueError("segment kind must be nonempty")
    if kind == "row_close":
        if bits:
            raise ValueError("row-close event must have zero width")
        if cursor.partial.columns != cursor.incoming.n:
            raise ValueError("row-close event requires a complete row")
        if charge != 1:
            raise ValueError("row-close event must have charge 1")
    elif charge:
        raise ValueError("row charge is allowed only at row close")

    before = cursor.partial
    child = _append_row_bits(cursor.incoming, before, bits)
    if _partial_row_has_sealed_component(cursor.incoming, child):
        return None

    start = before.columns
    end = child.columns
    segment_mask = ((1 << end) - 1) ^ ((1 << start) - 1)
    current_mask = child.row_mask
    horizontal = sum(
        bool(current_mask & (1 << (column - 1)))
        and bool(current_mask & (1 << column))
        for column in range(max(1, start), end)
    )
    vertical = (
        cursor.incoming.previous_u_mask & current_mask & segment_mask
    ).bit_count()
    d_u = child.row_u_cost - before.row_u_cost
    d_cycles = child.cycle_excess - before.cycle_excess
    d_edges = horizontal + vertical
    d_rank = d_edges - d_cycles
    if d_cycles < 0 or not 0 <= d_rank <= d_edges:
        raise AssertionError("partial-row oracle produced invalid graphic-rank deltas")

    has_new_frontier = cursor.incoming.row_index + 1 < cursor.incoming.n
    new_faces = (
        max(0, min(end, cursor.incoming.n - 1) - min(start, cursor.incoming.n - 1))
        if has_new_frontier
        else 0
    )
    debt_delta = new_faces - d_rank
    deltas = PacketSegmentDeltas(
        dU=d_u,
        dHorizontal=horizontal,
        dVertical=vertical,
        dEdges=d_edges,
        dCycles=d_cycles,
        dRank=d_rank,
        new_faces=new_faces,
        working_debt_delta=debt_delta,
        weight=Fraction(3 * d_u - 2 * d_rank) - charge,
    )
    return PacketStep(
        before=cursor,
        cursor=PacketRowCursor(cursor.incoming, child),
        bits=bits,
        kind=kind,
        name=name,
        charge=charge,
        deltas=deltas,
    )


def _sum_deltas(steps: Sequence[PacketStep]) -> PacketSegmentDeltas:
    return PacketSegmentDeltas(
        dU=sum(step.deltas.dU for step in steps),
        dHorizontal=sum(step.deltas.dHorizontal for step in steps),
        dVertical=sum(step.deltas.dVertical for step in steps),
        dEdges=sum(step.deltas.dEdges for step in steps),
        dCycles=sum(step.deltas.dCycles for step in steps),
        dRank=sum(step.deltas.dRank for step in steps),
        new_faces=sum(step.deltas.new_faces for step in steps),
        working_debt_delta=sum(step.deltas.working_debt_delta for step in steps),
        weight=sum((step.deltas.weight for step in steps), Fraction(0)),
    )


@dataclass(frozen=True, slots=True)
class PacketRowWeightCertificate:
    """Verified decomposition of one accepted row into exact segment weights."""

    incoming: FrontierState
    outgoing: FrontierState
    steps: tuple[PacketStep, ...]
    totals: PacketSegmentDeltas
    debt_in: int
    debt_out: int

    @classmethod
    def verify(
        cls,
        incoming: FrontierState,
        prefix: str,
        packet_names: Sequence[str],
        suffix: str,
        packet_alphabet: Mapping[str, str] = ROW_PACKET_ALPHABET,
    ) -> PacketRowWeightCertificate | None:
        """Replay and verify prefix, named packets, suffix, and row close."""

        unknown = [name for name in packet_names if name not in packet_alphabet]
        if unknown:
            raise ValueError(f"unknown packet names: {unknown!r}")
        packet_bits = tuple(packet_alphabet[name] for name in packet_names)
        all_bits = (prefix, *packet_bits, suffix)
        if any(bit not in ".U" for bits in all_bits for bit in bits):
            raise ValueError(
                "fixed bits and packet values must contain only '.' and 'U'"
            )
        if sum(map(len, all_bits)) != incoming.n:
            raise ValueError("fixed bits and packets do not span the grid width")

        cursor = begin_row(incoming)
        steps: list[PacketStep] = []
        segments = [(prefix, "prefix", None)]
        segments.extend(
            (bits, "packet", name) for name, bits in zip(packet_names, packet_bits)
        )
        segments.append((suffix, "suffix", None))
        for bits, kind, name in segments:
            step = append_segment_exact(cursor, bits, kind, name)
            if step is None:
                return None
            steps.append(step)
            cursor = step.cursor

        transition = finish_row(cursor, "")
        if transition is None:
            return None
        close = append_segment_exact(cursor, "", "row_close", charge=Fraction(1))
        assert close is not None
        steps.append(close)

        direct = advance_row(incoming, cursor.partial.row_mask)
        if direct is None or direct != transition.outgoing:
            raise AssertionError("partial-row certificate disagrees with advance_row")
        row = tile_grammar_row_deltas(incoming, cursor.partial.row_mask, direct)
        totals = _sum_deltas(steps)
        expected = (
            row.u_count,
            row.u_count - row.horizontal_runs,
            row.vertical_edges,
            row.edge_delta,
            row.cycle_delta,
            row.rank_delta,
        )
        actual = (
            totals.dU,
            totals.dHorizontal,
            totals.dVertical,
            totals.dEdges,
            totals.dCycles,
            totals.dRank,
        )
        if actual != expected:
            raise AssertionError(
                f"segment totals disagree with row deltas: {actual} != {expected}"
            )
        if totals.weight != Fraction(3 * row.u_count - 2 * row.rank_delta - 1):
            raise AssertionError(
                "segment weights do not equal the exact charged row weight"
            )

        debt_in = _frontier_debt(incoming)
        debt_out = _frontier_debt(direct)
        if debt_out - debt_in != totals.new_faces - totals.dRank:
            raise AssertionError("row frontier debt identity failed")
        if totals.working_debt_delta != debt_out - debt_in:
            raise AssertionError("segment working debt does not telescope")
        return cls(incoming, direct, tuple(steps), totals, debt_in, debt_out)


def verify_packet_row_weight(
    incoming: FrontierState,
    prefix: str,
    packet_names: Sequence[str],
    suffix: str,
    packet_alphabet: Mapping[str, str] = ROW_PACKET_ALPHABET,
) -> PacketRowWeightCertificate | None:
    """Convenience wrapper for :meth:`PacketRowWeightCertificate.verify`."""

    return PacketRowWeightCertificate.verify(
        incoming, prefix, packet_names, suffix, packet_alphabet
    )


__all__ = [
    "PacketRowWeightCertificate",
    "PacketSegmentDeltas",
    "PacketStep",
    "append_segment_exact",
    "begin_row",
    "verify_packet_row_weight",
]
