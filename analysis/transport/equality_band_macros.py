#!/usr/bin/env python3
"""Verified three-row macro transitions for the equality row grammar."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from analysis.bounds.proof_oriented_identities import tile_grammar_row_deltas
from analysis.tiles.tile_grammar import FrontierState, advance_row


EQUALITY_ROW_CHARGE = 1


@dataclass(frozen=True, slots=True)
class StructuralState:
    """The cumulative-cost-free part of a frontier state."""

    row_index: int
    previous_u_mask: int
    partition: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class RootedDebtUpdate:
    """Exact rooted-component debt and any incoming blocks joined to OUT."""

    before: int
    after: int
    delta: int
    incoming_blocks_merged_into_out: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class EqualityRowTransition:
    incoming: StructuralState
    outgoing: StructuralState
    mask: int
    d_u: int
    d_edges: int
    d_cycles: int
    d_rank: int
    charge: int
    weight: int
    rooted_debt: RootedDebtUpdate


@dataclass(frozen=True, slots=True)
class EqualityBandMacroTransition:
    """Three accepted primitive transitions and their verified sum."""

    incoming: FrontierState
    outgoing: FrontierState
    masks: tuple[int, int, int]
    structural_states: tuple[
        StructuralState, StructuralState, StructuralState, StructuralState
    ]
    rows: tuple[EqualityRowTransition, EqualityRowTransition, EqualityRowTransition]
    d_u: int
    d_edges: int
    d_cycles: int
    d_rank: int
    charge: int
    weight: int
    rooted_debt_before: int
    rooted_debt_after: int

    @property
    def intermediate_states(self) -> tuple[StructuralState, StructuralState]:
        return self.structural_states[1:3]


def structural_state(state: FrontierState) -> StructuralState:
    return StructuralState(state.row_index, state.previous_u_mask, state.partition)


def rooted_debt(state: FrontierState) -> int:
    """Count frontier partition blocks other than the block containing OUT."""
    out_block = state.partition[0]
    return len(set(state.partition) - {out_block})


def _incoming_blocks_merged_into_out(
    incoming: FrontierState, mask: int
) -> tuple[int, ...]:
    """Identify incoming non-OUT blocks connected to OUT by this row's edges."""
    if incoming.row_index == 0:
        return ()

    n = incoming.n
    # Nodes 0..n-1 are OUT followed by old faces. New faces, when present,
    # occupy n..2n-2. This is the same edge set consumed by advance_row.
    node_count = n if incoming.row_index + 1 == n else 2 * n - 1
    parent = list(range(node_count))

    def find(node: int) -> int:
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    def union(left: int, right: int) -> None:
        left_root = find(left)
        right_root = find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    representatives: dict[int, int] = {}
    for node, block in enumerate(incoming.partition):
        if block in representatives:
            union(node, representatives[block])
        else:
            representatives[block] = node

    both_u = incoming.previous_u_mask & mask
    for column in range(n):
        if both_u & (1 << column):
            left = 0 if column == 0 else column
            right = 0 if column + 1 == n else column + 1
            union(left, right)

    adjacent_u = mask & (mask >> 1)
    for column in range(n - 1):
        if adjacent_u & (1 << column):
            above = column + 1
            below = 0 if incoming.row_index + 1 == n else n + column
            union(above, below)

    out_root = find(0)
    out_block = incoming.partition[0]
    return tuple(
        sorted(
            block
            for block, representative in representatives.items()
            if block != out_block and find(representative) == out_root
        )
    )


def advance_equality_band(
    incoming: FrontierState, masks: Sequence[int]
) -> EqualityBandMacroTransition | None:
    """Compose exactly three accepted rows, returning ``None`` on any rejection."""
    masks = tuple(masks)
    if len(masks) != 3:
        raise ValueError("an equality-band macro requires exactly three row masks")
    if incoming.row_index + 3 > incoming.n:
        raise ValueError("three-row macro extends below the grid")

    states = [incoming]
    rows = []
    for mask in masks:
        outgoing = advance_row(states[-1], mask)
        if outgoing is None:
            return None
        deltas = tile_grammar_row_deltas(states[-1], mask, outgoing)
        before = rooted_debt(states[-1])
        after = rooted_debt(outgoing)
        debt = RootedDebtUpdate(
            before=before,
            after=after,
            delta=after - before,
            incoming_blocks_merged_into_out=_incoming_blocks_merged_into_out(
                states[-1], mask
            ),
        )
        weight = 3 * deltas.u_count - 2 * deltas.rank_delta - EQUALITY_ROW_CHARGE
        rows.append(
            EqualityRowTransition(
                incoming=structural_state(states[-1]),
                outgoing=structural_state(outgoing),
                mask=mask,
                d_u=deltas.u_count,
                d_edges=deltas.edge_delta,
                d_cycles=deltas.cycle_delta,
                d_rank=deltas.rank_delta,
                charge=EQUALITY_ROW_CHARGE,
                weight=weight,
                rooted_debt=debt,
            )
        )
        states.append(outgoing)

    macro = EqualityBandMacroTransition(
        incoming=incoming,
        outgoing=states[-1],
        masks=masks,  # type: ignore[arg-type]
        structural_states=tuple(map(structural_state, states)),  # type: ignore[arg-type]
        rows=tuple(rows),  # type: ignore[arg-type]
        d_u=sum(row.d_u for row in rows),
        d_edges=sum(row.d_edges for row in rows),
        d_cycles=sum(row.d_cycles for row in rows),
        d_rank=sum(row.d_rank for row in rows),
        charge=sum(row.charge for row in rows),
        weight=sum(row.weight for row in rows),
        rooted_debt_before=rooted_debt(incoming),
        rooted_debt_after=rooted_debt(states[-1]),
    )
    verify_equality_band_macro(macro)
    return macro


def verify_equality_band_macro(macro: EqualityBandMacroTransition) -> None:
    """Recompose a macro and verify every recorded row and aggregate delta."""
    state = macro.incoming
    expected_rows = []
    for mask in macro.masks:
        outgoing = advance_row(state, mask)
        if outgoing is None:
            raise ValueError("macro contains a rejected primitive transition")
        deltas = tile_grammar_row_deltas(state, mask, outgoing)
        before = rooted_debt(state)
        after = rooted_debt(outgoing)
        expected_rows.append(
            EqualityRowTransition(
                structural_state(state),
                structural_state(outgoing),
                mask,
                deltas.u_count,
                deltas.edge_delta,
                deltas.cycle_delta,
                deltas.rank_delta,
                EQUALITY_ROW_CHARGE,
                3 * deltas.u_count - 2 * deltas.rank_delta - EQUALITY_ROW_CHARGE,
                RootedDebtUpdate(
                    before,
                    after,
                    after - before,
                    _incoming_blocks_merged_into_out(state, mask),
                ),
            )
        )
        state = outgoing

    structural_states = (
        expected_rows[0].incoming,
        *(row.outgoing for row in expected_rows),
    )
    totals = (
        sum(row.d_u for row in expected_rows),
        sum(row.d_edges for row in expected_rows),
        sum(row.d_cycles for row in expected_rows),
        sum(row.d_rank for row in expected_rows),
        sum(row.charge for row in expected_rows),
        sum(row.weight for row in expected_rows),
    )
    recorded_totals = (
        macro.d_u,
        macro.d_edges,
        macro.d_cycles,
        macro.d_rank,
        macro.charge,
        macro.weight,
    )
    if tuple(expected_rows) != macro.rows:
        raise ValueError("macro row records disagree with primitive row deltas")
    if structural_states != macro.structural_states or state != macro.outgoing:
        raise ValueError("macro structural states disagree with primitive transitions")
    if totals != recorded_totals:
        raise ValueError("macro totals disagree with the sum of its row deltas")
    if macro.d_u != macro.outgoing.u_cost - macro.incoming.u_cost:
        raise ValueError("macro dU disagrees with frontier U costs")
    if macro.d_cycles != macro.outgoing.cycle_excess - macro.incoming.cycle_excess:
        raise ValueError("macro dCycles disagrees with frontier cycle excess")
    if (macro.rooted_debt_before, macro.rooted_debt_after) != (
        rooted_debt(macro.incoming),
        rooted_debt(macro.outgoing),
    ):
        raise ValueError("macro rooted debt disagrees with its endpoint partitions")
