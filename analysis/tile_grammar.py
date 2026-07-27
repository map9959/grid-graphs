#!/usr/bin/env python3
"""Finite-state dual-frontier grammar for diagonal U-patterns.

The frontier after processing primal row `r` consists of the `n-1` cell faces
immediately below that row plus OUT. A state records their connectivity
partition, the current row's U mask, accumulated U cost, and the number of
dual edges that closed cycles. Processing three rows is one tile-band grammar
transition.

This module is a synthesis primitive, not yet a residue-2 construction.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from construction_lab import DSU, dual_connectivity_check, q_formula, run_check
from diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
    residue_zero_explicit_pattern,
)
from tile_alphabet import ALPHABET, Tile
from tile_symmetry import orbit


@dataclass(frozen=True)
class FrontierState:
    n: int
    row_index: int
    previous_u_mask: int
    partition: tuple[int, ...]
    u_cost: int
    cycle_excess: int

    @property
    def finished(self) -> bool:
        return self.row_index == self.n


@dataclass(frozen=True)
class PartialBandState:
    columns: int
    right_u: tuple[bool, bool, bool]
    row_masks: tuple[int, int, int]
    u_cost: int
    cycle_excess: int
    partition_one: tuple[int, ...]
    partition_two: tuple[int, ...]
    partition_three: tuple[int, ...]
    tile_names: tuple[str, ...]


ROW_PACKET_ALPHABET: dict[str, str] = {
    "L": "UU.",
    "X": "U.U",
    "R": ".UU",
    "H": "UUU",
}


@dataclass(frozen=True, slots=True)
class PartialRowState:
    """Exact state after consuming a prefix of one new vertex row."""

    columns: int
    right_u: bool
    row_mask: int
    row_u_cost: int
    packet_charge: int
    h_count: int
    partition: tuple[int, ...]
    cycle_excess: int
    packet_names: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class RowPacketTransition:
    outgoing: FrontierState
    row_mask: int
    packet_names: tuple[str, ...]
    packet_charge: int
    h_count: int


@dataclass(frozen=True, slots=True)
class RowPacketVerification:
    incoming_states: int
    checked_rows: int
    sealed_rows: int
    attempted_transitions: int


PartialSelector = Callable[
    [FrontierState, int, tuple[PartialBandState, ...], int], tuple[tuple, ...]
]


def initial_state(n: int) -> FrontierState:
    if n < 2:
        raise ValueError("frontier grammar requires n >= 2")
    return FrontierState(
        n=n,
        row_index=0,
        previous_u_mask=0,
        partition=(0,),
        u_cost=0,
        cycle_excess=0,
    )


def row_mask(row: str) -> int:
    if any(value not in ".U" for value in row):
        raise ValueError("rows must contain only '.' and 'U'")
    return sum(1 << c for c, value in enumerate(row) if value == "U")


def render_mask(mask: int, n: int) -> str:
    return "".join("U" if mask & (1 << c) else "." for c in range(n))


def canonical_partition(dsu: DSU, nodes: list[object]) -> tuple[int, ...]:
    labels: dict[object, int] = {}
    out = []
    for node in nodes:
        root = dsu.find(node)
        if root not in labels:
            labels[root] = len(labels)
        out.append(labels[root])
    return tuple(out)


def dsu_from_partition(nodes: list[object], partition: tuple[int, ...]) -> DSU:
    if len(nodes) != len(partition):
        raise ValueError("partition has the wrong size")
    dsu = DSU(nodes)
    representatives: dict[int, object] = {}
    for node, label in zip(nodes, partition):
        if label in representatives:
            dsu.union(node, representatives[label])
        else:
            representatives[label] = node
    return dsu


def advance_row(state: FrontierState, current_u_mask: int) -> FrontierState | None:
    """Advance one primal row, or return None if a dual component is sealed."""
    if state.finished:
        raise ValueError("cannot advance a finished frontier")
    n = state.n
    if current_u_mask < 0 or current_u_mask >= 1 << n:
        raise ValueError("row mask does not fit the grid width")

    r = state.row_index
    old_nodes = [("old", c) for c in range(n - 1)] if r > 0 else []
    new_nodes = [("new", c) for c in range(n - 1)] if r + 1 < n else []
    out_node = ("out", 0)
    nodes = [out_node, *old_nodes, *new_nodes]
    dsu = DSU(nodes)

    if r > 0:
        partition_nodes = [out_node, *old_nodes]
        if len(state.partition) != len(partition_nodes):
            raise ValueError("frontier partition has the wrong size")
        representatives: dict[int, object] = {}
        for node, label in zip(partition_nodes, state.partition):
            if label in representatives:
                dsu.union(node, representatives[label])
            else:
                representatives[label] = node
    elif state.partition != (0,):
        raise ValueError("initial frontier partition must contain only OUT")

    cycles = state.cycle_excess

    def add_edge(a: object, b: object) -> None:
        nonlocal cycles
        if not dsu.union(a, b):
            cycles += 1

    # Vertical primal edges between the previous and current vertex rows have
    # dual endpoints in the old frontier (or OUT at the left/right boundary).
    if r > 0:
        both_u = state.previous_u_mask & current_u_mask
        for c in range(n):
            if not both_u & (1 << c):
                continue
            left = out_node if c == 0 else ("old", c - 1)
            right = out_node if c + 1 == n else ("old", c)
            add_edge(left, right)

    # Horizontal primal edges in the current row connect the old face above
    # to the new face below, with OUT used on the top and bottom boundaries.
    adjacent_u = current_u_mask & (current_u_mask >> 1)
    for c in range(n - 1):
        if not adjacent_u & (1 << c):
            continue
        above = out_node if r == 0 else ("old", c)
        below = out_node if r + 1 == n else ("new", c)
        add_edge(above, below)

    retained = {dsu.find(out_node), *(dsu.find(node) for node in new_nodes)}
    if any(dsu.find(node) not in retained for node in old_nodes):
        return None

    frontier_nodes = [out_node, *new_nodes]
    partition = canonical_partition(dsu, frontier_nodes)
    if r + 1 == n and partition != (0,):
        return None
    return FrontierState(
        n=n,
        row_index=r + 1,
        previous_u_mask=current_u_mask,
        partition=partition,
        u_cost=state.u_cost + current_u_mask.bit_count(),
        cycle_excess=cycles,
    )


def _row_node_order(state: FrontierState) -> tuple[list[object], list[object], list[object]]:
    old = (
        [("old", c) for c in range(state.n - 1)]
        if state.row_index > 0
        else []
    )
    new = (
        [("new", c) for c in range(state.n - 1)]
        if state.row_index + 1 < state.n
        else []
    )
    return [("out", 0), *old, *new], old, new


def _initial_partial_row(state: FrontierState) -> PartialRowState:
    order, old, _ = _row_node_order(state)
    incoming_nodes = [("out", 0), *old]
    if len(state.partition) != len(incoming_nodes):
        raise ValueError("frontier partition has the wrong size")
    dsu = DSU(order)
    incoming = dsu_from_partition(incoming_nodes, state.partition)
    representatives: dict[object, object] = {}
    for node in incoming_nodes:
        root = incoming.find(node)
        if root in representatives:
            dsu.union(node, representatives[root])
        else:
            representatives[root] = node
    return PartialRowState(0, False, 0, 0, 0, 0, canonical_partition(dsu, order), 0, ())


def _append_row_bits(
    state: FrontierState, partial: PartialRowState, bits: str
) -> PartialRowState:
    if any(bit not in ".U" for bit in bits):
        raise ValueError("fixed bits and packet values must contain only '.' and 'U'")
    if partial.columns + len(bits) > state.n:
        raise ValueError("row prefix extends beyond the grid width")
    order, old, new = _row_node_order(state)
    out = ("out", 0)
    dsu = dsu_from_partition(order, partial.partition)
    columns = partial.columns
    right_u = partial.right_u
    mask = partial.row_mask
    cost = partial.row_u_cost
    cycles = partial.cycle_excess

    def add_edge(a: object, b: object) -> None:
        nonlocal cycles
        if not dsu.union(a, b):
            cycles += 1

    for bit in bits:
        current_u = bit == "U"
        c = columns
        if (
            old
            and current_u
            and state.previous_u_mask & (1 << c)
        ):
            left = out if c == 0 else old[c - 1]
            right = out if c + 1 == state.n else old[c]
            add_edge(left, right)
        if c > 0 and right_u and current_u:
            above = out if not old else old[c - 1]
            below = out if not new else new[c - 1]
            add_edge(above, below)
        if current_u:
            mask |= 1 << c
            cost += 1
        right_u = current_u
        columns += 1

    return PartialRowState(
        columns=columns,
        right_u=right_u,
        row_mask=mask,
        row_u_cost=cost,
        packet_charge=partial.packet_charge,
        h_count=partial.h_count,
        partition=canonical_partition(dsu, order),
        cycle_excess=cycles,
        packet_names=partial.packet_names,
    )


def _partial_row_has_sealed_component(
    state: FrontierState, partial: PartialRowState
) -> bool:
    """Reject only old faces that no unprocessed column can still touch."""
    order, old, new = _row_node_order(state)
    labels = dict(zip(order, partial.partition))
    retired_end = max(0, partial.columns - 1)
    reachable = {labels[("out", 0)]}
    reachable.update(labels[node] for node in new)
    reachable.update(labels[node] for node in old[retired_end:])
    return any(labels[node] not in reachable for node in old[:retired_end])


def _partial_row_key(partial: PartialRowState) -> tuple:
    return (
        partial.columns,
        partial.right_u,
        partial.row_mask,
        partial.row_u_cost,
        partial.packet_charge,
        partial.h_count,
        partial.partition,
        partial.cycle_excess,
    )


def stream_row_packets(
    incoming: FrontierState,
    prefix: str,
    suffix: str,
    packet_domains: Sequence[Sequence[str]],
    *,
    packet_alphabet: Mapping[str, str] = ROW_PACKET_ALPHABET,
    packet_charge_bounds: tuple[int | None, int | None] = (None, None),
    u_cost_bounds: tuple[int | None, int | None] = (None, None),
) -> tuple[list[RowPacketTransition], int]:
    """Stream one row exactly, deduplicating full (unprojected) DSU states.

    Packet charge is ``len(U) - 2`` per packet. U-cost bounds apply to the
    outgoing state's cumulative cost, while packet-charge bounds are row-local.
    The attempted count is the number of partial-state/packet pairs expanded.
    """
    if incoming.finished:
        raise ValueError("cannot advance a finished frontier")
    if any(not domain for domain in packet_domains):
        raise ValueError("packet domains must be nonempty")
    unknown = {
        name for domain in packet_domains for name in domain if name not in packet_alphabet
    }
    if unknown:
        raise ValueError(f"unknown packet names: {sorted(unknown)}")
    widths = {len(packet_alphabet[name]) for domain in packet_domains for name in domain}
    if len(prefix) + len(suffix) + sum(
        len(packet_alphabet[domain[0]]) for domain in packet_domains
    ) != incoming.n:
        raise ValueError("fixed bits and packet domains do not span the grid width")
    if any(
        len(packet_alphabet[name]) != len(packet_alphabet[domain[0]])
        for domain in packet_domains
        for name in domain
    ):
        raise ValueError("all packets in a domain must have the same width")
    if not widths and len(prefix) + len(suffix) != incoming.n:
        raise ValueError("fixed bits do not span the grid width")

    min_charge, max_charge = packet_charge_bounds
    min_cost, max_cost = u_cost_bounds
    if min_charge is not None and max_charge is not None and min_charge > max_charge:
        raise ValueError("packet charge bounds are reversed")
    if min_cost is not None and max_cost is not None and min_cost > max_cost:
        raise ValueError("U-cost bounds are reversed")

    suffix_charge_min = [0] * (len(packet_domains) + 1)
    suffix_charge_max = [0] * (len(packet_domains) + 1)
    suffix_cost_min = [0] * (len(packet_domains) + 1)
    suffix_cost_max = [0] * (len(packet_domains) + 1)
    for index in range(len(packet_domains) - 1, -1, -1):
        counts = [packet_alphabet[name].count("U") for name in packet_domains[index]]
        suffix_charge_min[index] = suffix_charge_min[index + 1] + min(counts) - 2
        suffix_charge_max[index] = suffix_charge_max[index + 1] + max(counts) - 2
        suffix_cost_min[index] = suffix_cost_min[index + 1] + min(counts)
        suffix_cost_max[index] = suffix_cost_max[index + 1] + max(counts)

    initial = _append_row_bits(incoming, _initial_partial_row(incoming), prefix)
    partials = {_partial_row_key(initial): initial}
    attempted = 0
    suffix_u_cost = suffix.count("U")
    for domain_index, domain in enumerate(packet_domains):
        candidates: dict[tuple, PartialRowState] = {}
        for partial in partials.values():
            for name in domain:
                attempted += 1
                value = packet_alphabet[name]
                child = _append_row_bits(incoming, partial, value)
                child = PartialRowState(
                    columns=child.columns,
                    right_u=child.right_u,
                    row_mask=child.row_mask,
                    row_u_cost=child.row_u_cost,
                    packet_charge=partial.packet_charge + value.count("U") - 2,
                    h_count=partial.h_count + (value.count("U") == 3),
                    partition=child.partition,
                    cycle_excess=child.cycle_excess,
                    packet_names=(*partial.packet_names, name),
                )
                if _partial_row_has_sealed_component(incoming, child):
                    continue
                remaining = domain_index + 1
                if (
                    min_charge is not None
                    and child.packet_charge + suffix_charge_max[remaining] < min_charge
                ):
                    continue
                if (
                    max_charge is not None
                    and child.packet_charge + suffix_charge_min[remaining] > max_charge
                ):
                    continue
                lowest_cost = (
                    incoming.u_cost
                    + child.row_u_cost
                    + suffix_cost_min[remaining]
                    + suffix_u_cost
                )
                highest_cost = (
                    incoming.u_cost
                    + child.row_u_cost
                    + suffix_cost_max[remaining]
                    + suffix_u_cost
                )
                if min_cost is not None and highest_cost < min_cost:
                    continue
                if max_cost is not None and lowest_cost > max_cost:
                    continue
                candidates.setdefault(_partial_row_key(child), child)
        partials = candidates
        if not partials:
            break

    results = []
    for partial in partials.values():
        child = _append_row_bits(incoming, partial, suffix)
        if _partial_row_has_sealed_component(incoming, child):
            continue
        total_cost = incoming.u_cost + child.row_u_cost
        if min_charge is not None and child.packet_charge < min_charge:
            continue
        if max_charge is not None and child.packet_charge > max_charge:
            continue
        if min_cost is not None and total_cost < min_cost:
            continue
        if max_cost is not None and total_cost > max_cost:
            continue
        order, _, new = _row_node_order(incoming)
        dsu = dsu_from_partition(order, child.partition)
        partition = canonical_partition(dsu, [("out", 0), *new])
        if incoming.row_index + 1 == incoming.n and partition != (0,):
            continue
        outgoing = FrontierState(
            n=incoming.n,
            row_index=incoming.row_index + 1,
            previous_u_mask=child.row_mask,
            partition=partition,
            u_cost=total_cost,
            cycle_excess=incoming.cycle_excess + child.cycle_excess,
        )
        results.append(
            RowPacketTransition(
                outgoing,
                child.row_mask,
                child.packet_names,
                child.packet_charge,
                child.h_count,
            )
        )
    return results, attempted


def advance_band(
    state: FrontierState, band: tuple[int, int, int]
) -> FrontierState | None:
    """Apply one three-row tile-band transition."""
    current: FrontierState | None = state
    for mask in band:
        if current is None:
            return None
        current = advance_row(current, mask)
    return current


def band_node_orders(
    state: FrontierState,
) -> tuple[list[object], list[object], list[object], list[object], list[object], list[object]]:
    """Return the three DSU orders and their old/intermediate/new face rows."""
    n = state.n
    r = state.row_index
    if r + 3 > n:
        raise ValueError("three-row band extends below the grid")
    out = ("out", 0)
    old = [("old", c) for c in range(n - 1)] if r > 0 else []
    middle_one = [("middle-one", c) for c in range(n - 1)]
    middle_two = [("middle-two", c) for c in range(n - 1)]
    new = [("new", c) for c in range(n - 1)] if r + 3 < n else []
    return (
        [out, *old, *middle_one],
        [out, *old, *middle_one, *middle_two],
        [out, *old, *middle_one, *middle_two, *new],
        old,
        middle_one,
        middle_two,
    )


def initial_partial_band(state: FrontierState) -> PartialBandState:
    order_one, order_two, order_three, old, _, _ = band_node_orders(state)
    out = ("out", 0)

    def initial_partition(order: list[object]) -> tuple[int, ...]:
        dsu = DSU(order)
        incoming_nodes = [out, *old]
        if old:
            incoming = dsu_from_partition(incoming_nodes, state.partition)
            representatives: dict[object, object] = {}
            for node in incoming_nodes:
                root = incoming.find(node)
                if root in representatives:
                    dsu.union(node, representatives[root])
                else:
                    representatives[root] = node
        elif state.partition != (0,):
            raise ValueError("top frontier partition must contain only OUT")
        return canonical_partition(dsu, order)

    return PartialBandState(
        columns=0,
        right_u=(False, False, False),
        row_masks=(0, 0, 0),
        u_cost=0,
        cycle_excess=0,
        partition_one=initial_partition(order_one),
        partition_two=initial_partition(order_two),
        partition_three=initial_partition(order_three),
        tile_names=(),
    )


def partial_band_key(partial: PartialBandState) -> tuple:
    """Congruence key for every possible suffix of a three-row band."""
    return (
        partial.columns,
        partial.right_u,
        partial.row_masks[2],
        partial.u_cost,
        partial.cycle_excess,
        partial.partition_one,
        partial.partition_two,
        partial.partition_three,
    )


def append_tile_to_partial(
    state: FrontierState, partial: PartialBandState, tile: Tile
) -> PartialBandState:
    """Append one 3x3 tile while preserving exact band-transition semantics."""
    n = state.n
    r = state.row_index
    if partial.columns + 3 > n:
        raise ValueError("tile extends beyond the band width")
    order_one, order_two, order_three, old, middle_one, middle_two = band_node_orders(state)
    new = [("new", c) for c in range(n - 1)] if r + 3 < n else []
    out = ("out", 0)
    dsu_one = dsu_from_partition(order_one, partial.partition_one)
    dsu_two = dsu_from_partition(order_two, partial.partition_two)
    dsu_three = dsu_from_partition(order_three, partial.partition_three)
    cycles = partial.cycle_excess
    masks = list(partial.row_masks)
    right_u = partial.right_u
    cost = partial.u_cost

    def add_three(a: object, b: object) -> None:
        nonlocal cycles
        if not dsu_three.union(a, b):
            cycles += 1

    def add_first(a: object, b: object) -> None:
        dsu_one.union(a, b)
        dsu_two.union(a, b)
        add_three(a, b)

    def add_second(a: object, b: object) -> None:
        dsu_two.union(a, b)
        add_three(a, b)

    for local_c in range(3):
        c = partial.columns + local_c
        current = tuple(tile.rows[row][local_c] == "U" for row in range(3))
        top, middle, bottom = current

        if r > 0 and state.previous_u_mask & (1 << c) and top:
            left = out if c == 0 else old[c - 1]
            right = out if c + 1 == n else old[c]
            add_first(left, right)
        if top and middle:
            left = out if c == 0 else middle_one[c - 1]
            right = out if c + 1 == n else middle_one[c]
            add_second(left, right)
        if middle and bottom:
            left = out if c == 0 else middle_two[c - 1]
            right = out if c + 1 == n else middle_two[c]
            add_three(left, right)

        if c > 0:
            gap = c - 1
            if right_u[0] and top:
                above = out if r == 0 else old[gap]
                add_first(above, middle_one[gap])
            if right_u[1] and middle:
                add_second(middle_one[gap], middle_two[gap])
            if right_u[2] and bottom:
                below = out if r + 3 == n else new[gap]
                add_three(middle_two[gap], below)

        for row, value in enumerate(current):
            if value:
                masks[row] |= 1 << c
                cost += 1
        right_u = current

    return PartialBandState(
        columns=partial.columns + 3,
        right_u=right_u,
        row_masks=tuple(masks),  # type: ignore[arg-type]
        u_cost=cost,
        cycle_excess=cycles,
        partition_one=canonical_partition(dsu_one, order_one),
        partition_two=canonical_partition(dsu_two, order_two),
        partition_three=canonical_partition(dsu_three, order_three),
        tile_names=(*partial.tile_names, tile.name),
    )


def partial_band_has_sealed_component(
    state: FrontierState, partial: PartialBandState
) -> bool:
    """Return whether a processed horizontal prefix has lost a dual component."""
    order_one, order_two, order_three, old, middle_one, middle_two = band_node_orders(
        state
    )
    new = (
        [("new", c) for c in range(state.n - 1)]
        if state.row_index + 3 < state.n
        else []
    )
    out = ("out", 0)
    retired_end = max(0, partial.columns - 1)

    def sealed(
        order: list[object],
        partition: tuple[int, ...],
        retired: list[object],
        retained: list[object],
        mutable_auxiliary: list[object] | tuple[object, ...] = (),
    ) -> bool:
        labels = dict(zip(order, partition))
        still_mutable = retired[retired_end:]
        reachable_labels = {
            labels[node]
            for node in [*retained, *still_mutable, *mutable_auxiliary]
        }
        return any(labels[node] not in reachable_labels for node in retired[:retired_end])

    return (
        sealed(order_one, partial.partition_one, old, [out, *middle_one])
        or sealed(
            order_two,
            partial.partition_two,
            middle_one,
            [out, *middle_two],
            old[retired_end:],
        )
        or sealed(
            order_three,
            partial.partition_three,
            middle_two,
            [out, *new],
            [*old[retired_end:], *middle_one[retired_end:]],
        )
    )


def finish_partial_band(
    state: FrontierState, partial: PartialBandState
) -> FrontierState | None:
    if partial.columns != state.n:
        raise ValueError("cannot finish an incomplete tile band")
    order_one, order_two, order_three, old, middle_one, middle_two = band_node_orders(state)
    new = [("new", c) for c in range(state.n - 1)] if state.row_index + 3 < state.n else []
    out = ("out", 0)
    dsu_one = dsu_from_partition(order_one, partial.partition_one)
    dsu_two = dsu_from_partition(order_two, partial.partition_two)
    dsu_three = dsu_from_partition(order_three, partial.partition_three)

    def sealed(dsu: DSU, retired: list[object], retained: list[object]) -> bool:
        retained_roots = {dsu.find(node) for node in retained}
        return any(dsu.find(node) not in retained_roots for node in retired)

    if sealed(dsu_one, old, [out, *middle_one]):
        return None
    if sealed(dsu_two, middle_one, [out, *middle_two]):
        return None
    if sealed(dsu_three, middle_two, [out, *new]):
        return None

    partition = canonical_partition(dsu_three, [out, *new])
    return FrontierState(
        n=state.n,
        row_index=state.row_index + 3,
        previous_u_mask=partial.row_masks[2],
        partition=partition,
        u_cost=state.u_cost + partial.u_cost,
        cycle_excess=state.cycle_excess + partial.cycle_excess,
    )


def stream_band_domains(
    state: FrontierState,
    domains: list[tuple[Tile, ...]],
    max_u_cost: int | None = None,
    max_cycle_excess: int | None = None,
    remaining_u_costs: list[frozenset[int]] | None = None,
    target_u_costs: frozenset[int] | None = None,
    partial_beam_width: int | None = None,
    partial_selector: PartialSelector | None = None,
) -> tuple[list[tuple[FrontierState, tuple[int, int, int], tuple[str, ...]]], int]:
    """Compose a tile band left-to-right, deduplicating after every tile."""
    if len(domains) * 3 != state.n:
        raise ValueError("tile domains do not span the grid width")
    if remaining_u_costs is not None and len(remaining_u_costs) != len(domains) + 1:
        raise ValueError("remaining-cost table has the wrong size")
    initial = initial_partial_band(state)
    partials = {partial_band_key(initial): initial}
    transitions = 0
    for domain_index, domain in enumerate(domains):
        candidates: dict[tuple, PartialBandState] = {}
        for partial in partials.values():
            for tile in domain:
                transitions += 1
                child = append_tile_to_partial(state, partial, tile)
                if partial_band_has_sealed_component(state, child):
                    continue
                if max_u_cost is not None and state.u_cost + child.u_cost > max_u_cost:
                    continue
                if (
                    max_cycle_excess is not None
                    and state.cycle_excess + child.cycle_excess > max_cycle_excess
                ):
                    continue
                if (
                    remaining_u_costs is not None
                    and target_u_costs is not None
                    and not any(
                        target - state.u_cost - child.u_cost
                        in remaining_u_costs[domain_index + 1]
                        for target in target_u_costs
                    )
                ):
                    continue
                candidates.setdefault(partial_band_key(child), child)
        partials = candidates
        # Let the exact sealing check evaluate every final-column completion;
        # connectivity heuristics before that check can favor doomed components.
        if (
            partial_beam_width is not None
            and domain_index + 1 < len(domains)
            and len(partials) > partial_beam_width
        ):
            if partial_selector is None:
                ranked = sorted(
                    partials.values(),
                    key=lambda child: (
                        child.cycle_excess,
                        len(set(child.partition_one))
                        + len(set(child.partition_two))
                        + len(set(child.partition_three)),
                        partial_band_key(child),
                    ),
                )[:partial_beam_width]
                partials = {partial_band_key(child): child for child in ranked}
            else:
                ordered = tuple(sorted(partials.values(), key=partial_band_key))
                selected = partial_selector(
                    state, domain_index + 1, ordered, partial_beam_width
                )
                if len(selected) != partial_beam_width:
                    raise ValueError(
                        "partial selector must return exactly the requested width"
                    )
                if len(set(selected)) != len(selected):
                    raise ValueError("partial selector returned duplicate keys")
                unknown = [key for key in selected if key not in partials]
                if unknown:
                    raise ValueError("partial selector returned an unknown key")
                partials = {key: partials[key] for key in selected}
        if not partials:
            break

    results = []
    for partial in partials.values():
        outgoing = finish_partial_band(state, partial)
        if outgoing is not None:
            results.append((outgoing, partial.row_masks, partial.tile_names))
    return results, transitions


def tile_band_masks(tiles: tuple[Tile, ...]) -> tuple[int, int, int]:
    """Render one horizontal sequence of 3x3 tiles as three row masks."""
    if not tiles:
        raise ValueError("a tile band must contain at least one tile")
    rows = ["".join(tile.rows[r] for tile in tiles) for r in range(3)]
    return tuple(row_mask(row) for row in rows)  # type: ignore[return-value]


def production_tiles(oriented: bool = False) -> tuple[Tile, ...]:
    if not oriented:
        return tuple(ALPHABET.values())
    rows = sorted({variant for tile in ALPHABET.values() for variant in orbit(tile.rows)})
    return tuple(Tile(f"O{index:02}", variant) for index, variant in enumerate(rows))


def tile_band_productions(
    columns: int, oriented: bool = False
) -> list[tuple[tuple[str, ...], tuple[int, int, int]]]:
    """Enumerate bands over canonical or fully oriented named tiles."""
    if columns < 1:
        raise ValueError("tile column count must be positive")
    tiles = production_tiles(oriented)
    return [
        (tuple(tile.name for tile in choice), tile_band_masks(choice))
        for choice in product(tiles, repeat=columns)
    ]


def grammar_key(state: FrontierState) -> tuple[int, tuple[int, ...], int, int]:
    """Key for retaining one representative of an equivalent outgoing state."""
    return (
        state.previous_u_mask,
        state.partition,
        state.u_cost,
        state.cycle_excess,
    )


def suffix_u_costs(
    domains: list[list[tuple[Tile, ...]]],
) -> list[frozenset[int]]:
    """Exact attainable U costs for every suffix of a tile-domain matrix."""
    positions = [domain for row in domains for domain in row]
    suffix = [frozenset() for _ in range(len(positions) + 1)]
    suffix[-1] = frozenset((0,))
    for index in range(len(positions) - 1, -1, -1):
        tile_costs = {tile.u_count for tile in positions[index]}
        suffix[index] = frozenset(
            tile_cost + later
            for tile_cost in tile_costs
            for later in suffix[index + 1]
        )
    return suffix


def synthesize_tiled(
    n: int,
    beam_width: int = 5000,
    max_cycle_excess: int = 1,
    oriented: bool = False,
) -> tuple[list[str] | None, list[tuple[str, ...]] | None, int]:
    """Beam-search square patterns made entirely from canonical 3x3 tiles."""
    if n % 3 != 0 or n < 3:
        raise ValueError("canonical tiled synthesis requires positive n divisible by 3")
    tiles = production_tiles(oriented)
    tile_rows = n // 3
    domains = [[tiles for _ in range(tile_rows)] for _ in range(tile_rows)]
    return synthesize_domains(
        domains,
        q_formula(n),
        beam_width=beam_width,
        max_cycle_excess=max_cycle_excess,
    )


def synthesize_domains(
    domains: list[list[tuple[Tile, ...]]],
    target: int,
    beam_width: int = 5000,
    max_cycle_excess: int = 1,
) -> tuple[list[str] | None, list[tuple[str, ...]] | None, int]:
    """Synthesize from a tile matrix whose positions have explicit domains."""
    tile_rows = len(domains)
    if tile_rows == 0 or any(len(row) != tile_rows for row in domains):
        raise ValueError("tile domains must form a nonempty square matrix")
    n = 3 * tile_rows
    states: dict[
        tuple[int, tuple[int, ...], int, int],
        tuple[FrontierState, list[int], list[tuple[str, ...]]],
    ] = {grammar_key(initial_state(n)): (initial_state(n), [], [])}
    transitions = 0
    remaining_u_costs = suffix_u_costs(domains)

    if target not in remaining_u_costs[0]:
        return None, None, transitions

    for band_index, domain_row in enumerate(domains):
        candidates: dict[
            tuple[int, tuple[int, ...], int, int],
            tuple[FrontierState, list[int], list[tuple[str, ...]]],
        ] = {}
        for state, masks, names in states.values():
            outgoing_bands, attempted = stream_band_domains(
                state,
                domain_row,
                max_u_cost=target,
                max_cycle_excess=max_cycle_excess,
                remaining_u_costs=remaining_u_costs[
                    band_index * tile_rows : (band_index + 1) * tile_rows + 1
                ],
                target_u_costs=frozenset((target,)),
            )
            transitions += attempted
            for outgoing, band, production_names in outgoing_bands:
                candidates.setdefault(
                    grammar_key(outgoing),
                    (outgoing, [*masks, *band], [*names, production_names]),
                )

        expected_cost = target * (band_index + 1) / tile_rows
        ranked = sorted(
            candidates.values(),
            key=lambda item: (
                abs(item[0].u_cost - expected_cost),
                item[0].cycle_excess,
                len(set(item[0].partition)),
            ),
        )
        states = {grammar_key(item[0]): item for item in ranked[:beam_width]}
        if not states:
            break

    for state, masks, names in states.values():
        if state.finished and state.u_cost == target:
            return [render_mask(mask, n) for mask in masks], names, transitions
    return None, None, transitions


def reflected_domains(
    domain_rows: list[list[tuple[Tile, ...]]],
) -> list[list[tuple[Tile, ...]]]:
    """Return tile bands in bottom-up order with every tile reflected vertically."""
    return [
        [tuple(Tile(tile.name, tile.rows[::-1]) for tile in domain) for domain in row]
        for row in reversed(domain_rows)
    ]


def expand_domain_rows(
    domain_rows: list[list[tuple[Tile, ...]]],
    n: int,
    target_costs: frozenset[int],
    beam_width: int | None,
    max_cycle_excess: int,
    partial_beam_width: int | None = None,
    merge_targets: tuple[FrontierState, ...] = (),
    total_target: int | None = None,
    merge_targets_are_forward: bool = True,
) -> tuple[
    dict[tuple[int, tuple[int, ...], int, int], tuple[FrontierState, list[int], list[tuple[str, ...]]]],
    int,
]:
    """Expand one side of a bidirectional search from its outer boundary."""
    if not domain_rows:
        state = initial_state(n)
        return {grammar_key(state): (state, [], [])}, 0
    columns = len(domain_rows[0])
    if any(len(row) != columns for row in domain_rows):
        raise ValueError("domain rows must have a common width")
    remaining = suffix_u_costs(domain_rows)
    states = {grammar_key(initial_state(n)): (initial_state(n), [], [])}
    transitions = 0
    for band_index, domain_row in enumerate(domain_rows):
        start = band_index * columns
        candidates: dict[
            tuple[int, tuple[int, ...], int, int],
            tuple[FrontierState, list[int], list[tuple[str, ...]]],
        ] = {}
        for state, masks, names in states.values():
            outgoing_bands, attempted = stream_band_domains(
                state,
                domain_row,
                max_u_cost=max(target_costs),
                max_cycle_excess=max_cycle_excess,
                remaining_u_costs=remaining[start : start + columns + 1],
                target_u_costs=target_costs,
                partial_beam_width=partial_beam_width,
            )
            transitions += attempted
            for outgoing, band, production_names in outgoing_bands:
                candidates.setdefault(
                    grammar_key(outgoing),
                    (outgoing, [*masks, *band], [*names, production_names]),
                )
        if beam_width is not None and len(candidates) > beam_width:
            expected = sum(target_costs) / len(target_costs) * (band_index + 1) / len(
                domain_rows
            )

            def rank(item):
                outgoing = item[0]
                if merge_targets and band_index + 1 == len(domain_rows):
                    compatible = [
                        target_state
                        for target_state in merge_targets
                        if total_target is not None
                        and target_state.u_cost + outgoing.u_cost == total_target
                    ]
                    merges = [
                        merge_frontier_profile(target_state, outgoing)
                        if merge_targets_are_forward
                        else merge_frontier_profile(outgoing, target_state)
                        for target_state in compatible
                    ]
                    best_merge = min(merges, default=None)
                    return (
                        best_merge[0] if best_merge is not None else n + 1,
                        best_merge[1] if best_merge is not None else outgoing.cycle_excess,
                        len(set(outgoing.partition)),
                        abs(outgoing.u_cost - expected),
                    )
                return (
                    abs(outgoing.u_cost - expected),
                    outgoing.cycle_excess,
                    len(set(outgoing.partition)),
                )

            ranked = sorted(
                candidates.values(),
                key=rank,
            )[:beam_width]
            states = {grammar_key(item[0]): item for item in ranked}
        else:
            states = candidates
        if not states:
            break
    return states, transitions


def merge_frontier_partition(
    forward: FrontierState, backward: FrontierState
) -> tuple[tuple[int, ...], int]:
    """Return the joined cut partition and cycle excess for two frontiers."""
    if forward.n != backward.n:
        raise ValueError("frontier widths do not match")
    n = forward.n
    nodes = list(range(n))  # OUT followed by the n-1 faces at the cut.
    dsu = DSU(nodes)
    glue_cycles = 0

    def add_partition(partition: tuple[int, ...], count_cycles: bool) -> None:
        nonlocal glue_cycles
        representatives: dict[int, int] = {}
        for node, label in zip(nodes, partition):
            if label not in representatives:
                representatives[label] = node
            elif not dsu.union(node, representatives[label]) and count_cycles:
                glue_cycles += 1

    add_partition(forward.partition, False)
    add_partition(backward.partition, True)
    crossing = forward.previous_u_mask & backward.previous_u_mask
    for c in range(n):
        if not crossing & (1 << c):
            continue
        left = 0 if c == 0 else c
        right = 0 if c + 1 == n else c + 1
        if not dsu.union(left, right):
            glue_cycles += 1
    partition = canonical_partition(dsu, nodes)
    return partition, forward.cycle_excess + backward.cycle_excess + glue_cycles


def merge_frontier_profile(
    forward: FrontierState, backward: FrontierState
) -> tuple[int, int]:
    """Return component count and cycle excess after joining two frontiers."""
    partition, cycles = merge_frontier_partition(forward, backward)
    return len(set(partition)), cycles


def merge_frontiers(
    forward: FrontierState, backward: FrontierState
) -> tuple[bool, int]:
    """Join top-down and reflected bottom-up states across their omitted edge row."""
    components, cycles = merge_frontier_profile(forward, backward)
    return components == 1, cycles


def synthesize_domains_bidirectional(
    domains: list[list[tuple[Tile, ...]]],
    target: int,
    beam_width: int | None = 5000,
    max_cycle_excess: int = 1,
    partial_beam_width: int | None = None,
    diagnostics: dict[str, object] | None = None,
    target_rank_side: str = "backward",
    split: int | None = None,
) -> tuple[list[str] | None, list[tuple[str, ...]] | None, int, tuple[int, int]]:
    """Meet top-down and reflected bottom-up tile searches at a band boundary."""
    tile_rows = len(domains)
    if tile_rows < 2 or any(len(row) != tile_rows for row in domains):
        raise ValueError("bidirectional domains must form a square with at least two rows")
    if target_rank_side not in ("forward", "backward"):
        raise ValueError("target-ranked side must be 'forward' or 'backward'")
    n = 3 * tile_rows
    if split is None:
        split = (tile_rows + 1) // 2
    elif not 1 <= split < tile_rows:
        raise ValueError("bidirectional split must lie between tile rows")
    forward_domains = domains[:split]
    backward_domains = reflected_domains(domains[split:])
    forward_costs = suffix_u_costs(forward_domains)[0]
    backward_costs = suffix_u_costs(backward_domains)[0]
    viable_forward = frozenset(cost for cost in forward_costs if target - cost in backward_costs)
    viable_backward = frozenset(cost for cost in backward_costs if target - cost in forward_costs)
    if not viable_forward or not viable_backward:
        return None, None, 0, (0, 0)

    if target_rank_side == "backward":
        forward, forward_transitions = expand_domain_rows(
            forward_domains,
            n,
            viable_forward,
            beam_width,
            max_cycle_excess,
            partial_beam_width,
        )
        backward, backward_transitions = expand_domain_rows(
            backward_domains,
            n,
            viable_backward,
            beam_width,
            max_cycle_excess,
            partial_beam_width,
            tuple(item[0] for item in forward.values()),
            target,
            True,
        )
    else:
        backward, backward_transitions = expand_domain_rows(
            backward_domains,
            n,
            viable_backward,
            beam_width,
            max_cycle_excess,
            partial_beam_width,
        )
        forward, forward_transitions = expand_domain_rows(
            forward_domains,
            n,
            viable_forward,
            beam_width,
            max_cycle_excess,
            partial_beam_width,
            tuple(item[0] for item in backward.values()),
            target,
            False,
        )
    backward_by_cost: dict[
        int,
        list[tuple[FrontierState, list[int], list[tuple[str, ...]]]],
    ] = {}
    for item in backward.values():
        backward_by_cost.setdefault(item[0].u_cost, []).append(item)

    cost_pairs = 0
    connected_pairs = 0
    minimum_cycles: int | None = None
    minimum_components: int | None = None
    best_join: tuple[
        tuple[int, ...],
        FrontierState,
        FrontierState,
        list[tuple[str, ...]],
        list[tuple[str, ...]],
    ] | None = None
    for forward_state, forward_masks, forward_names in forward.values():
        for backward_state, backward_masks, backward_names in backward_by_cost.get(
            target - forward_state.u_cost, []
        ):
            cost_pairs += 1
            joined_partition, cycles = merge_frontier_partition(
                forward_state, backward_state
            )
            components = len(set(joined_partition))
            connected = components == 1
            if minimum_components is None or components < minimum_components:
                best_join = (
                    joined_partition,
                    forward_state,
                    backward_state,
                    forward_names,
                    backward_names,
                )
            minimum_components = (
                components
                if minimum_components is None
                else min(minimum_components, components)
            )
            if connected:
                connected_pairs += 1
                minimum_cycles = (
                    cycles if minimum_cycles is None else min(minimum_cycles, cycles)
                )
            if not connected or cycles > max_cycle_excess:
                continue
            if diagnostics is not None:
                diagnostics.update(
                    cost_pairs=cost_pairs,
                    connected_pairs=connected_pairs,
                    minimum_cycles=minimum_cycles,
                    minimum_components=minimum_components,
                )
            masks = [*forward_masks, *reversed(backward_masks)]
            names = [*forward_names, *reversed(backward_names)]
            return (
                [render_mask(mask, n) for mask in masks],
                names,
                forward_transitions + backward_transitions,
                (len(forward), len(backward)),
            )
    if diagnostics is not None:
        diagnostics.update(
            cost_pairs=cost_pairs,
            connected_pairs=connected_pairs,
            minimum_cycles=minimum_cycles,
            minimum_components=minimum_components,
        )
        if best_join is not None:
            (
                joined_partition,
                forward_state,
                backward_state,
                forward_names,
                backward_names,
            ) = best_join
            bridge_columns = tuple(
                c
                for c in range(forward_state.n)
                if joined_partition[0 if c == 0 else c]
                != joined_partition[0 if c + 1 == forward_state.n else c + 1]
            )
            diagnostics.update(
                best_partition=joined_partition,
                best_forward_mask=render_mask(forward_state.previous_u_mask, forward_state.n),
                best_backward_mask=render_mask(backward_state.previous_u_mask, backward_state.n),
                best_forward_partition=forward_state.partition,
                best_backward_partition=backward_state.partition,
                best_forward_cost=forward_state.u_cost,
                best_backward_cost=backward_state.u_cost,
                best_forward_cycles=forward_state.cycle_excess,
                best_backward_cycles=backward_state.cycle_excess,
                best_forward_tiles=tuple(forward_names),
                best_backward_tiles=tuple(reversed(backward_names)),
                bridge_columns=bridge_columns,
            )
    return (
        None,
        None,
        forward_transitions + backward_transitions,
        (len(forward), len(backward)),
    )


def residue_zero_template_domains(n: int) -> list[list[tuple[Tile, ...]]]:
    """Boundary template inferred from grammar witnesses at n=6 and n=9."""
    if n % 3 != 0 or n < 9:
        raise ValueError("residue-zero template currently requires n >= 9")
    k = n // 3
    oriented = {tile.name: tile for tile in production_tiles(oriented=True)}
    any_tile = tuple(oriented.values())
    fixed = lambda name: (oriented[name],)
    domains = [[any_tile for _ in range(k)] for _ in range(k)]

    domains[0][0] = fixed("O00")
    domains[0][k - 1] = fixed("O00")
    for c in range(1, k - 1):
        domains[0][c] = fixed("O03")
    for r in range(1, k):
        domains[r][0] = fixed("O05")
        domains[r][k - 1] = fixed("O18")
    domains[k - 1][1] = fixed("O12")
    return domains


def residue_zero_wide_domains(n: int) -> list[list[tuple[Tile, ...]]]:
    """Widen the observed boundary roles to every compatible oriented tile."""
    if n % 3 != 0 or n < 9:
        raise ValueError("residue-zero wide domains currently require n >= 9")
    k = n // 3
    tiles = production_tiles(oriented=True)
    five = tuple(tile for tile in tiles if tile.u_count == 5)
    six = tuple(tile for tile in tiles if tile.u_count == 6)
    top_five = tuple(tile for tile in five if not tile.north_us)
    top_six = tuple(tile for tile in six if not tile.north_us)
    left_five = tuple(tile for tile in five if not tile.west_us)
    right_five = tuple(tile for tile in five if not tile.east_us)
    bottom_five = tuple(tile for tile in five if not tile.south_us)
    domains = [[tiles for _ in range(k)] for _ in range(k)]

    domains[0][0] = top_five
    domains[0][k - 1] = top_five
    for c in range(1, k - 1):
        domains[0][c] = top_six
    for r in range(1, k):
        domains[r][0] = left_five
        domains[r][k - 1] = right_five
    domains[k - 1][1] = bottom_five
    if any(not domain for row in domains for domain in row):
        raise AssertionError("a residue-zero tile role has no oriented variants")
    return domains


def tile_class_domains(rows: list[str]) -> list[list[tuple[Tile, ...]]]:
    """Allow every alphabet orientation in each source tile's dihedral class."""
    n = len(rows)
    if n % 3 != 0 or any(len(row) != n for row in rows):
        raise ValueError("class domains require a square pattern divisible by three")
    tiles = production_tiles(oriented=True)
    domains = []
    for tile_r in range(n // 3):
        domain_row = []
        for tile_c in range(n // 3):
            block = tuple(
                rows[3 * tile_r + local_r][3 * tile_c : 3 * tile_c + 3]
                for local_r in range(3)
            )
            variants = tuple(tile for tile in tiles if tile.rows in orbit(block))
            if not variants:
                raise ValueError(
                    f"tile at ({tile_r}, {tile_c}) is outside the production alphabet"
                )
            domain_row.append(variants)
        domains.append(domain_row)
    return domains


def fix_source_band(
    domains: list[list[tuple[Tile, ...]]], rows: list[str], band_index: int
) -> None:
    """Restrict one domain row to the exact tile orientations in a source pattern."""
    tiles = {tile.rows: tile for tile in production_tiles(oriented=True)}
    tile_columns = len(domains)
    if band_index < 0:
        band_index += tile_columns
    if not 0 <= band_index < tile_columns:
        raise ValueError("source band index is out of range")
    for tile_c in range(tile_columns):
        block = tuple(
            rows[3 * band_index + local_r][3 * tile_c : 3 * tile_c + 3]
            for local_r in range(3)
        )
        if block not in tiles:
            raise ValueError(
                f"tile at ({band_index}, {tile_c}) is outside the production alphabet"
            )
        domains[band_index][tile_c] = (tiles[block],)


def analyze_masks(masks: list[int], n: int) -> FrontierState | None:
    if len(masks) != n:
        raise ValueError("a square pattern must have n row masks")
    state: FrontierState | None = initial_state(n)
    for mask in masks:
        if state is None:
            return None
        state = advance_row(state, mask)
    return state


def analyze_rows(rows: list[str]) -> FrontierState | None:
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("pattern must be square")
    return analyze_masks([row_mask(row) for row in rows], n)


def band_trace(rows: list[str]) -> list[FrontierState | None]:
    """Return states after each maximal group of three rows."""
    n = len(rows)
    masks = [row_mask(row) for row in rows]
    state: FrontierState | None = initial_state(n)
    trace = []
    for start in range(0, n, 3):
        for mask in masks[start : start + 3]:
            if state is None:
                break
            state = advance_row(state, mask)
        trace.append(state)
        if state is None:
            break
    return trace


def compress_mask(mask: int, start: int, width: int) -> int:
    """Delete one contiguous bit interval and close the remaining gap."""
    if start < 0 or width < 0:
        raise ValueError("mask deletion interval must be nonnegative")
    lower = mask & ((1 << start) - 1)
    upper = mask >> (start + width)
    return lower | (upper << start)


def canonicalize_partition_labels(partition: tuple[int, ...]) -> tuple[int, ...]:
    """Relabel a partition by first occurrence after projecting its nodes."""
    labels: dict[int, int] = {}
    return tuple(labels.setdefault(label, len(labels)) for label in partition)


def projected_frontier_key(
    state: FrontierState,
    slab_start: int,
    slab_width: int = 3,
    removed_u_cost: int = 0,
) -> tuple[int, int, tuple[int, ...], int, int]:
    """Project a frontier through deletion of a vertex/face slab.

    This is a cross-width comparison key, not a safe synthesis deduplication key.
    `slab_start` deletes equally indexed mask columns and frontier-face entries.
    """
    return frontier_key(
        project_frontier_state(state, slab_start, slab_width, removed_u_cost)
    )


def project_frontier_state(
    state: FrontierState,
    slab_start: int,
    slab_width: int = 3,
    removed_u_cost: int = 0,
) -> FrontierState:
    """Materialize the diagnostic deletion used for cross-width comparison.

    The result is not a safe synthesis quotient: deleted faces can hide
    attachment information needed by arbitrary future transitions.
    """
    if slab_width <= 0 or slab_start < 0 or slab_start + slab_width > state.n:
        raise ValueError("frontier slab must be a nonempty interval within the grid")
    if removed_u_cost < 0 or removed_u_cost > state.u_cost:
        raise ValueError("removed U cost must lie within the accumulated cost")
    face_partition = state.partition[1:]
    if face_partition and slab_start + slab_width > len(face_partition):
        raise ValueError("frontier slab extends beyond the exposed face row")
    projected_partition = (
        state.partition[:1]
        + face_partition[:slab_start]
        + face_partition[slab_start + slab_width :]
    )
    return FrontierState(
        n=state.n - slab_width,
        row_index=state.row_index,
        previous_u_mask=compress_mask(
            state.previous_u_mask, slab_start, slab_width
        ),
        partition=canonicalize_partition_labels(projected_partition),
        u_cost=state.u_cost - removed_u_cost,
        cycle_excess=state.cycle_excess,
    )


def frontier_key(state: FrontierState) -> tuple[int, int, tuple[int, ...], int, int]:
    """Return the unprojected counterpart of `projected_frontier_key`."""
    return (
        state.row_index,
        state.previous_u_mask,
        state.partition,
        state.u_cost,
        state.cycle_excess,
    )


def compare_residue_zero_traces(old_n: int, new_n: int) -> None:
    """Print exact projected frontier matches between cached residue-zero witnesses."""
    if new_n != old_n + 3:
        raise ValueError("trace comparison currently requires new_n = old_n + 3")
    old_rows = residue_zero_explicit_pattern(old_n)
    new_rows = residue_zero_explicit_pattern(new_n)
    old_trace = band_trace(old_rows)
    new_trace = band_trace(new_rows)
    print(f"residue-zero frontier projection n={old_n}->{new_n}")
    for band_index, (old_state, new_state) in enumerate(
        zip(old_trace, new_trace), start=1
    ):
        if old_state is None or new_state is None:
            print(f"band={band_index} sealed component")
            continue
        matches = []
        processed_rows = 3 * band_index
        for slab_start in range(old_n - 2):
            removed = sum(
                row[slab_start : slab_start + 3].count("U")
                for row in new_rows[:processed_rows]
            )
            if projected_frontier_key(new_state, slab_start, 3, removed) == frontier_key(
                old_state
            ):
                matches.append((slab_start, removed))
        print(
            f"band={band_index} old_U={old_state.u_cost} new_U={new_state.u_cost} "
            f"old_cycles={old_state.cycle_excess} new_cycles={new_state.cycle_excess} "
            f"matches={matches}"
        )


def verify_against_canonical(max_n: int = 4) -> int:
    """Exhaustively compare grammar connectivity with the canonical checker."""
    checked = 0
    for n in range(2, max_n + 1):
        for masks in product(range(1 << n), repeat=n):
            rows = [render_mask(mask, n) for mask in masks]
            canonical_ok, _, _ = dual_connectivity_check(rows)
            state = analyze_masks(list(masks), n)
            grammar_ok = state is not None and state.finished
            if grammar_ok != canonical_ok:
                raise AssertionError(
                    f"frontier mismatch at n={n}: canonical={canonical_ok}, "
                    f"grammar={grammar_ok}, rows={rows}"
                )
            if grammar_ok and state is not None:
                dual_edges = 0
                for r in range(n):
                    dual_edges += (masks[r] & (masks[r] >> 1)).bit_count()
                    if r > 0:
                        dual_edges += (masks[r - 1] & masks[r]).bit_count()
                expected_excess = dual_edges - (1 + (n - 1) ** 2) + 1
                if state.cycle_excess != expected_excess:
                    raise AssertionError(
                        f"cycle mismatch at n={n}: state={state.cycle_excess}, "
                        f"expected={expected_excess}, rows={rows}"
                    )
            checked += 1
    return checked


def verify_streamed_transitions(oriented: bool = False) -> int:
    """Compare streamed and complete transitions at both bands of a 6x6 grid."""
    tiles = production_tiles(oriented)
    domains = [tiles, tiles]
    incoming_states: dict[
        tuple[int, tuple[int, ...], int, int], FrontierState
    ] = {}
    direct_top = set()
    for choice in product(*domains):
        outgoing = advance_band(initial_state(6), tile_band_masks(choice))
        if outgoing is not None:
            key = grammar_key(outgoing)
            direct_top.add(key)
            incoming_states.setdefault(key, outgoing)
    streamed_top, _ = stream_band_domains(initial_state(6), domains)
    if {grammar_key(outgoing) for outgoing, _, _ in streamed_top} != direct_top:
        raise AssertionError("streamed top-band transitions differ from advance_band")

    checked = 1
    for incoming in incoming_states.values():
        direct_bottom = set()
        for choice in product(*domains):
            outgoing = advance_band(incoming, tile_band_masks(choice))
            if outgoing is not None:
                direct_bottom.add(grammar_key(outgoing))
        streamed_bottom, _ = stream_band_domains(incoming, domains)
        if {
            grammar_key(outgoing) for outgoing, _, _ in streamed_bottom
        } != direct_bottom:
            raise AssertionError(
                f"streamed bottom-band transitions differ at {grammar_key(incoming)}"
            )
        checked += 1
    return checked


def verify_streamed_row_packets() -> RowPacketVerification:
    """Exhaustively compare packet streaming with ``advance_row``.

    The primary checks cover every basic and center-seam mutable n=20 row from
    both fixed cap states. A one-packet n=5 check additionally covers the
    initial state and every possible one-row incoming frontier.
    """
    checked_rows = 0
    sealed_rows = 0
    attempted_transitions = 0
    incoming_count = 0

    def compare(
        incoming: FrontierState,
        prefix: str,
        suffix: str,
        domain_count: int,
        alphabet: Mapping[str, str] = ROW_PACKET_ALPHABET,
    ) -> None:
        nonlocal checked_rows, sealed_rows, attempted_transitions, incoming_count
        names_in_alphabet = tuple(alphabet)
        domains = [names_in_alphabet] * domain_count
        streamed, attempted = stream_row_packets(
            incoming, prefix, suffix, domains, packet_alphabet=alphabet
        )
        attempted_transitions += attempted
        incoming_count += 1
        actual = {item.row_mask: item for item in streamed}
        if len(actual) != len(streamed):
            raise AssertionError("packet stream returned duplicate complete row masks")

        expected_masks = set()
        for names in product(names_in_alphabet, repeat=domain_count):
            middle = "".join(alphabet[name] for name in names)
            mask = row_mask(prefix + middle + suffix)
            direct = advance_row(incoming, mask)
            checked_rows += 1
            if direct is None:
                sealed_rows += 1
                if mask in actual:
                    raise AssertionError(
                        f"stream retained a directly sealed row: n={incoming.n}, "
                        f"incoming={frontier_key(incoming)}, row={render_mask(mask, incoming.n)}"
                    )
                continue
            expected_masks.add(mask)
            item = actual.get(mask)
            expected_charge = sum(
                alphabet[name].count("U") - 2 for name in names
            )
            if item is None or (
                item.outgoing != direct
                or item.row_mask != direct.previous_u_mask
                or item.packet_names != names
                or item.packet_charge != expected_charge
                or item.h_count != sum(alphabet[name].count("U") == 3 for name in names)
            ):
                raise AssertionError(
                    f"packet transition mismatch: n={incoming.n}, "
                    f"incoming={frontier_key(incoming)}, row={render_mask(mask, incoming.n)}, "
                    f"direct={direct}, streamed={item}"
                )
        extra = set(actual) - expected_masks
        if extra:
            raise AssertionError(f"packet stream produced unexpected masks: {sorted(extra)}")

    rows = residue_two_affine_pattern(20)
    top = initial_state(20)
    for row in rows[:3]:
        advanced = advance_row(top, row_mask(row))
        if advanced is None:
            raise AssertionError("fixed n=20 top state sealed unexpectedly")
        top = advanced
    reflected_bottom = initial_state(20)
    for row in reversed(rows[-2:]):
        advanced = advance_row(reflected_bottom, row_mask(row))
        if advanced is None:
            raise AssertionError("reflected n=20 bottom state sealed unexpectedly")
        reflected_bottom = advanced
    compare(top, ".", ".", 6)
    compare(reflected_bottom, ".", ".", 6)
    phase_alphabet = {**ROW_PACKET_ALPHABET, "S": ".U."}
    compare(top, ".", ".", 6, phase_alphabet)
    compare(reflected_bottom, ".", ".", 6, phase_alphabet)

    compare(initial_state(5), ".", ".", 1)
    for previous_mask in range(1 << 5):
        incoming = advance_row(initial_state(5), previous_mask)
        if incoming is None:
            raise AssertionError("a first row cannot seal a dual component")
        compare(incoming, ".", ".", 1)

    return RowPacketVerification(
        incoming_states=incoming_count,
        checked_rows=checked_rows,
        sealed_rows=sealed_rows,
        attempted_transitions=attempted_transitions,
    )


def verify_bidirectional_merge(max_n: int = 3) -> int:
    """Compare every possible row cut with ordinary full-pattern analysis."""
    checked = 0
    for n in range(2, max_n + 1):
        for masks in product(range(1 << n), repeat=n):
            complete = analyze_masks(list(masks), n)
            for cut in range(1, n):
                forward: FrontierState | None = initial_state(n)
                for mask in masks[:cut]:
                    if forward is not None:
                        forward = advance_row(forward, mask)
                backward: FrontierState | None = initial_state(n)
                for mask in reversed(masks[cut:]):
                    if backward is not None:
                        backward = advance_row(backward, mask)
                merged_ok = False
                merged_cycles = -1
                if forward is not None and backward is not None:
                    merged_ok, merged_cycles = merge_frontiers(forward, backward)
                complete_ok = complete is not None
                if merged_ok != complete_ok:
                    raise AssertionError(
                        f"bidirectional connectivity mismatch at n={n}, cut={cut}, "
                        f"masks={masks}"
                    )
                if complete is not None and merged_cycles != complete.cycle_excess:
                    raise AssertionError(
                        f"bidirectional cycle mismatch at n={n}, cut={cut}, "
                        f"merged={merged_cycles}, complete={complete.cycle_excess}, "
                        f"masks={masks}"
                    )
                checked += 1
    return checked


def print_trace(n: int) -> None:
    rows = residue_two_explicit_pattern(n)
    canonical_ok, _, _ = dual_connectivity_check(rows)
    print(f"n={n} canonical_dual={canonical_ok}")
    for band, state in enumerate(band_trace(rows)):
        if state is None:
            print(f"band {band}: sealed component")
            return
        print(
            f"band {band}: rows={state.row_index} U={state.u_cost} "
            f"cycles={state.cycle_excess} prev={render_mask(state.previous_u_mask, n)} "
            f"partition={state.partition}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--verify-streamed", action="store_true")
    parser.add_argument("--verify-row-packets", action="store_true")
    parser.add_argument("--verify-bidirectional", action="store_true")
    parser.add_argument("--max-n", type=int, default=4)
    parser.add_argument("--trace", type=int, choices=(5, 8, 11, 14))
    parser.add_argument("--compare-zero", type=int, nargs=2, metavar=("OLD", "NEW"))
    parser.add_argument("--synthesize", type=int)
    parser.add_argument("--beam", type=int, default=5000)
    parser.add_argument("--oriented", action="store_true")
    parser.add_argument("--zero-template", type=int)
    parser.add_argument("--zero-wide", type=int)
    parser.add_argument("--zero-bidirectional", type=int)
    parser.add_argument("--class-pattern", type=Path)
    parser.add_argument("--fix-bottom-band", action="store_true")
    args = parser.parse_args()
    if args.verify:
        checked = verify_against_canonical(args.max_n)
        print(f"verified {checked} patterns through n={args.max_n}")
    if args.verify_streamed:
        checked = verify_streamed_transitions(oriented=args.oriented)
        alphabet = "oriented" if args.oriented else "canonical"
        print(f"verified {checked} streamed {alphabet} transition sets")
    if args.verify_row_packets:
        result = verify_streamed_row_packets()
        print(
            f"verified {result.checked_rows} packet rows from "
            f"{result.incoming_states} incoming states; sealed={result.sealed_rows} "
            f"attempted={result.attempted_transitions}"
        )
    if args.verify_bidirectional:
        checked = verify_bidirectional_merge(args.max_n)
        print(f"verified {checked} bidirectional cuts through n={args.max_n}")
    if args.trace is not None:
        print_trace(args.trace)
    if args.compare_zero is not None:
        compare_residue_zero_traces(*args.compare_zero)
    if args.synthesize is not None:
        rows, names, transitions = synthesize_tiled(
            args.synthesize, args.beam, oriented=args.oriented
        )
        print(f"synthesis transitions={transitions}")
        if rows is None:
            print("no tiled witness found")
        else:
            info = run_check(args.synthesize, rows, verbose=True)
            print(f"tile bands={names}")
            for row in rows:
                print(row)
            if not info["all_ok"]:
                raise SystemExit("grammar produced an invalid witness")
    if args.zero_template is not None:
        domains = residue_zero_template_domains(args.zero_template)
        rows, names, transitions = synthesize_domains(
            domains, q_formula(args.zero_template), args.beam
        )
        print(f"template transitions={transitions}")
        if rows is None:
            print("no template witness found")
        else:
            info = run_check(args.zero_template, rows, verbose=True)
            state = analyze_rows(rows)
            print(f"grammar cycles={state.cycle_excess if state else 'invalid'}")
            print(f"tile bands={names}")
            for row in rows:
                print(row)
            if not info["all_ok"]:
                raise SystemExit("template grammar produced an invalid witness")
    if args.zero_wide is not None:
        domains = residue_zero_wide_domains(args.zero_wide)
        rows, names, transitions = synthesize_domains(
            domains, q_formula(args.zero_wide), args.beam
        )
        print(f"wide-domain transitions={transitions}")
        if rows is None:
            print("no wide-domain witness found")
        else:
            info = run_check(args.zero_wide, rows, verbose=True)
            state = analyze_rows(rows)
            print(f"grammar cycles={state.cycle_excess if state else 'invalid'}")
            print(f"tile bands={names}")
            for row in rows:
                print(row)
            if not info["all_ok"]:
                raise SystemExit("wide-domain grammar produced an invalid witness")
    if args.zero_bidirectional is not None:
        domains = residue_zero_wide_domains(args.zero_bidirectional)
        rows, names, transitions, side_counts = synthesize_domains_bidirectional(
            domains,
            q_formula(args.zero_bidirectional),
            None if args.beam <= 0 else args.beam,
        )
        print(
            f"bidirectional transitions={transitions} "
            f"forward_states={side_counts[0]} backward_states={side_counts[1]}"
        )
        if rows is None:
            qualifier = "exhaustive" if args.beam <= 0 else "beam-limited"
            print(f"no {qualifier} bidirectional witness found")
        else:
            info = run_check(args.zero_bidirectional, rows, verbose=True)
            state = analyze_rows(rows)
            print(f"grammar cycles={state.cycle_excess if state else 'invalid'}")
            print(f"tile bands={names}")
            for row in rows:
                print(row)
            if not info["all_ok"]:
                raise SystemExit("bidirectional grammar produced an invalid witness")
    if args.class_pattern is not None:
        source_rows = [
            line.strip()
            for line in args.class_pattern.read_text().splitlines()
            if line.strip()
        ]
        n = len(source_rows)
        domains = tile_class_domains(source_rows)
        if args.fix_bottom_band:
            fix_source_band(domains, source_rows, -1)
        rows, names, transitions, side_counts = synthesize_domains_bidirectional(
            domains,
            q_formula(n),
            None if args.beam <= 0 else args.beam,
        )
        print(
            f"class transitions={transitions} "
            f"forward_states={side_counts[0]} backward_states={side_counts[1]}"
        )
        if rows is None:
            qualifier = "exhaustive" if args.beam <= 0 else "beam-limited"
            print(f"no {qualifier} class-neighborhood witness found")
        else:
            info = run_check(n, rows, verbose=True)
            state = analyze_rows(rows)
            print(f"grammar cycles={state.cycle_excess if state else 'invalid'}")
            print(f"tile bands={names}")
            for row in rows:
                print(row)
            if not info["all_ok"]:
                raise SystemExit("class-neighborhood grammar produced an invalid witness")
    if (
        not args.verify
        and not args.verify_streamed
        and not args.verify_row_packets
        and not args.verify_bidirectional
        and args.trace is None
        and args.compare_zero is None
        and args.synthesize is None
        and args.zero_template is None
        and args.zero_wide is None
        and args.zero_bidirectional is None
        and args.class_pattern is None
    ):
        parser.error(
            "choose --verify, --verify-streamed, --verify-row-packets, "
            "--verify-bidirectional, --trace, --compare-zero, --synthesize, "
            "--zero-template, --zero-wide, --zero-bidirectional, and/or --class-pattern"
        )
    if args.fix_bottom_band and args.class_pattern is None:
        parser.error("--fix-bottom-band requires --class-pattern")


if __name__ == "__main__":
    main()
