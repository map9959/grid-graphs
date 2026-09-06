#!/usr/bin/env python3
"""Exact coupled frontier grammar for the two forced-forest component systems.

For a selected full-degree set ``F``, ``H`` contains every grid edge having at
least one endpoint in ``F``.  A state retains the active-frontier connectivity
of both ``H`` and the induced graph ``G[F]``.  Component labels are canonical;
components absent from the new frontier retire and are returned as transition
deltas rather than retained by name.

This is a finite discovery model.  It does not assert an arbitrary-width bound.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from analysis.bounds.forced_forest_row_grammar import (
    Partition,
    State,
    _canonical_partition,
    _DisjointSet,
    _validate_mask,
    first_row_state,
    transition,
)


@dataclass(frozen=True)
class CoupledState:
    forced_mask: int
    h_partition: Partition
    f_partition: Partition
    retired_h: int = 0
    retired_f: int = 0
    forced_boundary_deficiency: int = 0


@dataclass(frozen=True)
class CoupledTransition:
    state: CoupledState
    retired_h: int
    retired_f: int
    merged_h: int
    merged_f: int


def _canonical_optional_partition(
    dsu: _DisjointSet, vertices: range, active_mask: int, offset: int = 0
) -> Partition:
    active = [vertex for vertex in vertices if active_mask & (1 << (vertex - offset))]
    labels: dict[int, int] = {}
    result = []
    for vertex in vertices:
        if not active_mask & (1 << (vertex - offset)):
            result.append(-1)
            continue
        root = dsu.find(vertex)
        if root not in labels:
            labels[root] = len(labels)
        result.append(labels[root])
    assert len(active) == sum(label >= 0 for label in result)
    return tuple(result)


def _label_count(partition: Partition) -> int:
    return len({label for label in partition if label >= 0})


def _side_deficiency(width: int, forced_mask: int) -> int:
    return int(bool(forced_mask & 1)) + int(
        bool(forced_mask & (1 << (width - 1)))
    )


def first_coupled_row_state(width: int, forced_mask: int) -> CoupledState | None:
    h_state = first_row_state(width, forced_mask)
    if h_state is None:
        return None
    dsu = _DisjointSet(width)
    for column in range(width - 1):
        if forced_mask & (3 << column) == 3 << column:
            if not dsu.union_edge(column, column + 1):
                return None
    return CoupledState(
        forced_mask,
        h_state.partition,
        _canonical_optional_partition(dsu, range(width), forced_mask),
        0,
        0,
        2 * forced_mask.bit_count() + _side_deficiency(width, forced_mask),
    )


def coupled_transition(
    width: int, state: CoupledState, forced_mask: int
) -> CoupledTransition | None:
    """Append one row and return both exact active component partitions."""
    _validate_mask(width, forced_mask)
    h_old = State(state.forced_mask, state.h_partition)
    h_new = transition(width, h_old, forced_mask)
    if h_new is None:
        return None

    dsu = _DisjointSet(2 * width)
    representatives: dict[int, int] = {}
    for column, label in enumerate(state.f_partition):
        if label < 0:
            continue
        if label in representatives:
            dsu.union_summary(representatives[label], column)
        else:
            representatives[label] = column

    for column in range(width):
        old_full = state.forced_mask & (1 << column)
        new_full = forced_mask & (1 << column)
        if old_full and new_full and not dsu.union_edge(column, width + column):
            raise AssertionError("G[F] cycle survived an acyclic H transition")
    for column in range(width - 1):
        if forced_mask & (3 << column) == 3 << column:
            if not dsu.union_edge(width + column, width + column + 1):
                raise AssertionError("G[F] cycle survived an acyclic H transition")

    f_new = _canonical_optional_partition(
        dsu, range(width, 2 * width), forced_mask, width
    )

    old_h = _label_count(state.h_partition)
    old_f = _label_count(state.f_partition)
    new_h = _label_count(h_new.partition)
    new_f = _label_count(f_new)

    # Restore H once more to read which old active blocks reach the new row.
    h_dsu = _DisjointSet(2 * width)
    h_representatives: dict[int, int] = {}
    for column, label in enumerate(state.h_partition):
        if label in h_representatives:
            h_dsu.union_summary(h_representatives[label], column)
        else:
            h_representatives[label] = column
    for column in range(width):
        if (state.forced_mask | forced_mask) & (1 << column):
            assert h_dsu.union_edge(column, width + column)
    for column in range(width - 1):
        if forced_mask & (3 << column):
            assert h_dsu.union_edge(width + column, width + column + 1)
    surviving_h_old = {
        label
        for column, label in enumerate(state.h_partition)
        if any(h_dsu.find(column) == h_dsu.find(width + new) for new in range(width))
    }
    surviving_f_old = {
        label
        for column, label in enumerate(state.f_partition)
        if label >= 0
        and any(dsu.find(column) == dsu.find(width + new) for new in range(width)
                if forced_mask & (1 << new))
    }

    # A merge is the reduction in surviving old blocks after adjoining the row.
    reached_h_new = {
        h_dsu.find(width + column)
        for column in range(width)
        if any(h_dsu.find(old) == h_dsu.find(width + column) for old in range(width))
    }
    reached_f_new = {
        dsu.find(width + column)
        for column in range(width)
        if forced_mask & (1 << column)
        and any(
            state.f_partition[old] >= 0
            and dsu.find(old) == dsu.find(width + column)
            for old in range(width)
        )
    }
    merged_h = len(surviving_h_old) - len(reached_h_new)
    merged_f = len(surviving_f_old) - len(reached_f_new)
    assert merged_h >= 0 and merged_f >= 0

    return CoupledTransition(
        CoupledState(
            forced_mask,
            h_new.partition,
            f_new,
            state.retired_h + old_h - len(surviving_h_old),
            state.retired_f + old_f - len(surviving_f_old),
            state.forced_boundary_deficiency
            - state.forced_mask.bit_count()
            + forced_mask.bit_count()
            + _side_deficiency(width, forced_mask),
        ),
        old_h - len(surviving_h_old),
        old_f - len(surviving_f_old),
        merged_h,
        merged_f,
    )


def validate_coupled_state(width: int, state: CoupledState) -> None:
    if len(state.h_partition) != width or len(state.f_partition) != width:
        raise ValueError("partition width mismatch")
    if any(
        bool(state.forced_mask & (1 << column)) !=
        (state.f_partition[column] >= 0)
        for column in range(width)
    ):
        raise ValueError("F partition support does not match the row mask")


def prefix_component_charge(row: int, state: CoupledState) -> int:
    """Exact accumulated row charge from the rectangular component identity."""
    if row <= 0:
        raise ValueError("row must be positive")
    active_h = _label_count(state.h_partition)
    active_f = _label_count(state.f_partition)
    return (
        3 * row
        - state.forced_boundary_deficiency
        + state.retired_h
        + active_h
        + state.retired_f
        + active_f
    )


def reachable_coupled_layers(width: int, height: int | None = None) -> list[set[CoupledState]]:
    """Enumerate all reachable coupled states without cost pruning."""
    if height is None:
        height = width
    if height <= 0:
        raise ValueError("height must be positive")
    first = {
        state
        for mask in range(1 << width)
        if (state := first_coupled_row_state(width, mask)) is not None
    }
    layers = [first]
    for _ in range(1, height):
        next_layer = set()
        for state in layers[-1]:
            for mask in range(1 << width):
                result = coupled_transition(width, state, mask)
                if result is not None:
                    next_layer.add(result.state)
        layers.append(next_layer)
    return layers


def reachable_coupled_transitions(
    width: int, incoming: Iterable[CoupledState]
) -> Iterable[tuple[CoupledState, int, CoupledTransition]]:
    for state in incoming:
        for mask in range(1 << width):
            result = coupled_transition(width, state, mask)
            if result is not None:
                yield state, mask, result
