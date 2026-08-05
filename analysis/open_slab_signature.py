#!/usr/bin/env python3
"""Lossless diagnostic signatures for forgetting a frontier slab interface."""

from __future__ import annotations

from dataclasses import dataclass

from tile_grammar import (
    FrontierState,
    canonicalize_partition_labels,
    compress_mask,
)


@dataclass(frozen=True, slots=True)
class OpenSlabSignature:
    original_n: int
    row_index: int
    slab_start: int
    slab_width: int
    compressed_previous_u_mask: int
    slab_previous_u_mask: int
    projected_partition: tuple[int, ...]
    attachment_partition: tuple[int, ...]
    normalized_u_cost: int
    removed_u_cost: int
    cycle_excess: int


def _validate_state(state: FrontierState, slab_start: int, slab_width: int) -> None:
    if state.n < 2 or not 0 <= state.row_index <= state.n:
        raise ValueError("frontier dimensions or row index are invalid")
    if state.previous_u_mask < 0 or state.previous_u_mask >= 1 << state.n:
        raise ValueError("previous-row mask does not fit the frontier width")
    if state.u_cost < 0 or state.cycle_excess < 0:
        raise ValueError("frontier costs and cycle excess must be nonnegative")
    if slab_width <= 0 or slab_start < 0:
        raise ValueError("frontier slab must be a nonempty nonnegative interval")
    if len(state.partition) != state.n:
        raise ValueError("open-slab signatures require a full exposed face frontier")
    if slab_start + slab_width > state.n - 1:
        raise ValueError("frontier slab extends beyond the exposed face row")
    if canonicalize_partition_labels(state.partition) != state.partition:
        raise ValueError("frontier partition must be canonical")


def extract_open_slab_signature(
    state: FrontierState,
    slab_start: int,
    slab_width: int = 3,
    removed_u_cost: int = 0,
) -> OpenSlabSignature:
    """Forget slab ports while retaining enough data to restore the exact state."""
    _validate_state(state, slab_start, slab_width)
    if removed_u_cost < 0 or removed_u_cost > state.u_cost:
        raise ValueError("removed U cost must lie within the accumulated cost")

    hidden = set(range(1 + slab_start, 1 + slab_start + slab_width))
    retained_indices = [index for index in range(state.n) if index not in hidden]
    retained_labels = tuple(state.partition[index] for index in retained_indices)
    projected_partition = canonicalize_partition_labels(retained_labels)
    projected_count = len(set(projected_partition))

    original_by_projected = [None] * projected_count
    for projected, original in zip(projected_partition, retained_labels, strict=True):
        if original_by_projected[projected] is None:
            original_by_projected[projected] = original
    if any(label is None for label in original_by_projected):
        raise AssertionError("projected partition labels are not contiguous")
    hidden_labels = tuple(state.partition[index] for index in sorted(hidden))
    attachment_partition = canonicalize_partition_labels(
        (*original_by_projected, *hidden_labels)
    )

    return OpenSlabSignature(
        original_n=state.n,
        row_index=state.row_index,
        slab_start=slab_start,
        slab_width=slab_width,
        compressed_previous_u_mask=compress_mask(
            state.previous_u_mask, slab_start, slab_width
        ),
        slab_previous_u_mask=(
            state.previous_u_mask >> slab_start
        ) & ((1 << slab_width) - 1),
        projected_partition=projected_partition,
        attachment_partition=attachment_partition,
        normalized_u_cost=state.u_cost - removed_u_cost,
        removed_u_cost=removed_u_cost,
        cycle_excess=state.cycle_excess,
    )


def restore_open_slab_state(signature: OpenSlabSignature) -> FrontierState:
    """Restore the concrete frontier represented by a lossless open-slab signature."""
    if signature.original_n < 2 or not 0 <= signature.row_index <= signature.original_n:
        raise ValueError("frontier dimensions or row index are invalid")
    if signature.slab_width <= 0 or signature.slab_start < 0:
        raise ValueError("frontier slab must be a nonempty nonnegative interval")
    if signature.slab_start + signature.slab_width > signature.original_n - 1:
        raise ValueError("frontier slab extends beyond the exposed face row")
    if signature.normalized_u_cost < 0 or signature.removed_u_cost < 0:
        raise ValueError("U costs must be nonnegative")
    retained_width = signature.original_n - signature.slab_width
    if (
        signature.slab_previous_u_mask < 0
        or signature.slab_previous_u_mask >= 1 << signature.slab_width
    ):
        raise ValueError("slab mask does not fit its declared width")
    if (
        signature.compressed_previous_u_mask < 0
        or signature.compressed_previous_u_mask >= 1 << retained_width
    ):
        raise ValueError("compressed mask does not fit the retained width")
    if canonicalize_partition_labels(signature.projected_partition) != signature.projected_partition:
        raise ValueError("projected partition must be canonical")
    if canonicalize_partition_labels(signature.attachment_partition) != signature.attachment_partition:
        raise ValueError("attachment partition must be canonical")

    projected_count = len(set(signature.projected_partition))
    if len(signature.attachment_partition) != projected_count + signature.slab_width:
        raise ValueError("attachment partition has the wrong number of tokens")
    projected_tokens = signature.attachment_partition[:projected_count]
    if len(set(projected_tokens)) != projected_count:
        raise ValueError("attachment partition merges distinct projected components")
    expected_projected_length = signature.original_n - signature.slab_width
    if len(signature.projected_partition) != expected_projected_length:
        raise ValueError("projected partition has the wrong frontier width")

    lower_mask = signature.compressed_previous_u_mask & (
        (1 << signature.slab_start) - 1
    )
    upper_mask = signature.compressed_previous_u_mask >> signature.slab_start
    previous_u_mask = (
        lower_mask
        | (signature.slab_previous_u_mask << signature.slab_start)
        | (upper_mask << (signature.slab_start + signature.slab_width))
    )
    if previous_u_mask >= 1 << signature.original_n:
        raise ValueError("restored mask does not fit the frontier width")

    full_labels = []
    retained_cursor = 0
    hidden_cursor = 0
    for full_index in range(signature.original_n):
        if 1 + signature.slab_start <= full_index < 1 + signature.slab_start + signature.slab_width:
            token = projected_count + hidden_cursor
            hidden_cursor += 1
        else:
            projected_label = signature.projected_partition[retained_cursor]
            retained_cursor += 1
            token = projected_label
        full_labels.append(signature.attachment_partition[token])

    return FrontierState(
        n=signature.original_n,
        row_index=signature.row_index,
        previous_u_mask=previous_u_mask,
        partition=canonicalize_partition_labels(tuple(full_labels)),
        u_cost=signature.normalized_u_cost + signature.removed_u_cost,
        cycle_excess=signature.cycle_excess,
    )


def verify_open_slab_round_trip(
    state: FrontierState,
    slab_start: int,
    slab_width: int = 3,
    removed_u_cost: int = 0,
) -> OpenSlabSignature:
    signature = extract_open_slab_signature(
        state, slab_start, slab_width, removed_u_cost
    )
    if restore_open_slab_state(signature) != state:
        raise AssertionError("open-slab signature did not round-trip")
    return signature
