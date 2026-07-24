#!/usr/bin/env python3
"""Search a cost-240 n=21 prefix against exact n=18-derived suffix caps."""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass

from construction_lab import q_formula, run_check
from diagonal_patterns import residue_zero_explicit_pattern
from tile_grammar import (
    FrontierState,
    PartialBandState,
    band_node_orders,
    band_trace,
    expand_domain_rows,
    frontier_key,
    grammar_key,
    initial_state,
    merge_frontier_partition,
    production_tiles,
    partial_band_key,
    project_frontier_state,
    projected_frontier_key,
    render_mask,
    stream_band_domains,
    suffix_u_costs,
)


@dataclass(frozen=True)
class Certificate:
    orientation: str
    slab_start: int


@dataclass(frozen=True)
class Cap:
    state: FrontierState
    backward_masks: tuple[int, int, int]
    names: tuple[str, ...]
    certificates: tuple[Certificate, ...]


@dataclass(frozen=True)
class PrefixNode:
    state: FrontierState
    masks: tuple[int, ...]
    names: tuple[tuple[str, ...], ...]


def rotate_two(rows: list[str]) -> list[str]:
    return [row[::-1] for row in reversed(rows)]


def rotate_two_reflected(rows: list[str]) -> list[str]:
    return list(reversed(rows))


def enumerate_target_caps() -> tuple[tuple[Cap, ...], dict[str, list[FrontierState]]]:
    """Return the exact 18 cap states and transformed n=18 traces."""
    tiles = production_tiles(oriented=True)
    five = tuple(tile for tile in tiles if tile.u_count == 5)
    states, transitions = expand_domain_rows(
        [[five] * 7],
        n=21,
        target_costs=frozenset((35,)),
        beam_width=None,
        max_cycle_excess=1,
    )
    if transitions != 59_952 or len(states) != 3_784:
        raise AssertionError(
            f"cap artifact changed: transitions={transitions}, states={len(states)}"
        )

    source = residue_zero_explicit_pattern(18)
    transformed = {
        "R2": rotate_two(source),
        "R2F": rotate_two_reflected(source),
    }
    traces = {
        name: [state for state in band_trace(rows) if state is not None]
        for name, rows in transformed.items()
    }
    targets = {name: frontier_key(trace[0]) for name, trace in traces.items()}

    records = []
    certificate_count = 0
    orientation_counts = defaultdict(int)
    for state, masks, names in states.values():
        certificates = []
        for orientation, target in targets.items():
            for slab_start in range(18):
                removed = sum(
                    ((mask >> slab_start) & 0b111).bit_count() for mask in masks
                )
                if projected_frontier_key(
                    state, slab_start, 3, removed
                ) != target:
                    continue
                certificates.append(Certificate(orientation, slab_start))
                certificate_count += 1
                orientation_counts[orientation] += 1
        if certificates:
            records.append(
                Cap(
                    state,
                    tuple(masks),  # type: ignore[arg-type]
                    tuple(names[0]),
                    tuple(certificates),
                )
            )
    if len(records) != 18 or certificate_count != 56:
        raise AssertionError(
            f"target cap artifact changed: caps={len(records)}, "
            f"certificates={certificate_count}"
        )
    if dict(orientation_counts) != {"R2": 27, "R2F": 29}:
        raise AssertionError(f"target orientation counts changed: {orientation_counts}")
    records.sort(key=lambda cap: grammar_key(cap.state))
    return tuple(records), traces


def partition_disagreement(
    left: tuple[int, ...], right: tuple[int, ...]
) -> int:
    if len(left) != len(right):
        raise ValueError("partitions must have equal lengths")
    return sum(
        (left[i] == left[j]) != (right[i] == right[j])
        for i in range(len(left))
        for j in range(i + 1, len(left))
    )


def bridge_capacity(state: FrontierState) -> int:
    total = 0
    for c in range(state.n):
        if not state.previous_u_mask & (1 << c):
            continue
        left = 0 if c == 0 else c
        right = 0 if c + 1 == state.n else c + 1
        total += state.partition[left] != state.partition[right]
    return total


def partial_metrics(
    state: FrontierState, partial: PartialBandState
) -> tuple[int, int, tuple[int, int, int], int, int, int, tuple]:
    """Summarize useful right ports and unresolved horizontal connectivity."""
    order_one, order_two, order_three, old, middle_one, middle_two = band_node_orders(
        state
    )
    new = (
        [("new", c) for c in range(state.n - 1)]
        if state.row_index + 3 < state.n
        else []
    )
    out = ("out", 0)
    gap = partial.columns - 1
    labels = (
        dict(zip(order_one, partial.partition_one)),
        dict(zip(order_two, partial.partition_two)),
        dict(zip(order_three, partial.partition_three)),
    )
    endpoints = (
        (out if state.row_index == 0 else old[gap], middle_one[gap]),
        (middle_one[gap], middle_two[gap]),
        (
            middle_two[gap],
            out if state.row_index + 3 == state.n else new[gap],
        ),
    )
    bridge_bits = tuple(
        int(partial.right_u[index] and label[a] != label[b])
        for index, (label, (a, b)) in enumerate(zip(labels, endpoints))
    )
    bridge_mask = sum(value << index for index, value in enumerate(bridge_bits))

    processed = (
        [out, *old[: partial.columns], *middle_one[: partial.columns]],
        [
            out,
            *old[: partial.columns],
            *middle_one[: partial.columns],
            *middle_two[: partial.columns],
        ],
        [
            out,
            *old[: partial.columns],
            *middle_one[: partial.columns],
            *middle_two[: partial.columns],
            *new[: partial.columns],
        ],
    )
    anchors = (
        [out, *old[gap:], *middle_one[gap:]],
        [out, *old[gap:], *middle_one[gap:], *middle_two[gap:]],
        [out, *old[gap:], *middle_one[gap:], *middle_two[gap:], *new[gap:]],
    )
    debts = []
    nonout = 0
    signatures = []
    for label, nodes, anchor_nodes, (a, b) in zip(
        labels, processed, anchors, endpoints
    ):
        node_labels = {label[node] for node in nodes}
        anchor_labels = {label[node] for node in anchor_nodes}
        debts.append(len(node_labels - anchor_labels))
        nonout += len(node_labels - {label[out]})
        signatures.append(
            (label[out] == label[a], label[out] == label[b], label[a] == label[b])
        )
    return (
        bridge_mask,
        sum(bridge_bits),
        tuple(debts),  # type: ignore[arg-type]
        max(debts),
        sum(debts),
        nonout,
        tuple(signatures),
    )


def round_robin_partial(
    candidates: tuple[PartialBandState, ...], width: int, bucket, score
) -> tuple[tuple, ...]:
    buckets: dict[tuple, list[PartialBandState]] = defaultdict(list)
    for partial in candidates:
        buckets[bucket(partial)].append(partial)
    for members in buckets.values():
        members.sort(key=score)
    selected = []
    round_index = 0
    while len(selected) < width:
        offers = [
            members[round_index]
            for members in buckets.values()
            if round_index < len(members)
        ]
        if not offers:
            break
        offers.sort(
            key=lambda partial: (
                score(partial), bucket(partial), partial_band_key(partial)
            )
        )
        selected.extend(offers[: width - len(selected)])
        round_index += 1
    return tuple(partial_band_key(partial) for partial in selected)


def make_partial_selector(policy: str):
    if policy == "legacy":
        return None

    def selector(
        state: FrontierState,
        tiles_done: int,
        candidates: tuple[PartialBandState, ...],
        width: int,
    ) -> tuple[tuple, ...]:
        del tiles_done
        metrics = {partial_band_key(item): partial_metrics(state, item) for item in candidates}

        def values(item: PartialBandState):
            return metrics[partial_band_key(item)]

        if policy == "bridge":
            ranked = sorted(
                candidates,
                key=lambda item: (
                    item.cycle_excess,
                    -values(item)[1],
                    values(item)[3],
                    values(item)[4],
                    values(item)[5],
                    partial_band_key(item),
                ),
            )
            return tuple(partial_band_key(item) for item in ranked[:width])
        if policy == "port":
            return round_robin_partial(
                candidates,
                width,
                lambda item: (
                    item.u_cost,
                    item.cycle_excess,
                    item.right_u,
                    values(item)[0],
                    values(item)[6],
                ),
                lambda item: (
                    values(item)[3],
                    values(item)[4],
                    values(item)[5],
                    -values(item)[1],
                    partial_band_key(item),
                ),
            )
        if policy == "obligation":
            return round_robin_partial(
                candidates,
                width,
                lambda item: (
                    item.u_cost,
                    item.cycle_excess,
                    values(item)[0],
                    tuple(min(value, 2) for value in values(item)[2]),
                ),
                lambda item: (
                    values(item)[3],
                    values(item)[4],
                    -values(item)[1],
                    values(item)[5],
                    values(item)[6],
                    partial_band_key(item),
                ),
            )
        raise ValueError(f"unknown partial policy {policy}")

    return selector


def trace_score(
    node: PrefixNode,
    band_number: int,
    traces: dict[str, list[FrontierState]],
    certificate_pairs: tuple[Certificate, ...],
) -> tuple:
    best = None
    for certificate in certificate_pairs:
        target = traces[certificate.orientation][band_number - 1]
        removed = sum(
            ((mask >> certificate.slab_start) & 0b111).bit_count()
            for mask in node.masks
        )
        projected = project_frontier_state(
            node.state, certificate.slab_start, 3, removed
        )
        score = (
            abs(projected.cycle_excess - target.cycle_excess),
            partition_disagreement(projected.partition, target.partition),
            (projected.previous_u_mask ^ target.previous_u_mask).bit_count(),
            abs(projected.u_cost - target.u_cost),
        )
        if best is None or score < best:
            best = score
    assert best is not None
    return (
        *best,
        abs(node.state.u_cost - 40 * band_number),
        len(set(node.state.partition)),
        -bridge_capacity(node.state),
        grammar_key(node.state),
        node.names,
    )


def cap_score(node: PrefixNode, caps: tuple[Cap, ...]) -> tuple:
    best = min(
        (
            len(set(partition)),
            cycles,
        )
        for cap in caps
        for partition, cycles in (merge_frontier_partition(node.state, cap.state),)
    )
    return (*best, len(set(node.state.partition)), grammar_key(node.state), node.names)


def select_diverse(
    nodes: list[PrefixNode], width: int, score
) -> dict[tuple, PrefixNode]:
    """Retain exact-partition diversity with deterministic round-robin selection."""
    deduplicated: dict[tuple, PrefixNode] = {}
    for node in nodes:
        key = grammar_key(node.state)
        old = deduplicated.get(key)
        if old is None or node.names < old.names:
            deduplicated[key] = node
    buckets: dict[tuple, list[PrefixNode]] = defaultdict(list)
    for node in deduplicated.values():
        bucket = (node.state.u_cost, node.state.cycle_excess, node.state.partition)
        buckets[bucket].append(node)
    for members in buckets.values():
        members.sort(key=score)

    selected = []
    round_index = 0
    while len(selected) < width:
        offers = [
            members[round_index]
            for members in buckets.values()
            if round_index < len(members)
        ]
        if not offers:
            break
        offers.sort(
            key=lambda node: (
                score(node),
                node.state.partition,
                grammar_key(node.state),
                node.names,
            )
        )
        selected.extend(offers[: width - len(selected)])
        round_index += 1
    return {grammar_key(node.state): node for node in selected}


def find_join(node: PrefixNode, caps: tuple[Cap, ...]):
    best = None
    for cap in caps:
        partition, cycles = merge_frontier_partition(node.state, cap.state)
        result = (len(set(partition)), cycles, partition, cap)
        if best is None or result[:2] < best[:2]:
            best = result
        if result[0] == 1 and cycles <= 1:
            return result
    return best


def build_forward_levels(
    traces: dict[str, list[FrontierState]],
    caps: tuple[Cap, ...],
    band_beams: tuple[int, ...],
    partial_beam: int,
    partial_policy: str,
) -> tuple[dict[int, dict[tuple, PrefixNode]], int]:
    """Build guided forward layers through band five for multicut joins."""
    tiles = production_tiles(oriented=True)
    domains = [[tiles] * 7 for _ in range(6)]
    remaining = suffix_u_costs(domains)
    certificates = tuple(
        sorted(
            {certificate for cap in caps for certificate in cap.certificates},
            key=lambda item: (item.orientation, item.slab_start),
        )
    )
    start = initial_state(21)
    states = {grammar_key(start): PrefixNode(start, (), ())}
    levels = {0: states}
    transitions = 0
    selector = make_partial_selector(partial_policy)
    for band_index in range(5):
        candidates = []
        suffix_start = band_index * 7
        for node in states.values():
            outgoing, attempted = stream_band_domains(
                node.state,
                domains[band_index],
                max_u_cost=240,
                max_cycle_excess=1,
                remaining_u_costs=remaining[suffix_start : suffix_start + 8],
                target_u_costs=frozenset((240,)),
                partial_beam_width=partial_beam,
                partial_selector=selector,
            )
            transitions += attempted
            candidates.extend(
                PrefixNode(state, (*node.masks, *masks), (*node.names, names))
                for state, masks, names in outgoing
            )
        score = lambda item: trace_score(
            item, band_index + 1, traces, certificates
        )
        states = select_diverse(candidates, band_beams[band_index], score)
        levels[band_index + 1] = states
        if not states:
            break
    return levels, transitions


def build_backward_levels(
    caps: tuple[Cap, ...],
    through_bands: int,
    width: int,
    partial_beam: int,
    partial_policy: str,
) -> tuple[dict[int, dict[tuple, PrefixNode]], int]:
    """Expand exact caps inward in reflected bottom-up coordinates."""
    tiles = production_tiles(oriented=True)
    domain_row = [tiles] * 7
    remaining = suffix_u_costs([domain_row])
    states = {
        grammar_key(cap.state): PrefixNode(
            cap.state, cap.backward_masks, (cap.names,)
        )
        for cap in caps
    }
    levels = {1: states}
    transitions = 0
    selector = make_partial_selector(partial_policy)

    def backward_score(item: PrefixNode) -> tuple:
        return (
            len(set(item.state.partition)),
            item.state.cycle_excess,
            -bridge_capacity(item.state),
            item.state.u_cost,
            grammar_key(item.state),
            item.names,
        )

    for band_count in range(2, through_bands + 1):
        forward_bands = 7 - band_count
        target_costs = frozenset(
            range(275 - 42 * forward_bands, 275 - 35 * forward_bands + 1)
        )
        candidates = []
        for node in states.values():
            outgoing, attempted = stream_band_domains(
                node.state,
                domain_row,
                max_u_cost=max(target_costs),
                max_cycle_excess=1,
                remaining_u_costs=remaining,
                target_u_costs=target_costs,
                partial_beam_width=partial_beam,
                partial_selector=selector,
            )
            transitions += attempted
            candidates.extend(
                PrefixNode(state, (*node.masks, *masks), (*node.names, names))
                for state, masks, names in outgoing
            )
        states = select_diverse(candidates, width, backward_score)
        levels[band_count] = states
        if not states:
            break
    return levels, transitions


def best_multicut_join(
    forward: dict[tuple, PrefixNode], backward: dict[tuple, PrefixNode]
):
    backward_by_cost: dict[int, list[PrefixNode]] = defaultdict(list)
    for node in backward.values():
        backward_by_cost[node.state.u_cost].append(node)
    best = None
    pairs = 0
    for front in forward.values():
        for back in backward_by_cost.get(275 - front.state.u_cost, ()):
            if front.state.row_index + back.state.row_index != 21:
                continue
            pairs += 1
            partition, cycles = merge_frontier_partition(front.state, back.state)
            result = (len(set(partition)), cycles, front, back, partition)
            if best is None or result[:2] < best[:2]:
                best = result
    return best, pairs


def search_multicut(
    caps: tuple[Cap, ...],
    traces: dict[str, list[FrontierState]],
    band_beams: tuple[int, ...],
    partial_beam: int,
    partial_policy: str,
    backward_width: int,
):
    forward, forward_transitions = build_forward_levels(
        traces, caps, band_beams, partial_beam, partial_policy
    )
    backward, backward_transitions = build_backward_levels(
        caps, 3, backward_width, partial_beam, partial_policy
    )
    overall = None
    for cut in (4, 5):
        back_bands = 7 - cut
        best, pairs = best_multicut_join(
            forward.get(cut, {}), backward.get(back_bands, {})
        )
        print(
            f"multicut={cut}/{back_bands} forward={len(forward.get(cut, {}))} "
            f"backward={len(backward.get(back_bands, {}))} pairs={pairs} "
            f"best={best[:2] if best else None}"
        )
        if best is not None and (overall is None or best[:2] < overall[:2]):
            overall = best
    return overall, forward_transitions + backward_transitions


def search_prefix(
    caps: tuple[Cap, ...],
    traces: dict[str, list[FrontierState]],
    band_beams: tuple[int, ...],
    partial_beam: int,
    partial_policy: str,
):
    if len(band_beams) != 6:
        raise ValueError("six complete-band beam widths are required")
    tiles = production_tiles(oriented=True)
    domains = [[tiles] * 7 for _ in range(6)]
    remaining = suffix_u_costs(domains)
    certificate_pairs = tuple(
        sorted(
            {certificate for cap in caps for certificate in cap.certificates},
            key=lambda item: (item.orientation, item.slab_start),
        )
    )
    start = initial_state(21)
    states = {grammar_key(start): PrefixNode(start, (), ())}
    transitions = 0
    partial_selector = make_partial_selector(partial_policy)

    for band_index, domain_row in enumerate(domains):
        candidates = []
        suffix_start = band_index * 7
        for node in states.values():
            outgoing, attempted = stream_band_domains(
                node.state,
                domain_row,
                max_u_cost=240,
                max_cycle_excess=1,
                remaining_u_costs=remaining[suffix_start : suffix_start + 8],
                target_u_costs=frozenset((240,)),
                partial_beam_width=partial_beam,
                partial_selector=partial_selector,
            )
            transitions += attempted
            parent_candidates = [
                PrefixNode(
                    state,
                    (*node.masks, *masks),
                    (*node.names, names),
                )
                for state, masks, names in outgoing
            ]
            if band_index == 5:
                for candidate in parent_candidates:
                    joined = find_join(candidate, caps)
                    if joined is not None and joined[0] == 1 and joined[1] <= 1:
                        return candidate, joined[3], transitions, joined
            local_score = (
                (lambda item: cap_score(item, caps))
                if band_index == 5
                else (
                    lambda item: trace_score(
                        item, band_index + 1, traces, certificate_pairs
                    )
                )
            )
            candidates.extend(
                select_diverse(
                    parent_candidates,
                    min(band_beams[band_index], len(parent_candidates)),
                    local_score,
                ).values()
            )

        score = (
            (lambda item: cap_score(item, caps))
            if band_index == 5
            else (
                lambda item: trace_score(
                    item, band_index + 1, traces, certificate_pairs
                )
            )
        )
        states = select_diverse(candidates, band_beams[band_index], score)
        if not states:
            break
        best = min(states.values(), key=score)
        join = find_join(best, caps)
        print(
            f"band={band_index + 1} states={len(states)} transitions={transitions} "
            f"best_score={score(best)[:7]} "
            f"best_join={(join[0], join[1]) if join else None}"
        )
    if not states:
        return None, None, transitions, None
    best = min(states.values(), key=lambda item: cap_score(item, caps))
    return best, None, transitions, find_join(best, caps)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--band-beams", default="50,100,200,400,800,1600", metavar="W1,...,W6"
    )
    parser.add_argument("--partial-beam", type=int, default=500)
    parser.add_argument(
        "--partial-policy",
        choices=("legacy", "bridge", "port", "obligation"),
        default="legacy",
    )
    parser.add_argument("--artifact-only", action="store_true")
    parser.add_argument("--multicut", action="store_true")
    parser.add_argument("--backward-width", type=int, default=500)
    args = parser.parse_args()
    try:
        band_beams = tuple(int(value) for value in args.band_beams.split(","))
    except ValueError as error:
        parser.error(f"invalid --band-beams: {error}")

    caps, traces = enumerate_target_caps()
    print("cap artifact: states=3784 targets=18 certificates=56")
    if args.artifact_only:
        return
    if args.multicut:
        best, transitions = search_multicut(
            caps,
            traces,
            band_beams,
            args.partial_beam,
            args.partial_policy,
            args.backward_width,
        )
        if best is None or best[0] != 1 or best[1] > 1:
            print(
                f"no multicut witness; transitions={transitions} "
                f"best={best[:2] if best else None}"
            )
            raise SystemExit(1)
        _, cycles, front, back, _ = best
        masks = [*front.masks, *reversed(back.masks)]
        rows = [render_mask(mask, 21) for mask in masks]
        info = run_check(21, rows, verbose=True)
        print(f"multicut witness transitions={transitions} cycles={cycles}")
        print("\n".join(rows))
        if not info["all_ok"]:
            raise SystemExit("multicut search produced an invalid witness")
        return
    prefix, cap, transitions, joined = search_prefix(
        caps, traces, band_beams, args.partial_beam, args.partial_policy
    )
    if prefix is None or cap is None:
        print(f"no guided witness; transitions={transitions} best_join={joined[:2] if joined else None}")
        raise SystemExit(1)

    masks = [*prefix.masks, *reversed(cap.backward_masks)]
    rows = [render_mask(mask, 21) for mask in masks]
    print(
        f"guided witness transitions={transitions} join_components={joined[0]} "
        f"join_cycles={joined[1]}"
    )
    info = run_check(21, rows, verbose=True)
    print("\n".join(rows))
    if q_formula(21) != 275 or not info["all_ok"]:
        raise SystemExit("guided cap search produced an invalid witness")


if __name__ == "__main__":
    main()
