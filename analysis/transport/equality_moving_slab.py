#!/usr/bin/env python3
"""Search moving decorated slabs with three noncontiguous HOLD rows."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

from analysis.transport.equality_corridor import build_equality_corridor
from analysis.transport.equality_slab_lanes import (
    _forgotten_only_components,
    enumerate_minimum_mask_paths,
    extract_cross_slab_signature,
    replay_masks,
)
from analysis.tiles.tile_grammar import compress_mask


SCHEMA = "grid-graphs.equality-moving-slab.v1"


def _source_prefix_states(paths: list[tuple[int, ...]]) -> tuple[list[set[tuple[int, ...]]], dict]:
    source_n = len(paths[0])
    if any(len(path) != source_n for path in paths):
        raise ValueError("source paths do not have a common width")
    prefixes = [set() for _ in range(source_n + 1)]
    states = {}
    for path in paths:
        trace = replay_masks(path)
        for depth in range(source_n + 1):
            prefix = path[:depth]
            prefixes[depth].add(prefix)
            states.setdefault(prefix, trace[depth])
    return prefixes, states


def _decoration(
    target_trace,
    target_depth: int,
    source_state,
    seam: int,
) -> tuple | None:
    slab_width = target_trace[0].n - source_state.n
    if (
        not 1 <= target_depth < target_trace[0].n
        or not 1 <= source_state.row_index < source_state.n
    ):
        return None
    target = target_trace[target_depth]
    removed_u = target.u_cost - source_state.u_cost
    if removed_u < 0:
        return None
    signature = extract_cross_slab_signature(
        target, seam, removed_u, slab_width=slab_width
    )
    if (
        signature.compressed_previous_u_mask != source_state.previous_u_mask
        or signature.projected_partition != source_state.partition
        or signature.normalized_u_cost != source_state.u_cost
    ):
        return None
    return (
        target_depth % 3,
        source_state.row_index % 3,
        seam,
        signature.slab_previous_u_mask,
        signature.attachment_partition,
        _forgotten_only_components(signature),
        signature.cycle_excess - source_state.cycle_excess,
    )


def _cap_mask_matches(target_state, source_state, seam: int) -> bool:
    slab_width = target_state.n - source_state.n
    return (
        compress_mask(target_state.previous_u_mask, seam, slab_width)
        == source_state.previous_u_mask
    )


def _target_alignment(
    target_masks: tuple[int, ...],
    source_prefixes: list[set[tuple[int, ...]]],
    source_states: dict,
) -> dict | None:
    target_trace = replay_masks(target_masks)
    target_n = len(target_masks)
    source_n = len(source_prefixes) - 1
    slab_width = target_n - source_n
    if slab_width <= 0:
        raise ValueError("target width must exceed source width")
    initial = ((), -1)
    layers = [{initial: 1}]
    word_layers = [{initial: Counter({"": 1})}]
    edges = []
    predecessors = {}

    for target_row, target_mask in enumerate(target_masks):
        children = defaultdict(int)
        child_words = defaultdict(Counter)
        row_edges = []
        target_state = target_trace[target_row + 1]
        for incoming, count in layers[-1].items():
            prefix, previous_seam = incoming
            source_depth = len(prefix)
            holds_used = target_row - source_depth
            seams = (
                range(source_n + 1)
                if previous_seam < 0
                else range(
                    max(0, previous_seam - 1),
                    min(source_n, previous_seam + 1) + 1,
                )
            )
            for seam in seams:
                compressed = compress_mask(target_mask, seam, slab_width)
                for operation in ("ADVANCE", "HOLD"):
                    if operation == "ADVANCE":
                        if source_depth == source_n:
                            continue
                        outgoing_prefix = (*prefix, compressed)
                        if outgoing_prefix not in source_prefixes[source_depth + 1]:
                            continue
                    else:
                        if (
                            holds_used == slab_width
                            or compressed != source_states[prefix].previous_u_mask
                        ):
                            continue
                        outgoing_prefix = prefix
                    source_state = source_states[outgoing_prefix]
                    outgoing_depth = len(outgoing_prefix)
                    if not _cap_mask_matches(target_state, source_state, seam):
                        continue
                    decoration = _decoration(
                        target_trace, target_row + 1, source_state, seam
                    )
                    if 1 <= outgoing_depth < source_n and decoration is None:
                        continue
                    outgoing = (outgoing_prefix, seam)
                    children[outgoing] += count
                    letter = "A" if operation == "ADVANCE" else "H"
                    for word, word_count in word_layers[-1][incoming].items():
                        child_words[outgoing][word + letter] += word_count
                    edge = (incoming, outgoing, operation, decoration)
                    row_edges.append(edge)
                    predecessors.setdefault((target_row + 1, outgoing), (incoming, operation))
        layers.append(dict(children))
        word_layers.append(dict(child_words))
        edges.append(row_edges)

    successful = {state for state in layers[target_n] if len(state[0]) == source_n}
    if not successful:
        return None
    good = [set() for _ in range(target_n + 1)]
    good[target_n] = successful
    successful_edges = [[] for _ in range(target_n)]
    for row in reversed(range(target_n)):
        for edge in edges[row]:
            if edge[1] in good[row + 1]:
                good[row].add(edge[0])
                successful_edges[row].append(edge)
    if initial not in good[0]:
        raise AssertionError("successful alignment lost its initial state")

    cycle_zero_successful = {
        state
        for state in successful
        if target_trace[-1].cycle_excess == source_states[state[0]].cycle_excess
    }
    strict_good = [set() for _ in range(target_n + 1)]
    strict_good[target_n] = cycle_zero_successful
    strict_edges = [[] for _ in range(target_n)]
    for row in reversed(range(target_n)):
        for edge in edges[row]:
            if edge[1] in strict_good[row + 1]:
                strict_good[row].add(edge[0])
                strict_edges[row].append(edge)

    alignment_count = sum(layers[target_n][state] for state in successful)
    operation_word_counts = Counter()
    terminal_cycle_counts = Counter()
    source_alignment_counts = Counter()
    source_cycle_alignment_counts = Counter()
    for state in successful:
        count = layers[target_n][state]
        operation_word_counts.update(word_layers[target_n][state])
        source_alignment_counts[state[0]] += count
        terminal_cycle_counts[
            target_trace[-1].cycle_excess - source_states[state[0]].cycle_excess
        ] += count
        if state in cycle_zero_successful:
            source_cycle_alignment_counts[state[0]] += count
    terminal = min(successful, key=repr)
    operations = []
    seams = []
    state = terminal
    for depth in reversed(range(1, target_n + 1)):
        incoming, operation = predecessors[(depth, state)]
        operations.append(operation)
        seams.append(state[1])
        state = incoming
    operations.reverse()
    seams.reverse()
    return {
        "alignment_count": alignment_count,
        "cycle_preserving_alignment_count": sum(
            layers[target_n][state] for state in cycle_zero_successful
        ),
        "source_alignment_counts": source_alignment_counts,
        "source_cycle_alignment_counts": source_cycle_alignment_counts,
        "operation_word_counts": operation_word_counts,
        "terminal_cycle_counts": terminal_cycle_counts,
        "successful_states": sum(len(layer) for layer in good),
        "edges": successful_edges,
        "cycle_preserving_edges": strict_edges,
        "sample": {
            "operations": operations,
            "seams": seams,
            "source_masks": list(terminal[0]),
        },
    }


def _decoration_id(decoration: tuple | None) -> str:
    return "CAP" if decoration is None else json.dumps(decoration, separators=(",", ":"))


def _graph_stats(edges: set[tuple[str, str]]) -> dict:
    adjacency = defaultdict(set)
    vertices = set()
    for incoming, outgoing in edges:
        adjacency[incoming].add(outgoing)
        vertices.update((incoming, outgoing))
    cycle_vertices = 0
    for start in vertices:
        stack = list(adjacency[start])
        seen = set()
        while stack:
            vertex = stack.pop()
            if vertex == start:
                cycle_vertices += 1
                break
            if vertex not in seen:
                seen.add(vertex)
                stack.extend(adjacency[vertex])
    return {
        "vertices": len(vertices),
        "edges": len(edges),
        "self_loops": sum(incoming == outgoing for incoming, outgoing in edges),
        "vertices_on_directed_cycles": cycle_vertices,
    }


def build_census() -> dict:
    source_paths = enumerate_minimum_mask_paths(build_equality_corridor(5))
    target_paths = enumerate_minimum_mask_paths(build_equality_corridor(8))
    source_prefixes, source_states = _source_prefix_states(source_paths)
    successful_targets = 0
    alignment_count = 0
    cycle_preserving_alignment_count = 0
    operation_counts = Counter()
    terminal_cycle_counts = Counter()
    seam_counts = Counter()
    interior_decorated_edges = set()
    strict_interior_decorated_edges = set()
    samples = []
    for target_id, target in enumerate(target_paths):
        result = _target_alignment(target, source_prefixes, source_states)
        if result is None:
            continue
        successful_targets += 1
        alignment_count += result["alignment_count"]
        cycle_preserving_alignment_count += result[
            "cycle_preserving_alignment_count"
        ]
        operation_counts.update(result["operation_word_counts"])
        terminal_cycle_counts.update(result["terminal_cycle_counts"])
        sample = result["sample"]
        seam_counts[",".join(map(str, sample["seams"]))] += 1
        if len(samples) < 50:
            samples.append({"target_path": target_id, **sample})
        for row, edges in enumerate(result["edges"]):
            for incoming, outgoing, _, outgoing_decoration in edges:
                incoming_decoration = None
                if row > 0:
                    source_state = source_states[incoming[0]]
                    incoming_decoration = _decoration(
                        replay_masks(target), row, source_state, incoming[1]
                    )
                if incoming_decoration is not None and outgoing_decoration is not None:
                    interior_decorated_edges.add(
                        (
                            _decoration_id(incoming_decoration),
                            _decoration_id(outgoing_decoration),
                        )
                    )
        for row, edges in enumerate(result["cycle_preserving_edges"]):
            for incoming, _, _, outgoing_decoration in edges:
                incoming_decoration = None
                if row > 0:
                    source_state = source_states[incoming[0]]
                    incoming_decoration = _decoration(
                        replay_masks(target), row, source_state, incoming[1]
                    )
                if incoming_decoration is not None and outgoing_decoration is not None:
                    strict_interior_decorated_edges.add(
                        (
                            _decoration_id(incoming_decoration),
                            _decoration_id(outgoing_decoration),
                        )
                    )
    return {
        "schema": SCHEMA,
        "scope": {
            "source_n": 5,
            "target_n": 8,
            "seam_step": 1,
            "operations": {"ADVANCE": 5, "HOLD": 3},
            "semantics": "optimal-path-moving-visible-interface-census",
        },
        "census": {
            "source_paths": len(source_paths),
            "target_paths": len(target_paths),
            "successful_target_paths": successful_targets,
            "alignment_paths": alignment_count,
            "terminal_cycle_preserving_alignments": cycle_preserving_alignment_count,
            "operation_words": dict(sorted(operation_counts.items())),
            "terminal_cycle_delta_histogram": {
                str(delta): count for delta, count in sorted(terminal_cycle_counts.items())
            },
            "sample_seam_words": dict(sorted(seam_counts.items())[:100]),
            "interior_decoration_transport_graph": _graph_stats(
                interior_decorated_edges
            ),
            "cycle_preserving_interior_decoration_graph": _graph_stats(
                strict_interior_decorated_edges
            ),
        },
        "samples": samples,
        "provenance": {
            "producer": "analysis/transport/equality_moving_slab.py",
            "command": [
                "python3",
                "-B",
                "analysis/transport/equality_moving_slab.py",
                "--output",
                "analysis/equality_moving_slab.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    artifact = build_census()
    rendered = json.dumps(artifact, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
