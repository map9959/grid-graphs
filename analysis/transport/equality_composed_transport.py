#!/usr/bin/env python3
"""Compose exact moving-slab relations through an intermediate equality cap."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

from analysis.patterns.diagonal_patterns import residue_two_explicit_pattern
from analysis.tiles.tile_grammar import row_mask
from analysis.transport.census_moving_seam_alignment import d4_orientations
from analysis.transport.equality_corridor import build_equality_corridor
from analysis.transport.equality_moving_slab import (
    _source_prefix_states,
    _target_alignment,
)
from analysis.transport.equality_slab_lanes import enumerate_minimum_mask_paths

SCHEMA = "grid-graphs.equality-composed-transport.v1"


def _relation(source_n: int, target_n: int) -> dict:
    source_paths = enumerate_minimum_mask_paths(build_equality_corridor(source_n))
    target_paths = enumerate_minimum_mask_paths(build_equality_corridor(target_n))
    source_prefixes, source_states = _source_prefix_states(source_paths)
    source_ids = {path: path_id for path_id, path in enumerate(source_paths)}
    pairs = Counter()
    cycle_pairs = Counter()
    operation_words = Counter()
    terminal_cycle_deltas = Counter()
    successful_targets = 0

    for target_id, target in enumerate(target_paths):
        result = _target_alignment(target, source_prefixes, source_states)
        if result is None:
            continue
        successful_targets += 1
        operation_words.update(result["operation_word_counts"])
        terminal_cycle_deltas.update(result["terminal_cycle_counts"])
        for source, count in result["source_alignment_counts"].items():
            pairs[(source_ids[source], target_id)] += count
        for source, count in result["source_cycle_alignment_counts"].items():
            cycle_pairs[(source_ids[source], target_id)] += count

    return {
        "source_n": source_n,
        "target_n": target_n,
        "source_paths": source_paths,
        "target_paths": target_paths,
        "pairs": pairs,
        "cycle_pairs": cycle_pairs,
        "successful_targets": successful_targets,
        "operation_words": operation_words,
        "terminal_cycle_deltas": terminal_cycle_deltas,
    }


def _relation_summary(relation: dict) -> dict:
    return {
        "source_n": relation["source_n"],
        "target_n": relation["target_n"],
        "source_paths": len(relation["source_paths"]),
        "target_paths": len(relation["target_paths"]),
        "successful_source_target_pairs": len(relation["pairs"]),
        "successful_target_paths": relation["successful_targets"],
        "alignment_paths": sum(relation["pairs"].values()),
        "cycle_preserving_source_target_pairs": len(relation["cycle_pairs"]),
        "cycle_preserving_alignment_paths": sum(relation["cycle_pairs"].values()),
        "operation_words": dict(sorted(relation["operation_words"].items())),
        "terminal_cycle_delta_histogram": {
            str(delta): count
            for delta, count in sorted(relation["terminal_cycle_deltas"].items())
        },
    }


def _compose(left: dict, right: dict) -> dict:
    if left["target_paths"] != right["source_paths"]:
        raise AssertionError("relations do not share the literal intermediate paths")

    left_by_middle = defaultdict(dict)
    right_by_middle = defaultdict(dict)
    strict_left_by_middle = defaultdict(dict)
    strict_right_by_middle = defaultdict(dict)
    for (source, middle), count in left["pairs"].items():
        left_by_middle[middle][source] = count
    for (middle, target), count in right["pairs"].items():
        right_by_middle[middle][target] = count
    for (source, middle), count in left["cycle_pairs"].items():
        strict_left_by_middle[middle][source] = count
    for (middle, target), count in right["cycle_pairs"].items():
        strict_right_by_middle[middle][target] = count

    triples = []
    endpoint_pairs = set()
    alignment_chains = 0
    for middle in sorted(left_by_middle.keys() & right_by_middle.keys()):
        for source, left_count in left_by_middle[middle].items():
            for target, right_count in right_by_middle[middle].items():
                endpoint_pairs.add((source, target))
                chain_count = left_count * right_count
                alignment_chains += chain_count
                if len(triples) < 50:
                    triples.append(
                        {
                            "source_path": source,
                            "intermediate_path": middle,
                            "target_path": target,
                            "alignment_chains": chain_count,
                        }
                    )

    strict_triples = 0
    strict_endpoint_pairs = set()
    strict_alignment_chains = 0
    for middle in strict_left_by_middle.keys() & strict_right_by_middle.keys():
        for source, left_count in strict_left_by_middle[middle].items():
            for target, right_count in strict_right_by_middle[middle].items():
                strict_triples += 1
                strict_endpoint_pairs.add((source, target))
                strict_alignment_chains += left_count * right_count

    return {
        "joined_intermediate_paths": len(left_by_middle.keys() & right_by_middle.keys()),
        "source_intermediate_target_triples": sum(
            len(left_by_middle[middle]) * len(right_by_middle[middle])
            for middle in left_by_middle.keys() & right_by_middle.keys()
        ),
        "source_target_pairs": len(endpoint_pairs),
        "alignment_chains": alignment_chains,
        "cycle_preserving_joined_intermediate_paths": len(
            strict_left_by_middle.keys() & strict_right_by_middle.keys()
        ),
        "cycle_preserving_triples": strict_triples,
        "cycle_preserving_source_target_pairs": len(strict_endpoint_pairs),
        "cycle_preserving_alignment_chains": strict_alignment_chains,
        "endpoint_pairs": endpoint_pairs,
        "cycle_endpoint_pairs": strict_endpoint_pairs,
        "samples": triples,
    }


def _fixed_n11_control(source_paths: list[tuple[int, ...]], reachable_sources: set[int]) -> dict:
    source_prefixes, source_states = _source_prefix_states(source_paths)
    source_ids = {path: path_id for path_id, path in enumerate(source_paths)}
    orientation_results = []
    successful_pairs = set()
    reachable_pairs = set()
    alignment_paths = 0
    for orientation in d4_orientations(residue_two_explicit_pattern(11)):
        target = tuple(map(row_mask, orientation.rows))
        result = _target_alignment(target, source_prefixes, source_states)
        pair_count = 0
        reachable_pair_count = 0
        if result is not None:
            alignment_paths += result["alignment_count"]
            for source, count in result["source_alignment_counts"].items():
                source_id = source_ids[source]
                successful_pairs.add((source_id, orientation.name))
                pair_count += count
                if source_id in reachable_sources:
                    reachable_pairs.add((source_id, orientation.name))
                    reachable_pair_count += count
        orientation_results.append(
            {
                "orientation": orientation.name,
                "alignment_paths": pair_count,
                "cap_reachable_alignment_paths": reachable_pair_count,
            }
        )
    return {
        "source_paths": len(source_paths),
        "cap_reachable_source_paths": len(reachable_sources),
        "target": "cached-exact-n11-all-distinct-d4-orientations",
        "successful_source_orientation_pairs": len(successful_pairs),
        "cap_reachable_source_orientation_pairs": len(reachable_pairs),
        "alignment_paths": alignment_paths,
        "orientations": orientation_results,
    }


def build_census() -> dict:
    relation_2_5 = _relation(2, 5)
    relation_5_8 = _relation(5, 8)
    direct_2_8 = _relation(2, 8)
    composed = _compose(relation_2_5, relation_5_8)
    direct_pairs = set(direct_2_8["pairs"])
    direct_cycle_pairs = set(direct_2_8["cycle_pairs"])
    endpoint_overlap = composed["endpoint_pairs"] & direct_pairs
    cycle_endpoint_overlap = (
        composed["cycle_endpoint_pairs"] & direct_cycle_pairs
    )
    reachable_n8_sources = {target for _, target in relation_5_8["pairs"]}
    fixed_n11_control = _fixed_n11_control(
        relation_5_8["target_paths"], reachable_n8_sources
    )

    return {
        "schema": SCHEMA,
        "scope": {
            "corridor_chain": [2, 5, 8],
            "seam_step": 1,
            "composed_slab_widths": [3, 3],
            "direct_slab_width": 6,
            "intermediate_join": "literal-full-row-mask-path-equality",
            "semantics": "complete-minimum-path-cap-reset-and-direct-multiband-census",
        },
        "relations": {
            "2_to_5": _relation_summary(relation_2_5),
            "5_to_8": _relation_summary(relation_5_8),
            "direct_2_to_8": _relation_summary(direct_2_8),
        },
        "cap_mediated_composition": {
            key: value
            for key, value in composed.items()
            if key not in {"endpoint_pairs", "cycle_endpoint_pairs", "samples"}
        },
        "direct_multiband_comparison": {
            "composed_source_target_pairs": len(composed["endpoint_pairs"]),
            "direct_width_six_source_target_pairs": len(direct_pairs),
            "common_source_target_pairs": len(endpoint_overlap),
            "cycle_preserving_composed_source_target_pairs": len(
                composed["cycle_endpoint_pairs"]
            ),
            "cycle_preserving_direct_source_target_pairs": len(direct_cycle_pairs),
            "cycle_preserving_common_source_target_pairs": len(
                cycle_endpoint_overlap
            ),
        },
        "fixed_n11_continuation_control": fixed_n11_control,
        "composition_samples": composed["samples"],
        "limitations": [
            "The n=2 source has only one interior frontier depth.",
            "Composition resets through a complete n=5 square; it is not an interior self-loop.",
            "The direct width-six language requires one contiguous six-column moving slab.",
            "No claim is made about equality states first appearing above width 8.",
            "The n=11 continuation checks the cached exact witness and its D4 orbit, not all n=11 optima.",
            "Retained-cell rewrites are forbidden in every relation.",
        ],
        "provenance": {
            "producer": "analysis/transport/equality_composed_transport.py",
            "command": [
                "python3",
                "-B",
                "-m",
                'analysis.transport.equality_composed_transport',
                "--output",
                "analysis/equality_composed_transport.json",
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
