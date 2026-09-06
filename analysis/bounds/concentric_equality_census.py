#!/usr/bin/env python3
"""Census concentric port signatures over complete small equality corridors."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from analysis.bounds.concentric_connectivity_profile import analyze_pattern
from analysis.transport.equality_corridor import build_equality_corridor
from analysis.transport.equality_slab_lanes import enumerate_minimum_mask_paths
from analysis.tiles.tile_grammar import render_mask
from analysis._paths import analysis_path


SCHEMA = "grid-graphs.concentric-equality-census.v1"
DEFAULT_OUTPUT = analysis_path("concentric_equality_census.json")
BOUNDS = {
    "repeated_port_components": 4,
    "maximum_cyclic_port_runs": 3,
    "compressed_port_run_count": 9,
}


def census_case(n: int) -> dict:
    corridor = build_equality_corridor(n)
    paths = enumerate_minimum_mask_paths(corridor)
    by_side: dict[int, Counter[tuple[int, int, int]]] = {}
    maxima = {field: 0 for field in BOUNDS}
    violating_patterns = 0
    first_violation = None

    for masks in paths:
        rows = tuple(render_mask(mask, n) for mask in masks)
        profile = analyze_pattern(rows)
        pattern_violates = False
        for prefix in profile["centered_prefixes"]:
            side = prefix["side"]
            triple = (
                prefix["repeated_port_components"],
                prefix["maximum_cyclic_port_runs"],
                prefix["compressed_port_run_count"],
            )
            by_side.setdefault(side, Counter())[triple] += 1
            for field, bound in BOUNDS.items():
                maxima[field] = max(maxima[field], prefix[field])
                if prefix[field] > bound:
                    pattern_violates = True
                    if first_violation is None:
                        first_violation = {
                            "field": field,
                            "bound": bound,
                            "observed": prefix[field],
                            "side": side,
                            "rows": list(rows),
                            "prefix": prefix,
                        }
        violating_patterns += pattern_violates

    return {
        "n": n,
        "minimum_u": corridor.minimum_u,
        "minimum_path_count": corridor.minimum_path_count,
        "distinct_patterns": len(paths),
        "maxima": maxima,
        "violating_patterns": violating_patterns,
        "first_violation": first_violation,
        "profiles_by_side": {
            str(side): [
                {
                    "repeated_port_components": triple[0],
                    "maximum_cyclic_port_runs": triple[1],
                    "compressed_port_run_count": triple[2],
                    "patterns": count,
                }
                for triple, count in sorted(histogram.items())
            ]
            for side, histogram in sorted(by_side.items())
        },
    }


def build_artifact() -> dict:
    cases = {f"n{n}-complete-equality": census_case(n) for n in (5, 8)}
    return {
        "schema": SCHEMA,
        "declared_bounds": BOUNDS,
        "scope": "all distinct globally minimum connected frontier paths at n=5,8",
        "cases": cases,
        "conclusion": (
            "The declared port-signature bounds are tested over the complete n=5,8 "
            "equality classes. This is a finite-width census, not arbitrary-width coverage."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    artifact = build_artifact()
    args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    for name, case in artifact["cases"].items():
        print(
            f"{name}: patterns={case['distinct_patterns']} maxima={case['maxima']} "
            f"violations={case['violating_patterns']}"
        )


if __name__ == "__main__":
    main()
