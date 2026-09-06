#!/usr/bin/env python3
"""Search an exact affine formula over coupled interval extrema."""

from __future__ import annotations

import json
from fractions import Fraction


from analysis.bounds.coupled_interval_potential import enumerate_source, interval_feature
from analysis.bounds.forced_forest_additive_potential import (
    exact_farkas_from_seed,
    projected_candidate,
    projected_farkas_seed,
    verify_formula,
)
from analysis._paths import analysis_path


NUMERIC_NAMES = (
    "constant",
    "phase_is_0",
    "phase_is_1",
    "top_mode",
    "terminal_mode",
    "saturated_depth",
    "width",
    "forced_count",
    "forced_runs",
    "left_forced",
    "right_forced",
    "h_components",
    "f_components",
    "retired_h",
    "retired_f",
    "forced_boundary_deficiency",
    "max_interval_00",
    "max_interval_01",
    "max_interval_10",
    "max_interval_11",
)


def _design(feature: tuple) -> list[Fraction]:
    if feature in (("initial",), ("zero",)):
        return [Fraction(0)] * len(NUMERIC_NAMES)
    phase, boundary, reserve = feature[:3]
    maxima = dict(feature[13])
    numeric = (
        1,
        int(phase == 0),
        int(phase == 1),
        int(boundary == "top"),
        int(boundary == "terminal"),
        0 if reserve == "terminal" else reserve,
        *feature[3:13],
        *(maxima.get(key, 0) for key in ((0, 0), (0, 1), (1, 0), (1, 1))),
    )
    return [Fraction(value) for value in numeric]


def constraints(widths: list[int]):
    sources = [enumerate_source(width) for width in widths]
    features = []
    for source in sources:
        for row, layer in enumerate(source.layers):
            features.extend(
                interval_feature(source.width, row, state, "extrema")
                for state in layer
                if state is not None
            )
    strongest = {}

    def retain(row, rhs):
        integer = tuple(int(value) for value in row)
        previous = strongest.get(integer)
        if previous is None or rhs < previous:
            strongest[integer] = rhs

    for source in sources:
        for state in source.layers[-1]:
            if state is None:
                continue
            design = _design(interval_feature(source.width, source.width, state, "extrema"))
            retain([-value for value in design], -4)
        for row_edges in source.edges:
            for edge in row_edges:
                incoming = _design(
                    interval_feature(edge.width, edge.row, edge.incoming, "extrema")
                )
                outgoing = _design(
                    interval_feature(edge.width, edge.row + 1, edge.outgoing, "extrema")
                )
                retain(
                    [right - left for left, right in zip(incoming, outgoing)], edge.weight
                )
    return NUMERIC_NAMES, [(row, rhs) for row, rhs in sorted(strongest.items())]


def build(discovery_widths: list[int], held_out_widths: list[int]) -> dict:
    names, discovery = constraints(discovery_widths)
    held_names, held_out = constraints(held_out_widths)
    if held_names != names:
        raise AssertionError("discovery and held-out bases differ")
    proposal = projected_candidate(discovery, 5000)
    candidates = []
    for denominator in (10, 100, 1000, 10000, 1000000):
        rational = [Fraction(value).limit_denominator(denominator) for value in proposal]
        replay = verify_formula(rational, discovery)
        held_replay = verify_formula(rational, held_out)
        candidates.append({
            "denominator_limit": denominator,
            "replay": replay,
            "held_out_replay": held_replay,
            "coefficients": {
                name: [value.numerator, value.denominator]
                for name, value in zip(names, rational)
                if value
            },
        })
        if replay["feasible"] and held_replay["feasible"]:
            break
    _values, dual_seed = projected_farkas_seed(discovery, 1000)
    farkas = exact_farkas_from_seed(discovery, dual_seed)
    return {
        "scope": {
            "discovery_widths": discovery_widths,
            "held_out_widths": held_out_widths,
            "terminal_target": 4,
        },
        "basis": list(names),
        "discovery_constraints": len(discovery),
        "held_out_constraints": len(held_out),
        "candidates": candidates,
        "exact_infeasibility_certificate": farkas,
    }


if __name__ == "__main__":
    output = analysis_path("coupled_interval_formula.json")
    output.write_text(json.dumps(build(list(range(3, 7)), [7, 8]), indent=2, sort_keys=True) + "\n")
