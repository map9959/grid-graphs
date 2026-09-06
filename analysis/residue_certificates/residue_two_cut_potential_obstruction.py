#!/usr/bin/env python3
"""Exact obstruction to scalar potentials on bounded packet-cut states."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from analysis.residue_certificates.residue_two_stable_counter_certificate import (
    horizontal_edges,
    stable_rule_certificates,
    vertical_edges,
)
from analysis.residue_certificates.residue_two_stable_topology_certificate import stable_topology_certificates
from analysis._paths import analysis_path


SCHEMA = "grid-graphs.residue-two-cut-potential-obstruction.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_cut_potential_obstruction.json")


def _row_weight(rule) -> tuple[int, int]:
    horizontal = horizontal_edges(rule.action)
    vertical = vertical_edges(rule.source, rule.action)
    cycles = rule.deltas.cycles
    return (
        3 * rule.deltas.u.packet_coefficient
        - 2 * (
            horizontal.packet_coefficient
            + vertical.packet_coefficient
            - cycles.packet_coefficient
        ),
        3 * rule.deltas.u.constant
        - 2 * (horizontal.constant + vertical.constant - cycles.constant)
        - 1,
    )


def build_artifact() -> dict:
    counters = stable_rule_certificates()
    topology = stable_topology_certificates()
    if len(counters) != len(topology):
        raise AssertionError("stable counter and topology rule counts differ")
    negative_loops = []
    for index, (rule, certificate) in enumerate(zip(counters, topology)):
        if certificate.prefix_state != certificate.loop_state:
            raise AssertionError("stable dominant packet is not a cut-state self-loop")
        slope, constant = _row_weight(rule)
        if slope < 0:
            negative_loops.append({
                "rule": index,
                "row_weight": f"{slope}*L+{constant}",
                "dominant_packet_increment": slope,
                "cut_state_self_loop": True,
            })
    if [(item["rule"], item["dominant_packet_increment"]) for item in negative_loops] != [
        (0, -1), (5, -1)
    ]:
        raise AssertionError("negative stable packet loops changed")
    return {
        "schema": SCHEMA,
        "scope": {
            "stable_rules": len(counters),
            "packet_lengths": "all integers L>=7",
            "obstruction_class": "scalar potential depending only on bounded packet-cut state",
            "weighted_word_potential_ruled_out": False,
        },
        "negative_self_loops": negative_loops,
        "proof": {
            "inequality": "packet_weight + psi(out)-psi(in) >= 0",
            "self_loop_specialization": "-1 + psi(q)-psi(q) >= 0",
            "contradiction": "-1>=0",
            "conclusion": (
                "No scalar potential on this or any finite refinement of the repeated "
                "packet state can certify every packet separately."
            ),
            "required_extension": (
                "A frontier-word potential must emit structural weight on atom-parser "
                "transitions and prove row inequalities after horizontal telescoping."
            ),
        },
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_cut_potential_obstruction.py",
            "command": [
                "python3", "-B", "analysis/residue_certificates/residue_two_cut_potential_obstruction.py",
                "--output", "analysis/residue_two_cut_potential_obstruction.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"cut-potential obstruction matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
