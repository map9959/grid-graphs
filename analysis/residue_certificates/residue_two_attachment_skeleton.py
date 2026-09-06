#!/usr/bin/env python3
"""Reduced attachment-skeleton certificates for residue-two controls.

The reduced metric counts boundary occurrence runs, not raw port multiplicity.
Its inequalities are unconditional word/annulus facts.  Boundedness across the
enumerated equality controls is evidence only.
"""

from __future__ import annotations

import argparse
import json
import os
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

from analysis.bounds.concentric_connectivity_profile import analyze_pattern
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from analysis.transport.equality_corridor import build_equality_corridor
from analysis.transport.equality_slab_lanes import enumerate_minimum_mask_paths
from analysis.bounds.proof_oriented_identities import check_pattern_identities
from analysis.residue_certificates.residue_two_n11_grammar_counterexample import ROWS as N11_SILENT_ROWS
from analysis.tiles.tile_grammar import advance_row, initial_state, render_mask, row_mask
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_attachment_skeleton.json"
SCHEMA = "grid-graphs.residue-two-attachment-skeleton.v1"


@dataclass(frozen=True, slots=True)
class AttachmentSkeleton:
    port_occurrences: int
    ported_components: int
    attachment_debt: int
    occurrence_runs: int
    branching_components: int
    branch_cost: int
    maximum_runs_per_component: int
    reduced_tokens: tuple[str, ...]
    alternating_component_pair: tuple[int, int] | None


def cyclic_runs(word: Iterable[int | str]) -> tuple[int | str, ...]:
    """Contract equal cyclic neighbors in a boundary word."""
    values = tuple(word)
    if not values:
        return ()
    runs = [values[0]]
    for value in values[1:]:
        if value != runs[-1]:
            runs.append(value)
    if len(runs) > 1 and runs[0] == runs[-1]:
        runs.pop()
    return tuple(runs)


def alternating_component_pair(word: Iterable[int]) -> tuple[int, int] | None:
    """Return a pair with cyclic A,B,A,B occurrences, if one exists."""
    runs = cyclic_runs(word)
    labels = sorted(set(runs))
    for index, left in enumerate(labels):
        for right in labels[index + 1 :]:
            projected = cyclic_runs(value for value in runs if value in (left, right))
            if len(projected) >= 4:
                return left, right
    return None


def attachment_skeleton(word: Iterable[int]) -> AttachmentSkeleton:
    """Compress a cyclic component-port word while retaining branch demand."""
    values = tuple(word)
    runs = cyclic_runs(values)
    run_counts = Counter(runs)
    branching = [label for label in runs if run_counts[label] > 1]
    branching_ids = {label: index for index, label in enumerate(dict.fromkeys(branching))}
    tokens = cyclic_runs(
        f"R{branching_ids[label]}" if label in branching_ids else "S"
        for label in runs
    )
    branch_cost = sum(count - 1 for count in run_counts.values())
    result = AttachmentSkeleton(
        port_occurrences=len(values),
        ported_components=len(run_counts),
        attachment_debt=max(len(run_counts) - 1, 0),
        occurrence_runs=len(runs),
        branching_components=len(branching_ids),
        branch_cost=branch_cost,
        maximum_runs_per_component=max(run_counts.values(), default=0),
        reduced_tokens=tuple(str(token) for token in tokens),
        alternating_component_pair=alternating_component_pair(values),
    )
    if result.occurrence_runs - result.ported_components != result.branch_cost:
        raise AssertionError("branch-cost identity failed")
    if result.branching_components > result.branch_cost:
        raise AssertionError("each branching component must pay branch cost")
    if result.branch_cost > result.port_occurrences - result.ported_components:
        raise AssertionError("branch cost exceeds occurrence surplus")
    return result


def nested_noncrossing_word(depth: int) -> tuple[int, ...]:
    """An unbounded topological family with nested, nonalternating blocks."""
    if type(depth) is not int or depth < 1:
        raise ValueError("depth must be a positive integer")
    return (*range(depth), *reversed(range(depth)))


def linear_frontier_metric(partition: tuple[int, ...]) -> dict:
    """Occurrence/debt metric retaining gaps between repeated live components."""
    if not partition:
        raise ValueError("frontier partition must contain OUT")
    out = partition[0]
    faces = partition[1:]
    positions: dict[int, list[int]] = {}
    for index, label in enumerate(faces):
        if label != out:
            positions.setdefault(label, []).append(index)
    runs = {
        label: sum(index == 0 or faces[index - 1] != label for index in slots)
        for label, slots in positions.items()
    }
    return {
        "attachment_debt": len(positions),
        "branching_components": sum(value > 1 for value in runs.values()),
        "branch_cost": sum(value - 1 for value in runs.values()),
        "silent_face_slots": sum(
            slots[-1] - slots[0] + 1 - len(slots) for slots in positions.values()
        ),
        "maximum_occurrence_hull_span": max(
            (slots[-1] - slots[0] + 1 for slots in positions.values()), default=0
        ),
    }


def _prefix_skeletons(rows: tuple[str, ...]) -> tuple[dict, list[dict]]:
    identities = check_pattern_identities(list(rows))
    curvature = 3 * identities.u_count - 2 * identities.graphic_rank - len(rows)
    profile = analyze_pattern(rows)
    records = []
    for prefix in profile["centered_prefixes"]:
        skeleton = attachment_skeleton(prefix["canonical_cyclic_port_word"])
        if skeleton.alternating_component_pair is not None:
            raise AssertionError("planar dual components alternate on a centered boundary")
        if skeleton.port_occurrences != prefix["perimeter_ports"]:
            raise AssertionError("port word does not contain every perimeter port")
        if skeleton.ported_components != prefix["ported_components"]:
            raise AssertionError("port word component count changed")
        if skeleton.branch_cost > prefix["attachment_surplus"]:
            raise AssertionError("annulus attachment-surplus bound failed")
        records.append(
            {
                "side": prefix["side"],
                **asdict(skeleton),
                "attachment_surplus": prefix["attachment_surplus"],
            }
        )
    summary = {
        "n": len(rows),
        "u_count": identities.u_count,
        "charged_curvature": curvature,
        "maximum_branch_cost": max((item["branch_cost"] for item in records), default=0),
        "maximum_branching_components": max(
            (item["branching_components"] for item in records), default=0
        ),
        "maximum_reduced_tokens": max(
            (len(item["reduced_tokens"]) for item in records), default=0
        ),
        "maximum_runs_per_component": max(
            (item["maximum_runs_per_component"] for item in records), default=0
        ),
    }
    return summary, records


def _complete_equality_case(n: int) -> dict:
    corridor = build_equality_corridor(n)
    paths = enumerate_minimum_mask_paths(corridor)
    branch_histogram = Counter()
    maximum = 0
    for masks in paths:
        rows = tuple(render_mask(mask, n) for mask in masks)
        summary, _ = _prefix_skeletons(rows)
        maximum = max(maximum, summary["maximum_branch_cost"])
        branch_histogram[summary["maximum_branch_cost"]] += 1

    local_candidates = {
        "row_weight_ge_debt_delta": [10**9, None],
        "row_weight_ge_branch_delta": [10**9, None],
        "row_weight_ge_debt_plus_branch_delta": [10**9, None],
    }
    for edges in corridor.corridor_edges:
        for edge in edges:
            incoming = linear_frontier_metric(edge.incoming[2])
            outgoing = linear_frontier_metric(edge.outgoing[2])
            deltas = {
                "row_weight_ge_debt_delta": outgoing["attachment_debt"]
                - incoming["attachment_debt"],
                "row_weight_ge_branch_delta": outgoing["branch_cost"]
                - incoming["branch_cost"],
                "row_weight_ge_debt_plus_branch_delta": (
                    outgoing["attachment_debt"]
                    + outgoing["branch_cost"]
                    - incoming["attachment_debt"]
                    - incoming["branch_cost"]
                ),
            }
            for name, delta in deltas.items():
                slack = edge.weight - delta
                if slack < local_candidates[name][0]:
                    local_candidates[name] = [
                        slack,
                        {
                            "row": edge.row,
                            "row_weight": edge.weight,
                            "incoming": incoming,
                            "outgoing": outgoing,
                        },
                    ]
    return {
        "n": n,
        "minimum_charged_curvature": corridor.minimum_weight,
        "patterns": len(paths),
        "maximum_branch_cost": maximum,
        "maximum_branch_cost_histogram": {
            str(value): count for value, count in sorted(branch_histogram.items())
        },
        "local_candidate_inequalities": {
            name: {"minimum_slack": value[0], "counterexample": value[1]}
            for name, value in local_candidates.items()
        },
    }


def _n11_linear_history() -> list[dict]:
    state = initial_state(11)
    history = [{"completed_rows": 0, **linear_frontier_metric(state.partition)}]
    for row_index, row in enumerate(N11_SILENT_ROWS, 1):
        state = advance_row(state, row_mask(row))
        if state is None:
            raise AssertionError("n=11 silent witness became invalid")
        history.append(
            {"completed_rows": row_index, **linear_frontier_metric(state.partition)}
        )
    if history[8]["branch_cost"] != 1 or history[8]["silent_face_slots"] == 0:
        raise AssertionError("n=11 silent gap is not retained by the occurrence metric")
    return history


def build_artifact(*, regenerate_complete: bool = False) -> dict:
    cached = DEFAULT_OUTPUT.exists() and not regenerate_complete
    if cached:
        complete = json.loads(DEFAULT_OUTPUT.read_text())["complete_small_equality"]
    else:
        complete = {str(n): _complete_equality_case(n) for n in (5, 8)}

    equality_rows = {
        "n5-fixed": tuple(residue_two_explicit_pattern(5)),
        "n8-fixed": tuple(residue_two_explicit_pattern(8)),
        "n11-fixed": tuple(residue_two_explicit_pattern(11)),
        "n11-silent": tuple(N11_SILENT_ROWS),
        "n14-fixed": tuple(residue_two_explicit_pattern(14)),
    }
    equality = {name: _prefix_skeletons(rows)[0] for name, rows in equality_rows.items()}
    affine = {
        f"A{n}": _prefix_skeletons(tuple(residue_two_affine_pattern(n)))[0]
        for n in range(17, 42, 3)
    }
    a23_profile = analyze_pattern(tuple(residue_two_affine_pattern(23)))
    old_a23 = {
        "maximum_repeated_components": max(
            item["repeated_port_components"] for item in a23_profile["centered_prefixes"]
        ),
        "maximum_cyclic_runs_per_component": max(
            item["maximum_cyclic_port_runs"] for item in a23_profile["centered_prefixes"]
        ),
        "maximum_compressed_runs": max(
            item["compressed_port_run_count"] for item in a23_profile["centered_prefixes"]
        ),
    }
    if not (
        old_a23["maximum_repeated_components"] > 4
        and old_a23["maximum_compressed_runs"] > 9
    ):
        raise AssertionError("A23 no longer falsifies the old observed bounds")

    nested = {}
    for depth in (4, 6, 12):
        skeleton = attachment_skeleton(nested_noncrossing_word(depth))
        if skeleton.alternating_component_pair is not None:
            raise AssertionError("nested topological control unexpectedly crosses")
        nested[str(depth)] = {
            **asdict(skeleton),
            "reduced_tokens": list(skeleton.reduced_tokens),
        }
    return {
        "schema": SCHEMA,
        "scope": {
            "unconditional_results": [
                "branch_cost = occurrence_runs - ported_components",
                "branching_components <= branch_cost",
                "on an unsealed annulus, branch_cost <= perimeter_ports - ported_components = attachment_surplus",
                "disjoint planar components have no cyclic A,B,A,B boundary alternation",
            ],
            "complete_equality_widths": [5, 8],
            "fixed_equality_controls": [5, 8, 11, 14],
            "affine_controls": list(range(17, 42, 3)),
            "arbitrary_width_constant_bound_claimed": False,
        },
        "definitions": {
            "occurrence_run": "a maximal cyclic interval of perimeter ports belonging to one internal component",
            "branch_cost": "sum over ported components of occurrence_runs(component)-1",
            "attachment_debt": "ported_components-1, floored at zero",
            "reduced_tokens": "cyclic run word with one canonical R token per branching component and all one-run components mapped to S",
            "silent_gap_behavior": "separated occurrences remain separate runs even when intervening packets contain no port of the component",
        },
        "theorems": {
            "occurrence_bound": (
                "Every component uses at least one port, so contracting adjacent equal "
                "ports gives occurrence_runs<=perimeter_ports and hence "
                "branch_cost<=perimeter_ports-ported_components."
            ),
            "annulus_link": (
                "For an unsealed centered prefix, perimeter_ports-ported_components "
                "is q_s-d_s, the attachment term in "
                "M_s-(s-1)^2=(q_s-d_s)+beta_s."
            ),
            "noncrossing": (
                "Two disjoint connected subgraphs in a disk cannot have alternating "
                "A,B,A,B boundary occurrences; otherwise their connecting arcs cross."
            ),
        },
        "old_4_3_9_falsification": {
            "status": "not-topological-and-false-on-affine-A23",
            "A23_observed": old_a23,
            "old_bounds": {
                "maximum_repeated_components": 4,
                "maximum_cyclic_runs_per_component": 3,
                "maximum_compressed_runs": 9,
            },
            "nested_noncrossing_family": nested,
        },
        "complete_small_equality": complete,
        "fixed_equality_controls": equality,
        "affine_surplus_controls": affine,
        "n11_silent_frontier_history": _n11_linear_history(),
        "observed_conjectures": {
            "equality_branch_bound": (
                "Every enumerated curvature-five pattern at n=5,8 and both fixed "
                "n=11 controls and n=14 has maximum centered branch cost at most 1."
            ),
            "affine_growth": (
                "For sampled affine A_n, maximum branch cost grows by one per width-three "
                "extension and equals (charged_curvature-2)/3."
            ),
            "theorem_status": False,
        },
        "local_invariant_result": {
            "proved": (
                "The branch-cost/attachment-surplus inequality is local to every "
                "centered annulus and survives silent occurrence gaps."
            ),
            "falsified": (
                "None of row_weight>=Delta(debt), row_weight>=Delta(branch_cost), "
                "or row_weight>=Delta(debt+branch_cost) holds on all complete n=5,8 "
                "equality-corridor transitions; exact counterexamples are recorded."
            ),
            "next_candidate": (
                "A proof potential must include cap phase or remaining merge capacity; "
                "branch cost alone is not a row-local curvature potential."
            ),
        },
        "limitations": [
            "The constant branch bound one is a finite census and fixed-witness observation, not a theorem.",
            "The affine growth formula is symbolically unproved and sampled only at A17 through A41.",
            "Noncrossing and the attachment-surplus bound do not by themselves imply curvature five.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_attachment_skeleton.py",
            "complete_regeneration_command": [
                "GRID_GRAPHS_REGENERATE=1",
                "python3",
                "-B",
                "analysis/residue_certificates/residue_two_attachment_skeleton.py",
                "--output",
                "analysis/residue_two_attachment_skeleton.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--regenerate-complete", action="store_true")
    args = parser.parse_args()
    regenerate = args.regenerate_complete or bool(os.environ.get("GRID_GRAPHS_REGENERATE"))
    rendered = json.dumps(build_artifact(regenerate_complete=regenerate), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"attachment-skeleton certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
