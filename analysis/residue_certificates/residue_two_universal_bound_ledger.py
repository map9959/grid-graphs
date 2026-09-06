#!/usr/bin/env python3
"""Auditable proof ledger for the residue-two universal upper-bound workstream.

The ledger proves the algebra reducing the old baseline to charged curvature
five, imports only explicitly scoped finite certificates, and verifies the n=17
terminal attachment-debt obstruction.  It does not turn finite-width evidence
into arbitrary-width coverage.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from analysis.patterns.diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from analysis.bounds.proof_oriented_identities import check_pattern_identities
from analysis.residue_certificates.residue_two_attachment_history import build_analysis
from analysis.residue_certificates.residue_two_local_motif_grammar import (
    all_rooted_triple_symbols,
    hull_carrier_local_acceptance,
)
from analysis.residue_certificates.residue_two_n11_grammar_counterexample import (
    FORBIDDEN_MOTIFS,
    ROWS as N11_SILENT_ROWS,
    build_artifact as build_n11_counterexample,
)
from analysis.tiles.tile_grammar import advance_row, initial_state, row_mask
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_universal_bound_ledger.json"
STRUCTURAL_GAP = HERE / "residue_two_structural_defect_gap.json"
ATTACHMENT_SKELETON = HERE / "residue_two_attachment_skeleton.json"
CAP_MERGE_POTENTIAL = HERE / "residue_two_cap_merge_potential.json"
PERSISTENT_DEBT = HERE / "residue_two_persistent_debt_certificate.json"
N17_RESULT = HERE / "frontier_n17_unmirrored_result.json"
SCHEMA = "grid-graphs.residue-two-universal-bound-ledger.v1"


def old_baseline(n: int) -> int:
    """Return 6k^2+5k+3 for n=3k+2."""
    if type(n) is not int or n < 5 or n % 3 != 2:
        raise ValueError("baseline requires n=3k+2 with k>=1")
    k = (n - 2) // 3
    return 6 * k * k + 5 * k + 3


def curvature_lower_bound(n: int, curvature: int) -> int:
    """Round the exact inequality 3|U| >= 2(n-1)^2+n+curvature."""
    if type(n) is not int or type(curvature) is not int:
        raise TypeError("n and curvature must be integers")
    numerator = 2 * (n - 1) ** 2 + n + curvature
    return (numerator + 2) // 3


def verify_baseline_algebra(n: int) -> dict:
    """Verify that curvature five is exactly the old residue-two baseline."""
    target = old_baseline(n)
    numerator = 2 * (n - 1) ** 2 + n + 5
    if numerator != 3 * target:
        raise AssertionError("residue-two baseline identity failed")
    if curvature_lower_bound(n, 5) != target:
        raise AssertionError("curvature lower bound did not recover the baseline")
    return {
        "n": n,
        "k": (n - 2) // 3,
        "identity": "3*q_old = 2*(n-1)^2+n+5",
        "q_old": target,
    }


def _pattern_record(n: int, rows: list[str] | tuple[str, ...], selection: str) -> dict:
    identities = check_pattern_identities(list(rows))
    curvature = 3 * identities.u_count - 2 * identities.graphic_rank - n
    identity_curvature = 2 * identities.run_sum + 2 * identities.cycle_rank - identities.u_count - n
    if identities.components != 1 or curvature != identity_curvature:
        raise AssertionError("pattern is disconnected or violates the run/rank identity")
    return {
        "n": n,
        "selection": selection,
        "u_count": identities.u_count,
        "rank": identities.graphic_rank,
        "run_sum": identities.run_sum,
        "cycle_rank": identities.cycle_rank,
        "charged_curvature": curvature,
        "old_baseline": old_baseline(n),
    }


def _n11_silent_gap_record() -> dict:
    counterexample = build_n11_counterexample()
    allowed = frozenset({()} | (set(all_rooted_triple_symbols()) - FORBIDDEN_MOTIFS))
    state = initial_state(11)
    contiguous_failures = []
    hull_failures = []
    for row_number, row in enumerate(N11_SILENT_ROWS, 1):
        state = advance_row(state, row_mask(row))
        if state is None:
            raise AssertionError("n=11 silent-carrier witness became invalid")
        item = counterexample["states"][row_number - 1]
        if not item["carrier_accepted"]:
            contiguous_failures.append(row_number)
        if not hull_carrier_local_acceptance(state, allowed):
            hull_failures.append(row_number)
    if contiguous_failures != [8] or hull_failures:
        raise AssertionError("silent-carrier falsifier no longer has its declared shape")
    return {
        "width": 11,
        "charged_curvature": counterexample["scope"]["charged_curvature"],
        "contiguous_support_failure_rows": contiguous_failures,
        "silent_packet": counterexample["failure"]["missing_groups"],
        "occupied_groups": counterexample["failure"]["occupied_groups"],
        "repaired_by_next_row": counterexample["failure"]["repaired_by_next_row"],
        "hull_carrier_failure_rows": hull_failures,
        "maximum_face_cut_open_width": counterexample["surviving_restrictions"][
            "maximum_face_cut_open_width"
        ],
        "falsifies": [
            "every low-curvature carrier has contiguous packet support",
            "a carrier must occupy every packet crossed by its occurrence hull",
        ],
    }


def _complete_small_width_record() -> dict:
    artifact = json.loads(STRUCTURAL_GAP.read_text())
    if artifact["scope"]["complete_reachable_and_completable_layers"] != [5, 8]:
        raise AssertionError("unexpected finite structural-gap scope")
    records = {}
    for width in (5, 8):
        coverage = artifact["coverage"][str(width)]
        if coverage["minimum_weight"] != 5:
            raise AssertionError("finite residue-two minimum curvature changed")
        records[str(width)] = {
            "minimum_charged_curvature": coverage["minimum_weight"],
            "reachable_states": coverage["reachable_states"],
            "completable_transitions": coverage["completable_transitions"],
            "equality_states": coverage["equality_states"],
            "equality_edges": coverage["equality_edges"],
            "implied_u_lower_bound": curvature_lower_bound(width, 5),
        }
    return records


def _n17_terminal_debt_record() -> dict:
    history = build_analysis()
    result = json.loads(N17_RESULT.read_text())
    terminal = history["terminal_178"]
    survivors = terminal["states"]
    if len(survivors) != 20:
        raise AssertionError("n=17 survivor count changed")
    if any(item["rooted_debt"] != 2 for item in survivors):
        raise AssertionError("a 178-U survivor does not carry debt two")
    if any(item["budgeted_merge_capacity"] >= item["rooted_debt"] for item in survivors):
        raise AssertionError("a 178-U survivor unexpectedly has enough merge capacity")
    if any(item["accepted_suffix_count"] for item in survivors):
        raise AssertionError("a 178-U terminal suffix unexpectedly closes")
    witness = history["witness_179_suffix"]
    if (
        witness["rooted_debt"],
        witness["remaining_u_budget"],
        witness["budgeted_merge_capacity"],
        witness["accepted_suffix_count"],
    ) != (1, 1, 1, 1):
        raise AssertionError("179-U debt-paying control changed")
    if not (
        result["status"] == "UNSAT"
        and result["n"] == 17
        and result["u_count_limit"] == 178
        and result["final_checkpoint"]["states"] == 0
    ):
        raise AssertionError("n=17 exhaustive result does not certify 178-U UNSAT")
    return {
        "scope": "artifact-backed exact n=17 terminal obstruction only",
        "u_limit": 178,
        "survivors_two_cells_before_terminal": len(survivors),
        "survivor_attachment_debt": 2,
        "survivor_merge_capacity_histogram": terminal["capacity_counts"],
        "survivors_with_accepted_suffix": 0,
        "full_search_status": result["status"],
        "full_search_final_states": result["final_checkpoint"]["states"],
        "minimum_u": result["minimum_u"],
        "extra_over_old_baseline": result["minimum_u"] - old_baseline(17),
        "positive_control": {
            "u_count": 179,
            "hinge_debt": witness["rooted_debt"],
            "remaining_u_budget": witness["remaining_u_budget"],
            "merge_capacity": witness["budgeted_merge_capacity"],
            "accepted_suffixes": witness["accepted_suffix_count"],
        },
    }


def _attachment_skeleton_record() -> dict:
    artifact = json.loads(ATTACHMENT_SKELETON.read_text())
    if artifact.get("schema") != "grid-graphs.residue-two-attachment-skeleton.v1":
        raise AssertionError("unexpected attachment-skeleton schema")
    a23 = artifact["old_4_3_9_falsification"]["A23_observed"]
    if a23 != {
        "maximum_compressed_runs": 12,
        "maximum_cyclic_runs_per_component": 3,
        "maximum_repeated_components": 5,
    }:
        raise AssertionError("A23 no longer gives the required 4/3/9 falsifier")
    complete = artifact["complete_small_equality"]
    fixed = artifact["fixed_equality_controls"]
    affine = artifact["affine_surplus_controls"]
    if any(item["maximum_branch_cost"] > 1 for item in complete.values()):
        raise AssertionError("complete small equality branch bound changed")
    if any(item["maximum_branch_cost"] > 1 for item in fixed.values()):
        raise AssertionError("fixed equality branch bound changed")
    if [affine[f"A{n}"]["maximum_branch_cost"] for n in range(17, 42, 3)] != list(
        range(2, 11)
    ):
        raise AssertionError("sampled affine branch growth changed")
    return {
        "unconditional_theorems": artifact["scope"]["unconditional_results"],
        "annulus_identity_link": artifact["theorems"]["annulus_link"],
        "old_4_3_9_status": artifact["old_4_3_9_falsification"]["status"],
        "A23_old_signature": a23,
        "complete_equality": {
            width: {
                "patterns": item["patterns"],
                "maximum_branch_cost": item["maximum_branch_cost"],
                "branch_histogram": item["maximum_branch_cost_histogram"],
            }
            for width, item in complete.items()
        },
        "fixed_equality_maximum_branch_cost": {
            name: item["maximum_branch_cost"] for name, item in fixed.items()
        },
        "affine_branch_growth": {
            name: {
                "charged_curvature": item["charged_curvature"],
                "maximum_branch_cost": item["maximum_branch_cost"],
            }
            for name, item in affine.items()
        },
        "n11_silent_row8": artifact["n11_silent_frontier_history"][8],
        "simple_row_local_potentials": "falsified on complete n=5,8 equality transitions",
        "theorem_boundary": {
            "proved": (
                "noncrossing and branch_cost<=attachment_surplus for every represented annulus"
            ),
            "conjectured": (
                "curvature-five controls have maximum centered branch cost at most one"
            ),
            "not_implied": (
                "the unconditional skeleton inequalities do not imply K(U)>=5"
            ),
        },
    }


def _cap_merge_potential_record() -> dict:
    artifact = json.loads(CAP_MERGE_POTENTIAL.read_text())
    if artifact.get("schema") != "grid-graphs.residue-two-cap-merge-potential.v1":
        raise AssertionError("unexpected cap/merge potential schema")
    training = artifact["training_certificate"]
    if training["terminal_constant"] != 5 or training["slack_histogram"] != {"0": 588}:
        raise AssertionError("cap/merge training certificate lost constant five")
    terminal = artifact["n17_terminal_debt"]
    if terminal["u178_survivor_deficit_histogram"] != {"1": 18, "2": 2}:
        raise AssertionError("n17 unpayable-debt control changed")
    return {
        "feature_fields": artifact["feature"]["fields"],
        "training": {
            "complete_widths": artifact["scope"]["complete_transition_sources"],
            "feature_states": training["features"],
            "concrete_transitions": training["concrete_transitions"],
            "distinct_constraints": training["distinct_constraints"],
            "terminal_constant": training["terminal_constant"],
            "slack_histogram": training["slack_histogram"],
        },
        "heldout_fixed_paths": artifact["heldout_fixed_paths"],
        "n17_baseline": {
            "path_total_weight": artifact["n17_baseline_extension"]["path_total_weight"],
            "available_slack": artifact["n17_baseline_extension"]["total_available_slack"],
            "slack_by_source": artifact["n17_baseline_extension"]["slack_by_source"][
                "n17-affine-179"
            ],
        },
        "n17_terminal_unpayable_debt": terminal,
        "conclusion": artifact["result"],
        "coverage_warning": artifact["feature"]["finite_width_warning"],
    }


def _persistent_debt_record() -> dict:
    artifact = json.loads(PERSISTENT_DEBT.read_text())
    if artifact.get("schema") != "grid-graphs.residue-two-persistent-debt.v1":
        raise AssertionError("unexpected persistent-debt schema")
    terminal = artifact["n17_terminal_separation"]
    if terminal["u178_unpayable_debt_histogram"] != {"1": 18, "2": 2}:
        raise AssertionError("persistent local n17 separation changed")
    certificate = artifact["min_plus_certificate"]
    if certificate["terminal_constant"] != 5 or set(certificate["slack_histogram"]) != {"0"}:
        raise AssertionError("persistent history certificate lost constant five")
    return {
        "history_fields": artifact["history_channel"]["fields"],
        "local_capacity": artifact["local_capacity_theorem"],
        "complete_history_census": artifact["complete_history_census"],
        "min_plus": {
            "features": certificate["features"],
            "concrete_transitions": certificate["concrete_transitions"],
            "distinct_constraints": certificate["distinct_constraints"],
            "terminal_constant": certificate["terminal_constant"],
            "slack_histogram": certificate["slack_histogram"],
        },
        "n17_terminal": terminal,
        "finite_language": artifact["low_curvature_hull_language"],
        "result": artifact["result"],
    }


def build_ledger() -> dict:
    algebra_samples = [verify_baseline_algebra(n) for n in (5, 17, 119)]
    witnesses = {
        str(n): _pattern_record(
            n,
            residue_two_affine_pattern(n) if n == 17 else residue_two_explicit_pattern(n),
            "fixed near-equality witness" if n == 17 else "fixed equality witness",
        )
        for n in (5, 8, 11, 14, 17)
    }
    return {
        "schema": SCHEMA,
        "scope": {
            "width_independent_result": "exact algebraic reduction only",
            "complete_operational_widths": [5, 8],
            "fixed_witness_widths": [11, 14, 17],
            "terminal_debt_widths": [17],
            "complete_attachment_skeleton_widths": [5, 8],
            "arbitrary_width_baseline_proved": False,
            "arbitrary_width_extra_unit_proved": False,
        },
        "exact_reduction": {
            "charged_curvature": "K(U)=3|U|-2*rho-n=2R+2beta-|U|-n",
            "connected_rank": "rho=(n-1)^2",
            "baseline_equivalence": "K(U)>=5 iff |U|>=6k^2+5k+3 for n=3k+2",
            "samples_are_regression_not_coverage": algebra_samples,
        },
        "complete_finite_certificates": _complete_small_width_record(),
        "fixed_pattern_identities": witnesses,
        "n11_silent_carrier_falsifier": _n11_silent_gap_record(),
        "attachment_skeleton": _attachment_skeleton_record(),
        "cap_merge_potential": _cap_merge_potential_record(),
        "persistent_debt": _persistent_debt_record(),
        "n17_attachment_debt": _n17_terminal_debt_record(),
        "smallest_missing_coverage_lemma": {
            "name": "low-curvature hull-carrier coverage",
            "statement": (
                "For every n=3k+2 and every dual-connected U with K(U)<=5, "
                "every row frontier and centered annulus admits an OUT-rooted hull "
                "attachment skeleton whose live components may cross unoccupied "
                "packets silently, and whose packet/cap transitions belong to a "
                "finite symbolic language with minimum accepting min-plus weight 5."
            ),
            "why_this_scope_is_minimal": (
                "States with K(U)>5 already satisfy the baseline. Contiguous support "
                "cannot replace hull support because the exact n=11 equality witness "
                "has one silent packet at row 8."
            ),
            "certificate_needed": [
                "a width-independent finite hull-carrier state including silent passage",
                "exhaustive symbolic transition coverage for all K<=5 prefixes with accepting suffixes",
                "an exact min-plus potential with initial-to-terminal value at least 5",
                "cap phase or remaining merge capacity beyond scalar debt and branch cost",
                "a persistent unpayable-debt flag capable of distinguishing the n17 terminal",
                "an arbitrary-width silent-hull transition proof preserving the local capacity bound",
            ],
        },
        "next_attachment_obligation": (
            "After baseline coverage, prove that for k>=5 every K=5 accepting-language "
            "candidate reaches attachment debt strictly larger than remaining merge "
            "capacity. The current terminal-debt certificate proves this only at n=17."
        ),
        "limitations": [
            "The algebra samples do not constitute finite-width fitting or coverage.",
            "Only widths 5 and 8 import complete reachable/completable transition censuses.",
            "The n=11 and n=14 patterns are witnesses, not complete searches in this ledger.",
            "The n=17 UNSAT claim is backed by committed exhaustive-search artifacts; this Python ledger does not rerun that search.",
            "The stable affine 19-rule certificates are intentionally excluded from universal coverage because they certify one generated family only.",
            "The old 4/3/9 port-signature bound is false on affine A23 and is not used as a topological premise.",
            "The observed equality branch-cost bound one is conjectural outside complete n=5,8 and fixed n=11,14 controls.",
            "The cap/merge potential uses suffix-enumerated capacity and covers only its declared finite transitions.",
            "The persistent replacement removes suffix enumeration but its generic 2U capacity bound is weak before the terminal cap.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_universal_bound_ledger.py",
            "command": [
                "python3",
                "-B",
                "analysis/residue_certificates/residue_two_universal_bound_ledger.py",
                "--output",
                "analysis/residue_two_universal_bound_ledger.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_ledger(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"universal-bound proof ledger matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
