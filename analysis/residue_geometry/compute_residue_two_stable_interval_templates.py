#!/usr/bin/env python3
"""Wave 2 exact search for a stable residue-two interval template.

The search is deliberately finite and deterministic.  It modifies the proved
affine baseline by a period-at-most-three sequence of horizontal three-bit
interval assignments in the interior packet rectangle, followed by one of 32
bounded cap/seam toggle sets.  There is no randomization, beam search, SAT, or
counterexample-guided refinement.

A miss is only a miss for GRAMMAR_METADATA below.  The default 100,000 limit
exceeds the grammar's 75,296 canonical templates, so the default run is
complete unless a candidate is found first.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Iterable, Iterator

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    run_check,
)
from analysis.patterns.diagonal_patterns import q_formula, residue_two_affine_pattern

SCHEMA = "grid-graphs.residue-two-stable-interval-template-search.v1"
WIDTHS = (23, 26, 29)
KS = (7, 8, 9)
DEFAULT_MAX_TEMPLATES = 100_000
MAX_TEMPLATES = 100_000


@dataclass(frozen=True, order=True, slots=True)
class IntervalOperation:
    value: str
    left: int
    right: int

    def __post_init__(self) -> None:
        if self.value == "keep":
            if (self.left, self.right) != (0, -1):
                raise ValueError("keep has the canonical empty interval")
        elif self.value not in (".", "U") or not 0 <= self.left <= self.right < 3:
            raise ValueError("an assignment is a nonempty interval in one three-bit packet")


KEEP = IntervalOperation("keep", 0, -1)
OPERATIONS = (KEEP,) + tuple(
    IntervalOperation(value, left, right)
    for value in (".", "U")
    for left in range(3)
    for right in range(left, 3)
)
CAP_VARIANTS = (
    "top_left_corner",
    "top_right_corner",
    "bottom_left_corner",
    "bottom_right_corner",
    "top_seam_anchor",
)


@dataclass(frozen=True, order=True, slots=True)
class Template:
    period: int
    row_operations: tuple[IntervalOperation, ...]
    cap_variant_mask: int

    def __post_init__(self) -> None:
        if self.period not in (1, 2, 3) or len(self.row_operations) != self.period:
            raise ValueError("the declared row period must be 1, 2, or 3")
        if self.period > 1 and len(set(self.row_operations)) == 1:
            raise ValueError("constant words must use canonical period one")
        if not 0 <= self.cap_variant_mask < 1 << len(CAP_VARIANTS):
            raise ValueError("cap variant mask is outside the declared five-bit language")


def template_count() -> int:
    periodic_words = len(OPERATIONS) + (len(OPERATIONS) ** 2 - len(OPERATIONS))
    periodic_words += len(OPERATIONS) ** 3 - len(OPERATIONS)
    return periodic_words * (1 << len(CAP_VARIANTS))


GRAMMAR_METADATA = {
    "baseline": "diagonal_patterns.residue_two_affine_pattern(3*k+2)",
    "width_parameter": "n=3*k+2",
    "searched_k": list(KS),
    "bulk_row_domain": "rows 3 <= r < n-3",
    "bulk_packet_domain": "packet indices 2 <= j < k-2; packet j occupies columns 1+3*j..3+3*j",
    "bulk_word": (
        "a canonical row-period word of length 1, 2, or 3; each letter keeps the "
        "baseline or assigns U/preserved(.) to one nonempty contiguous subinterval "
        "of every bulk packet"
    ),
    "operation_order": [asdict(item) for item in OPERATIONS],
    "cap_variants": {
        "semantics": "XOR the named baseline cell; all 32 subsets are enumerated in integer-mask order",
        "names_and_coordinates": {
            "top_left_corner": "(0,0)",
            "top_right_corner": "(0,n-1)",
            "bottom_left_corner": "(n-1,0)",
            "bottom_right_corner": "(n-1,n-1)",
            "top_seam_anchor": "(2,n-2)",
        },
    },
    "canonicalization": (
        "constant period-2 and period-3 words are omitted in favor of period 1; "
        "all other ordered words are distinct declared templates"
    ),
    "enumeration_order": "period, row operation tuple product order, cap mask 0..31",
    "declared_template_count": 75_296,
    "acceptance": [
        "at k=7,8,9 the preserved score is exactly 3*k^2+7*k (equivalently U count q_formula(n))",
        "no unit cell has three forced vertices or a forced diagonal pair",
        "every induced forced component is a straight horizontal or vertical interval",
        "construction_lab.dual_connectivity_check accepts",
        "construction_lab.forest_completion_check accepts",
    ],
    "resource_model": (
        "templates are streamed one at a time; cardinality and local gates precede graph checks; "
        "no frontier collection proportional to the template count is retained"
    ),
}


def iter_templates() -> Iterator[Template]:
    for period in (1, 2, 3):
        for word in itertools.product(OPERATIONS, repeat=period):
            if period > 1 and len(set(word)) == 1:
                continue
            for cap_mask in range(1 << len(CAP_VARIANTS)):
                yield Template(period, word, cap_mask)


def _cap_cells(n: int) -> tuple[tuple[int, int], ...]:
    return ((0, 0), (0, n - 1), (n - 1, 0), (n - 1, n - 1), (2, n - 2))


def materialize(template: Template, k: int) -> list[str]:
    if k < 7:
        raise ValueError("the stable grammar requires k >= 7")
    n = 3 * k + 2
    cells = [list(row) for row in residue_two_affine_pattern(n)]
    for row in range(3, n - 3):
        operation = template.row_operations[(row - 3) % template.period]
        if operation.value == "keep":
            continue
        for packet in range(2, k - 2):
            start = 1 + 3 * packet
            for offset in range(operation.left, operation.right + 1):
                cells[row][start + offset] = operation.value
    for bit, (row, column) in enumerate(_cap_cells(n)):
        if template.cap_variant_mask & (1 << bit):
            cells[row][column] = "." if cells[row][column] == "U" else "U"
    return ["".join(row) for row in cells]


def _local_interval_gates(rows: list[str]) -> tuple[bool, str]:
    """Check the proof-oriented local and straight-component prerequisites."""
    n = len(rows)
    forced = {(r, c) for r, row in enumerate(rows) for c, value in enumerate(row) if value == "."}
    for r in range(n - 1):
        for c in range(n - 1):
            square = ((r, c), (r, c + 1), (r + 1, c), (r + 1, c + 1))
            present = [cell in forced for cell in square]
            if sum(present) >= 3:
                return False, "unit cell has at least three forced vertices"
            if present[0] and present[3] or present[1] and present[2]:
                return False, "unit cell has diagonally opposite forced vertices"

    remaining = set(forced)
    while remaining:
        seed = remaining.pop()
        component = {seed}
        stack = [seed]
        while stack:
            r, c = stack.pop()
            for neighbor in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)):
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    stack.append(neighbor)
        component_rows = {r for r, _ in component}
        component_columns = {c for _, c in component}
        if len(component_rows) != 1 and len(component_columns) != 1:
            return False, "forced component is not a straight interval"
    return True, "ok"


def _template_record(template: Template) -> dict:
    return {
        "period": template.period,
        "row_operations": [asdict(item) for item in template.row_operations],
        "cap_variant_mask": template.cap_variant_mask,
        "cap_variants": [
            name for bit, name in enumerate(CAP_VARIANTS)
            if template.cap_variant_mask & (1 << bit)
        ],
    }


def evaluate_template(template: Template) -> dict | None:
    width_records = []
    for k in KS:
        n = 3 * k + 2
        rows = materialize(template, k)
        u_count = sum(row.count("U") for row in rows)
        preserved = n * n - u_count
        if u_count != q_formula(n) or preserved != 3 * k * k + 7 * k:
            return None
        local_ok, local_reason = _local_interval_gates(rows)
        if not local_ok:
            return None
        dual_ok, connected, total = dual_connectivity_check(rows)
        if not dual_ok:
            return None
        forest_ok, forest_reason = forest_completion_check(rows)
        if not forest_ok:
            return None
        width_records.append({
            "k": k,
            "n": n,
            "u_count": u_count,
            "q_target": q_formula(n),
            "preserved_score": preserved,
            "preserved_target": 3 * k * k + 7 * k,
            "local_interval_gates": local_reason,
            "dual_connected": connected,
            "dual_total": total,
            "forest_completion": forest_reason,
        })
    return {"template": _template_record(template), "width_checks": width_records}


def _rows_hash(rows: list[str]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def independent_replay(template: Template) -> dict:
    """Rematerialize a witness and replay canonical and optional symbolic APIs."""
    records = []
    all_compact = True
    stable_covered = 0
    stable_total = 0
    for k in KS:
        n = 3 * k + 2
        rows = materialize(template, k)
        expected = q_formula(n)
        canonical = run_check(n, rows, expected_u=expected)
        local_ok, local_reason = _local_interval_gates(rows)
        compact = {"accepted": False, "round_trips": 0, "states": n + 1}
        try:
            from analysis.residue_certificates.residue_two_affine_motif_grammar import (
                encode_compact_boundary_defect_frontier,
                expand_compact_boundary_defect_frontier,
                replay_trace,
            )

            states = replay_trace(rows)
            encoded = [encode_compact_boundary_defect_frontier(state) for state in states]
            round_trips = sum(
                expand_compact_boundary_defect_frontier(item) == state
                for item, state in zip(encoded, states, strict=True)
            )
            compact = {"accepted": round_trips == len(states), "round_trips": round_trips, "states": len(states)}
        except (ValueError, AssertionError) as error:
            compact["reason"] = str(error)
        all_compact &= compact["accepted"]

        stable = {"applicable": False, "covered_transitions": 0, "transitions": n}
        if compact["accepted"]:
            from analysis.residue_certificates.residue_two_compact_transition import (
                structural_key,
                trace_observations,
            )
            from analysis.residue_certificates.residue_two_stable_counter_certificate import (
                stable_rule_certificates,
            )
            from analysis.residue_certificates.residue_two_stable_topology_certificate import (
                stable_topology_certificates,
            )

            rules = {
                (item.source, item.action, item.target)
                for item in stable_rule_certificates()
            }
            topology_rules = {
                (item.source, item.action, item.target)
                for item in stable_topology_certificates()
            }
            observed = [structural_key(item) for item in trace_observations(n, rows)]
            covered = sum(rule in rules and rule in topology_rules for rule in observed)
            stable = {"applicable": covered == len(observed), "covered_transitions": covered, "transitions": len(observed)}
            stable_covered += covered
            stable_total += len(observed)

        if not canonical["all_ok"] or not local_ok:
            raise AssertionError(f"independent replay failed at n={n}: {canonical}, {local_reason}")
        records.append({
            "k": k,
            "n": n,
            "rows": rows,
            "rows_sha256": _rows_hash(rows),
            "canonical": canonical,
            "local_interval_gates": {"ok": local_ok, "reason": local_reason},
            "compact_frontier_codec": compact,
            "existing_affine_stable_certificates": stable,
        })
    symbolic = _template_record(template)
    return {
        "independently_replayed": True,
        "stable_symbolic_description": symbolic,
        "stable_symbolic_description_sha256": hashlib.sha256(
            json.dumps(symbolic, sort_keys=True, separators=(",", ":")).encode("ascii")
        ).hexdigest(),
        "same_symbolic_description_all_widths": True,
        "compact_codec_all_widths": all_compact,
        "existing_affine_stable_certificate_coverage": {
            "covered_transitions": stable_covered,
            "transitions": stable_total,
            "note": "These certificates apply only when an observed rule is one of the 19 existing affine rules.",
        },
        "widths": records,
    }


Evaluator = Callable[[Template], dict | None]


def search_templates(
    max_templates: int = DEFAULT_MAX_TEMPLATES,
    *,
    templates: Iterable[Template] | None = None,
    evaluator: Evaluator = evaluate_template,
    replay: Callable[[Template], dict] = independent_replay,
) -> dict:
    if not 1 <= max_templates <= MAX_TEMPLATES:
        raise ValueError(f"max_templates must be between 1 and {MAX_TEMPLATES}")
    declared = template_count() if templates is None else None
    stream = iter_templates() if templates is None else iter(templates)
    examined = 0
    found_template = None
    found = None
    exhausted = True
    for template in stream:
        if examined == max_templates:
            exhausted = False
            break
        examined += 1
        found = evaluator(template)
        if found is not None:
            found_template = template
            break

    if found_template is not None:
        status = "found"
        result = {**found, "independent_replay": replay(found_template)}
    elif exhausted:
        status = "complete_no_candidate"
        result = None
    else:
        status = "incomplete_due_to_cap"
        result = None
    return {
        "schema": SCHEMA,
        "status": status,
        "complete": status in ("found", "complete_no_candidate"),
        "search": {
            "method": "deterministic exhaustive enumeration",
            "random": False,
            "beam": False,
            "sat": False,
            "cegar": False,
            "widths": list(WIDTHS),
            "max_templates": max_templates,
            "templates_examined": examined,
            "declared_template_count": declared,
            "grammar_exhausted": exhausted and found_template is None,
            "stopped_on_first_candidate": found_template is not None,
        },
        "grammar": GRAMMAR_METADATA,
        "candidate": result,
        "claim": (
            "A complete miss excludes exactly the declared finite grammar. A capped miss makes no exclusion "
            "claim. A found template is checked only at k=7,8,9; its shared symbolic descriptor is proof-ready "
            "data, not by itself an arbitrary-k theorem."
        ),
        "provenance": {
            "producer": "analysis/residue_geometry/compute_residue_two_stable_interval_templates.py",
            "command": [
                "python3", "-B", "-m",
                                 'analysis.residue_geometry.compute_residue_two_stable_interval_templates',
                "--output", "analysis/residue_two_stable_interval_templates.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-templates", type=int, default=DEFAULT_MAX_TEMPLATES)
    args = parser.parse_args()
    manifest = search_templates(args.max_templates)
    args.output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(
        f"{manifest['status']}: examined {manifest['search']['templates_examined']} "
        f"templates; wrote {args.output}"
    )


if __name__ == "__main__":
    main()
