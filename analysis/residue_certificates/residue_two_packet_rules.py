#!/usr/bin/env python3
"""Observed transition-rule census for residue-two row packets.

The census is finite diagnostic evidence.  It replays every edge of the
complete n=5 and n=8 equality corridors and three selected larger traces; it
does not assert that the observed local rules are complete at other widths.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.tiles.row_packet_transition import (
    PacketRowCursor,
    append_packet,
    finish_row,
    start_row,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    PartialRowState,
    _append_row_bits,
    _initial_partial_row,
    _partial_row_has_sealed_component,
    _row_node_order,
    advance_row,
    initial_state,
    render_mask,
    row_mask,
)
from analysis.transport.equality_corridor import (
    CorridorEdge,
    build_equality_corridor,
    structural_key,
)

SCHEMA = "grid-graphs.residue-two-packet-rules.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_packet_rules.json")
CORRIDOR_WIDTHS = (5, 8)
TRACE_WIDTHS = (11, 14, 17)
LOCAL_OFFSETS = tuple(range(-3, 3))


@dataclass(frozen=True, slots=True)
class PacketRule:
    """One width-normalized observed update at a cap or packet segment."""

    segment_mode: str
    row_phase: int
    row_boundary_mode: str
    prior_word: str
    current_word: str
    right_u_before: bool
    right_u_after: bool
    d_u: int
    d_edges: int
    d_cycles: int
    d_rank: int
    working_debt_delta: int
    cut_signature_before: tuple[tuple[int | None, ...], tuple[int | None, ...]]
    cut_signature_after: tuple[tuple[int | None, ...], tuple[int | None, ...]]


def row_boundary_mode(state: FrontierState) -> str:
    """Classify the row being consumed, independently of its width."""
    if state.row_index == 0:
        return "top"
    if state.row_index + 1 == state.n:
        return "bottom"
    return "bulk"


def working_component_debt(incoming: FrontierState, partial: PartialRowState) -> int:
    """Count non-OUT components still represented at the current scan cut.

    Old faces strictly left of the cut have retired.  New faces strictly left
    of the cut are complete.  This is exactly the retained-node convention
    used by the private partial-row sealing check, with OUT excluded as debt.
    """
    order, old, new = _row_node_order(incoming)
    labels = dict(zip(order, partial.partition))
    retired_end = max(0, partial.columns - 1)
    live = [*old[retired_end:], *new[:retired_end]]
    out_label = labels[("out", 0)]
    return len({labels[node] for node in live if labels[node] != out_label})


def rooted_cut_signature(
    incoming: FrontierState, partial: PartialRowState
) -> tuple[tuple[int | None, ...], tuple[int | None, ...]]:
    """Return a rooted six-face window on each side of the row scan state.

    Offsets -3..2 are relative to the cut column.  Old faces always exist away
    from the top row; new faces enter the signature only once both endpoint
    columns have been consumed.  Labels are jointly canonicalized with OUT=0,
    so attachment and carry identity is retained between old and new windows.
    """
    order, old, new = _row_node_order(incoming)
    labels = dict(zip(order, partial.partition))
    canonical = {labels[("out", 0)]: 0}
    completed_new = min(len(new), max(0, partial.columns - 1))

    def window(nodes: list[object], available: int) -> tuple[int | None, ...]:
        result: list[int | None] = []
        for offset in LOCAL_OFFSETS:
            slot = partial.columns + offset
            if not 0 <= slot < available:
                result.append(None)
                continue
            label = labels[nodes[slot]]
            canonical.setdefault(label, len(canonical))
            result.append(canonical[label])
        return tuple(result)

    return window(old, len(old)), window(new, completed_new)


def _segment_edges(incoming: FrontierState, before: PartialRowState, bits: str) -> int:
    edges = 0
    right_u = before.right_u
    for offset, bit in enumerate(bits):
        column = before.columns + offset
        current_u = bit == "U"
        edges += current_u and bool(incoming.previous_u_mask & (1 << column))
        edges += current_u and right_u
        right_u = current_u
    return int(edges)


def _rule(
    incoming: FrontierState,
    before: PacketRowCursor,
    after: PacketRowCursor,
    mode: str,
    bits: str,
) -> PacketRule:
    start = before.partial.columns
    prior = render_mask(incoming.previous_u_mask, incoming.n)[start : start + len(bits)]
    d_edges = _segment_edges(incoming, before.partial, bits)
    d_cycles = after.partial.cycle_excess - before.partial.cycle_excess
    if not 0 <= d_cycles <= d_edges:
        raise AssertionError("partial cycle increment is not an edge nullity")
    return PacketRule(
        segment_mode=mode,
        row_phase=incoming.row_index % 3,
        row_boundary_mode=row_boundary_mode(incoming),
        prior_word=prior,
        current_word=bits,
        right_u_before=before.partial.right_u,
        right_u_after=after.partial.right_u,
        d_u=after.partial.row_u_cost - before.partial.row_u_cost,
        d_edges=d_edges,
        d_cycles=d_cycles,
        d_rank=d_edges - d_cycles,
        working_debt_delta=(
            working_component_debt(incoming, after.partial)
            - working_component_debt(incoming, before.partial)
        ),
        cut_signature_before=rooted_cut_signature(incoming, before.partial),
        cut_signature_after=rooted_cut_signature(incoming, after.partial),
    )


def replay_row_segments(
    incoming: FrontierState, row: str
) -> tuple[tuple[PacketRule, ...], FrontierState]:
    """Replay one cap/three-bit-packet/cap row and return exact local rules."""
    if incoming.n % 3 != 2 or len(row) != incoming.n or set(row) - {".", "U"}:
        raise ValueError("packet replay requires an n=3k+2 row over '.' and 'U'")

    cursor = PacketRowCursor(incoming, _initial_partial_row(incoming))
    rules = []
    prefix = row[0]
    after = start_row(incoming, prefix)
    if after is None:
        raise ValueError("row seals a component in its prefix cap")
    rules.append(_rule(incoming, cursor, after, "prefix_cap", prefix))
    cursor = after

    for start in range(1, incoming.n - 1, 3):
        bits = row[start : start + 3]
        after = append_packet(cursor, bits, {bits: bits})
        if after is None:
            raise ValueError(f"row seals a component in packet at column {start}")
        rules.append(_rule(incoming, cursor, after, "packet", bits))
        cursor = after

    suffix = row[-1]
    suffix_partial = _append_row_bits(incoming, cursor.partial, suffix)
    if _partial_row_has_sealed_component(incoming, suffix_partial):
        raise ValueError("row seals a component in its suffix cap")
    suffix_cursor = PacketRowCursor(incoming, suffix_partial)
    rules.append(_rule(incoming, cursor, suffix_cursor, "suffix_cap", suffix))
    transition = finish_row(cursor, suffix)
    if transition is None:
        raise ValueError("row fails bottom closure")

    totals = segment_totals(rules)
    if transition.outgoing.u_cost - incoming.u_cost != totals["dU"]:
        raise AssertionError("segment U increments do not reproduce the row")
    if transition.outgoing.cycle_excess - incoming.cycle_excess != totals["dCycles"]:
        raise AssertionError("segment cycle increments do not reproduce the row")
    return tuple(rules), transition.outgoing


def segment_totals(rules: tuple[PacketRule, ...] | list[PacketRule]) -> dict[str, int]:
    """Return exact additive row totals, including its single unit charge."""
    totals = {
        "dU": sum(rule.d_u for rule in rules),
        "dEdges": sum(rule.d_edges for rule in rules),
        "dCycles": sum(rule.d_cycles for rule in rules),
        "dRank": sum(rule.d_rank for rule in rules),
        "workingDebtDelta": sum(rule.working_debt_delta for rule in rules),
    }
    totals["weight"] = 3 * totals["dU"] - 2 * totals["dRank"] - 1
    return totals


def rule_id(rule: PacketRule) -> str:
    payload = json.dumps(asdict(rule), separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


def _edge_record(width: int, edge: CorridorEdge, incoming: FrontierState) -> tuple[dict, tuple[PacketRule, ...]]:
    row = render_mask(edge.mask, width)
    rules, outgoing = replay_row_segments(incoming, row)
    totals = segment_totals(rules)
    expected = {
        "dU": edge.d_u,
        "dEdges": edge.d_rank + edge.d_cycles,
        "dCycles": edge.d_cycles,
        "dRank": edge.d_rank,
        "weight": edge.weight,
    }
    if any(totals[field] != value for field, value in expected.items()):
        raise AssertionError(f"segment ledger disagrees with n={width} row {edge.row}")
    if structural_key(outgoing) != edge.outgoing:
        raise AssertionError("packet replay disagrees with corridor outgoing state")
    return {
        "row": edge.row,
        "incoming_mask": render_mask(incoming.previous_u_mask, width),
        "incoming_partition": list(incoming.partition),
        "current_row": row,
        "rule_ids": [rule_id(rule) for rule in rules],
        "totals": totals,
    }, rules


def _trace_records(width: int) -> tuple[list[dict], list[PacketRule]]:
    rows = residue_two_affine_pattern(width) if width == 17 else residue_two_explicit_pattern(width)
    incoming = initial_state(width)
    records = []
    all_rules = []
    for index, row in enumerate(rows):
        rules, outgoing = replay_row_segments(incoming, row)
        direct = advance_row(incoming, row_mask(row))
        if direct != outgoing:
            raise AssertionError(f"fixed n={width} packet replay failed at row {index}")
        records.append({
            "row": index,
            "incoming_mask": render_mask(incoming.previous_u_mask, width),
            "current_row": row,
            "rule_ids": [rule_id(rule) for rule in rules],
            "totals": segment_totals(rules),
        })
        all_rules.extend(rules)
        incoming = outgoing
    return records, all_rules


def _support_comparison(supports: dict[int, set[str]]) -> dict:
    left, right = (supports[n] for n in CORRIDOR_WIDTHS)
    return {
        "n5_rules": len(left),
        "n8_rules": len(right),
        "shared_rules": len(left & right),
        "n5_only_rules": len(left - right),
        "n8_only_rules": len(right - left),
        "jaccard": [len(left & right), len(left | right)],
    }


def build_artifact() -> dict:
    """Build the complete finite census and all fixed-trace coverage counts."""
    catalog: dict[str, PacketRule] = {}
    corridor_records: dict[str, dict] = {}
    supports: dict[int, set[str]] = {}
    for width in CORRIDOR_WIDTHS:
        corridor = build_equality_corridor(width)
        records = []
        counts: Counter[str] = Counter()
        for edges in corridor.corridor_edges:
            for edge in edges:
                record, rules = _edge_record(
                    width, edge, corridor.layers[edge.row][edge.incoming]
                )
                records.append(record)
                for rule in rules:
                    identifier = rule_id(rule)
                    if identifier in catalog and catalog[identifier] != rule:
                        raise AssertionError("truncated rule digest collision")
                    catalog[identifier] = rule
                    counts[identifier] += 1
        supports[width] = set(counts)
        corridor_records[str(width)] = {
            "edges": len(records),
            "segments": sum(counts.values()),
            "distinct_rules": len(counts),
            "rule_occurrences": dict(sorted(counts.items())),
            "edge_ledger": records,
        }

    baseline = supports[5] | supports[8]
    traces = {}
    for width in TRACE_WIDTHS:
        records, rules = _trace_records(width)
        identifiers = [rule_id(rule) for rule in rules]
        counts = Counter(identifiers)
        covered = [identifier for identifier in identifiers if identifier in baseline]
        uncovered = [identifier for identifier in identifiers if identifier not in baseline]
        for rule in rules:
            identifier = rule_id(rule)
            if identifier in catalog and catalog[identifier] != rule:
                raise AssertionError("truncated rule digest collision")
            catalog[identifier] = rule
        traces[str(width)] = {
            "selection": "fixed near-equality 179-U witness" if width == 17 else "fixed equality witness",
            "rows": len(records),
            "segments": len(rules),
            "covered_occurrences": len(covered),
            "uncovered_occurrences": len(uncovered),
            "covered_distinct_rules": len(set(covered)),
            "uncovered_distinct_rules": len(set(uncovered)),
            "uncovered_rule_ids": sorted(set(uncovered)),
            "rule_occurrences": dict(sorted(counts.items())),
            "row_ledger": records,
        }

    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-observed-packet-transition-diagnostic-only",
            "complete_equality_corridors": list(CORRIDOR_WIDTHS),
            "fixed_equality_witnesses": [11, 14],
            "near_equality_control": {"width": 17, "u_count": 179},
            "theorem_or_certificate": False,
            "coverage_beyond_observed_edges_claimed": False,
        },
        "definitions": {
            "packet_layout": "one left cap bit, consecutive three-bit packets, one right cap bit",
            "row_phase": "zero-based row index modulo three before consuming the row",
            "row_boundary_mode": "top, bulk, or bottom row being consumed",
            "working_component_debt": "non-OUT labels on unretired old faces or completed new faces at the scan cut",
            "cut_signature": "jointly OUT-rooted old/new face labels at offsets -3..2 from the scan cut; null means absent or not completed",
            "rule_normalization": "width, absolute row and absolute packet position are omitted; cap mode and local boundary effects remain observable",
            "row_weight": "sum over segments of 3*dU-2*dRank, minus one row charge",
        },
        "support_comparison": _support_comparison(supports),
        "corridors": corridor_records,
        "fixed_traces": traces,
        "rule_catalog": {
            identifier: asdict(rule) for identifier, rule in sorted(catalog.items())
        },
        "limitations": [
            "Only n=5 and n=8 are complete equality corridors.",
            "The n=11, n=14 and n=17 results concern one fixed witness each.",
            "An uncovered rule is a baseline support miss, not evidence that the transition is invalid.",
            "The six-face cut window is an observed local signature, not proved sufficient control.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_packet_rules.py",
            "command": ["python3", "-B", "-m",
                                         'analysis.residue_certificates.residue_two_packet_rules', "--output", "analysis/residue_two_packet_rules.json"],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if args.output is None or not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"finite packet-rule census matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
