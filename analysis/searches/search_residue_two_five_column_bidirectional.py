#!/usr/bin/env python3
"""Lean exact bidirectional solver for the n=20 five-column corridor.

The search keeps ordinary in-memory dictionaries.  It first builds exact
top-down and vertically reflected bottom-up censuses at cuts 8/9, 9/10, and
13/14, chooses the cut with the fewest cost/quota-compatible state pairs, and
then exhausts those joins.  A timeout or state guard always remains
inconclusive.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import signal
import time
from dataclasses import dataclass
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT, analysis_path, source_path
from analysis.searches.search_residue_two_phase_front import _packet_names
from analysis.searches.search_residue_two_phase_packet_corridor_22 import phase_rows
from analysis.searches.search_residue_two_two_lobe_phase_corridor import (
    CAP_DISTRIBUTIONS,
    FIXED_BODY_ROWS,
    MUTABLE_ROWS,
    TARGET_U,
    N,
    file_sha256,
    masks_with_u_count,
    rows_sha256,
)
from analysis.searches.search_residue_two_two_lobe_phase_corridor_five_columns import (
    mutable_row_words,
    row_domains,
    validate_scope,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    merge_frontier_partition,
    merge_frontier_profile,
    render_mask,
    row_mask,
)

CUTS = (8, 9, 13)
MUTABLE_H_QUOTA = 11
DEFAULT_RESULT = analysis_path("search_residue_two_five_column_bidirectional_result.json")
DEFAULT_WITNESS = analysis_path("residue_two_five_column_bidirectional_witness.txt")


class MemoryGuardError(RuntimeError):
    pass


@dataclass(slots=True)
class Node:
    state: FrontierState
    h_count: int
    ways: int
    parent: Node | None
    mask: int | None


# H count is outside FrontierState, so quota classes are separate dictionaries;
# within each class the complete, unprojected FrontierState is the exact key.
Layer = dict[int, dict[FrontierState, Node]]


def _iter_nodes(layer: Layer):
    for h_count in sorted(layer):
        yield from layer[h_count].values()


def _state_count(layer: Layer) -> int:
    return sum(map(len, layer.values()))


def _ways(layer: Layer) -> int:
    return sum(node.ways for node in _iter_nodes(layer))


def _layer_hash(layer: Layer) -> str:
    records = sorted(
        (
            h_count,
            state.n,
            state.row_index,
            state.previous_u_mask,
            state.partition,
            state.u_cost,
            state.cycle_excess,
            node.ways,
        )
        for h_count, states in layer.items()
        for state, node in states.items()
    )
    return hashlib.sha256(
        json.dumps(records, separators=(",", ":")).encode("ascii")
    ).hexdigest()


def _root() -> Layer:
    state = initial_state(N)
    return {0: {state: Node(state, 0, 1, None, None)}}


def _row_choices(
    rows: list[str], domains: dict[int, tuple[str, ...]], row: int
) -> tuple[tuple[int, int], ...]:
    choices = domains.get(row, (rows[row],))
    return tuple(
        (row_mask(choice), _packet_names(choice).count("H") if row in MUTABLE_ROWS else 0)
        for choice in choices
    )


def _add(
    outgoing: Layer,
    child: FrontierState,
    h_count: int,
    parent: Node,
    mask: int,
    max_states: int,
) -> bool:
    quota = outgoing.setdefault(h_count, {})
    old = quota.get(child)
    if old is None:
        if _state_count(outgoing) >= max_states:
            raise MemoryGuardError(f"exact layer exceeded {max_states:,} states")
        quota[child] = Node(child, h_count, parent.ways, parent, mask)
        return True
    old.ways += parent.ways
    return False


def _expand_row(
    layer: Layer,
    choices: tuple[tuple[int, int], ...],
    mutable_processed: int,
    max_states: int,
) -> tuple[Layer, dict]:
    outgoing: Layer = {}
    viable = new_states = 0
    remaining_mutable = len(MUTABLE_ROWS) - mutable_processed
    for parent in _iter_nodes(layer):
        for mask, h_delta in choices:
            h_count = parent.h_count + h_delta
            if h_count > MUTABLE_H_QUOTA or h_count + 5 * remaining_mutable < MUTABLE_H_QUOTA:
                continue
            child = advance_row(parent.state, mask)
            if child is None or child.u_cost > TARGET_U:
                continue
            viable += 1
            new_states += _add(outgoing, child, h_count, parent, mask, max_states)
    return outgoing, {
        "incoming_states": _state_count(layer),
        "domain_size": len(choices),
        "transitions_attempted": _state_count(layer) * len(choices),
        "viable_transitions": viable,
        "outgoing_states": _state_count(outgoing),
        "new_states": new_states,
        "assignments_represented": _ways(outgoing),
        "frontier_sha256": _layer_hash(outgoing),
    }


def _summary(layer: Layer) -> dict:
    return {
        "states": _state_count(layer),
        "assignments_represented": _ways(layer),
        "h_counts": {str(h): len(states) for h, states in sorted(layer.items())},
        "u_costs": sorted({state.u_cost for node in _iter_nodes(layer) for state in (node.state,)}),
        "frontier_sha256": _layer_hash(layer),
    }


def forward_census(
    rows: list[str], domains: dict[int, tuple[str, ...]], max_states: int, report: bool
) -> tuple[dict[int, Layer], list[dict]]:
    layer = _root()
    levels: dict[int, Layer] = {}
    records = []
    mutable_processed = 0
    for row in range(max(CUTS) + 1):
        if row in MUTABLE_ROWS:
            mutable_processed += 1
        layer, stats = _expand_row(
            layer, _row_choices(rows, domains, row), mutable_processed, max_states
        )
        stats.update(row=row, direction="forward")
        records.append(stats)
        if row in CUTS:
            levels[row] = layer
        if report:
            print(
                f"forward row={row} states={stats['outgoing_states']} "
                f"assignments={stats['assignments_represented']}",
                flush=True,
            )
    return levels, records


def cap_lane_choices(rows: list[str], distribution: tuple[int, int] | None):
    if distribution is None:
        return (
            ("fixed", (row_mask(rows[19]),), (row_mask(rows[18]),)),
        )
    first, second = distribution
    return (("all masks", masks_with_u_count(second), masks_with_u_count(first)),)


def backward_census(
    rows: list[str],
    domains: dict[int, tuple[str, ...]],
    distribution: tuple[int, int] | None,
    max_states: int,
    report: bool,
) -> tuple[dict[int, Layer], list[dict]]:
    layer = _root()
    levels: dict[int, Layer] = {}
    records = []
    mutable_processed = 0
    _, row19_masks, row18_masks = cap_lane_choices(rows, distribution)[0]
    for row in range(19, min(CUTS), -1):
        if row == 19:
            choices = tuple((mask, 0) for mask in row19_masks)
        elif row == 18:
            choices = tuple((mask, 0) for mask in row18_masks)
        else:
            choices = _row_choices(rows, domains, row)
        if row in MUTABLE_ROWS:
            mutable_processed += 1
        layer, stats = _expand_row(layer, choices, mutable_processed, max_states)
        stats.update(row=row, direction="reflected-bottom")
        records.append(stats)
        cut = row - 1
        if cut in CUTS:
            levels[cut] = layer
        if report:
            label = "fixed" if distribution is None else f"{distribution[0]}/{distribution[1]}"
            print(
                f"bottom lane={label} row={row} states={stats['outgoing_states']} "
                f"assignments={stats['assignments_represented']}",
                flush=True,
            )
    return levels, records


def compatible_pair_census(forward: Layer, backward: Layer) -> dict:
    state_pairs = assignment_pairs = 0
    buckets = []
    for forward_h, forward_states in sorted(forward.items()):
        backward_h = MUTABLE_H_QUOTA - forward_h
        backward_states = backward.get(backward_h, {})
        by_cost: dict[int, tuple[int, int]] = {}
        for node in backward_states.values():
            count, ways = by_cost.get(node.state.u_cost, (0, 0))
            by_cost[node.state.u_cost] = (count + 1, ways + node.ways)
        for forward_node in forward_states.values():
            count, ways = by_cost.get(TARGET_U - forward_node.state.u_cost, (0, 0))
            state_pairs += count
            assignment_pairs += forward_node.ways * ways
        if forward_states and backward_states:
            buckets.append(
                {
                    "forward_h": forward_h,
                    "backward_h": backward_h,
                    "forward_states": len(forward_states),
                    "backward_states": len(backward_states),
                }
            )
    return {
        "candidate_state_pairs": state_pairs,
        "candidate_assignment_pairs": assignment_pairs,
        "quota_buckets": buckets,
    }


def _masks(node: Node) -> list[int]:
    masks = []
    while node.parent is not None:
        assert node.mask is not None
        masks.append(node.mask)
        node = node.parent
    masks.reverse()
    return masks


def _validate_witness(candidate: list[str], base: list[str], distribution) -> dict:
    from analysis.patterns.construction_lab import run_check

    info = run_check(N, candidate, verbose=False)
    domains = row_domains(base)
    mutable_h = sum(_packet_names(candidate[row]).count("H") for row in MUTABLE_ROWS)
    expected_distribution = (
        (base[18].count("U"), base[19].count("U"))
        if distribution is None
        else distribution
    )
    scope_ok = (
        all(candidate[row] == base[row] for row in FIXED_BODY_ROWS)
        and all(candidate[row] in domains[row] for row in MUTABLE_ROWS)
        and (candidate[18].count("U"), candidate[19].count("U")) == expected_distribution
        and mutable_h == MUTABLE_H_QUOTA
    )
    result = {
        **info,
        "scope_ok": scope_ok,
        "mutable_h": mutable_h,
        "rows_sha256": rows_sha256(candidate),
    }
    if not info["all_ok"] or not scope_ok:
        raise AssertionError(f"independent run_check rejected joined witness: {result}")
    return result


def join_lane(
    forward: Layer,
    backward: Layer,
    rows: list[str],
    distribution: tuple[int, int] | None,
) -> tuple[dict, list[str] | None, dict | None]:
    backward_buckets: dict[tuple[int, int], list[Node]] = {}
    for node in _iter_nodes(backward):
        backward_buckets.setdefault((node.h_count, node.state.u_cost), []).append(node)
    checked = represented = connected = connected_assignments = 0
    minimum_profile: tuple[int, int] | None = None
    witness = None
    validation = None
    for top in _iter_nodes(forward):
        key = (MUTABLE_H_QUOTA - top.h_count, TARGET_U - top.state.u_cost)
        for bottom in backward_buckets.get(key, ()):
            checked += 1
            pair_ways = top.ways * bottom.ways
            represented += pair_ways
            # Exercise both exact public merge helpers; profile is derived from
            # the same full partitions and the partition is useful diagnostics.
            partition, cycles = merge_frontier_partition(top.state, bottom.state)
            profile = merge_frontier_profile(top.state, bottom.state)
            if profile != (len(set(partition)), cycles):
                raise AssertionError("frontier merge helpers disagree")
            minimum_profile = profile if minimum_profile is None else min(minimum_profile, profile)
            if profile[0] != 1:
                continue
            connected += 1
            connected_assignments += pair_ways
            if witness is None:
                masks = [*_masks(top), *reversed(_masks(bottom))]
                candidate = [render_mask(mask, N) for mask in masks]
                validation = _validate_witness(candidate, rows, distribution)
                witness = candidate
    return {
        "exact": True,
        "result": "positive" if witness is not None else "negative",
        "pairs_checked": checked,
        "assignment_pairs_checked": represented,
        "connected_state_pairs": connected,
        "connected_assignment_pairs": connected_assignments,
        "minimum_profile": list(minimum_profile) if minimum_profile is not None else None,
    }, witness, validation


def _lane_name(distribution: tuple[int, int] | None) -> str:
    return "fixed" if distribution is None else f"all-{distribution[0]}-{distribution[1]}"


def provenance(rows: list[str]) -> dict:
    directory = ANALYSIS_ROOT
    paths = {
        "generator": Path(__file__),
        "phase_witness": directory / "residue_two_phase_front_witness.txt",
        "five_column_domain": source_path('search_residue_two_two_lobe_phase_corridor_five_columns.py'),
        "phase_front": source_path('search_residue_two_phase_front.py'),
        "phase_rows_source": source_path('search_residue_two_phase_packet_corridor_22.py'),
        "corridor_caps": source_path('search_residue_two_two_lobe_phase_corridor.py'),
        "frontier": source_path('tile_grammar.py'),
    }
    return {
        "phase_witness_rows_sha256": rows_sha256(rows),
        "source_files": {
            name: {"path": path.name, "sha256": file_sha256(path)}
            for name, path in paths.items()
        },
    }


def scope(rows: list[str]) -> dict:
    domains = row_domains(rows)
    return {
        "n": N,
        "target_u": TARGET_U,
        "fixed_body_rows": [[0, 3], [10, 13]],
        "mutable_rows": [[4, 9], [14, 17]],
        "mutable_packet_columns": [0, 1, 2, 3, 4],
        "frozen_packet_columns": [5],
        "row_language": "complete basic L*(X|H)+R*, center width <=5, ending R",
        "mutable_h_quota": MUTABLE_H_QUOTA,
        "domain_sizes": {str(row): len(domains[row]) for row in MUTABLE_ROWS},
        "domain_hashes": {str(row): rows_sha256(domains[row]) for row in MUTABLE_ROWS},
        "cuts": [f"{cut}/{cut + 1}" for cut in CUTS],
        "cap_lanes": ["fixed", *[list(value) for value in CAP_DISTRIBUTIONS]],
        "storage": "ordinary in-memory dictionaries",
        "deduplication": "mutable H bucket then full unprojected FrontierState",
        "multiplicities": "exact within each cap lane",
        "aggregate_lane_counts": (
            "lane-counted; fixed cap also appears in all-(18,2), so lane sums "
            "are not distinct-union counts"
        ),
    }


def solve(max_states: int, report: bool = True) -> tuple[dict, list[str] | None]:
    rows = phase_rows()
    validate_scope(rows)
    domains = row_domains(rows)
    fixed_cost = sum(rows[row].count("U") for row in FIXED_BODY_ROWS) + 20
    if fixed_cost + 12 * len(MUTABLE_ROWS) + MUTABLE_H_QUOTA != TARGET_U:
        raise AssertionError("H quota no longer implies the target U count")
    record = {
        "schema": "grid-graphs.residue-two-five-column-bidirectional.v1",
        "exact": False,
        "result": "incomplete",
        "provenance": provenance(rows),
        "scope": scope(rows),
        "memory_guard_states_per_layer": max_states,
        "forward_layers": [],
        "lanes": [],
        "cut_census": [],
        "chosen_cut": None,
        "witness": None,
        "independent_validation": None,
    }
    forward, forward_stats = forward_census(rows, domains, max_states, report)
    record["forward_layers"] = forward_stats
    lane_data = []
    for distribution in (None, *CAP_DISTRIBUTIONS):
        backward, stats = backward_census(
            rows, domains, distribution, max_states, report
        )
        lane = {
            "name": _lane_name(distribution),
            "distribution": (
                [rows[18].count("U"), rows[19].count("U")]
                if distribution is None
                else list(distribution)
            ),
            "census_status": "complete",
            "backward_layers": stats,
            "cuts": {},
            "join": None,
        }
        for cut in CUTS:
            census = compatible_pair_census(forward[cut], backward[cut])
            lane["cuts"][f"{cut}/{cut + 1}"] = {
                "forward": _summary(forward[cut]),
                "backward": _summary(backward[cut]),
                **census,
            }
        record["lanes"].append(lane)
        lane_data.append((distribution, backward, lane))

    for cut in CUTS:
        label = f"{cut}/{cut + 1}"
        record["cut_census"].append(
            {
                "cut": label,
                "candidate_state_pairs": sum(
                    lane["cuts"][label]["candidate_state_pairs"]
                    for _, _, lane in lane_data
                ),
                "candidate_assignment_pairs": sum(
                    lane["cuts"][label]["candidate_assignment_pairs"]
                    for _, _, lane in lane_data
                ),
                "peak_side_states": max(
                    max(
                        lane["cuts"][label]["forward"]["states"],
                        lane["cuts"][label]["backward"]["states"],
                    )
                    for _, _, lane in lane_data
                ),
            }
        )
    chosen = min(
        record["cut_census"],
        key=lambda item: (item["candidate_state_pairs"], item["peak_side_states"], item["cut"]),
    )
    record["chosen_cut"] = chosen["cut"]
    chosen_cut = int(chosen["cut"].split("/")[0])
    first_witness = None
    for distribution, backward, lane in lane_data:
        joined, witness, validation = join_lane(
            forward[chosen_cut], backward[chosen_cut], rows, distribution
        )
        lane["join"] = joined
        if first_witness is None and witness is not None:
            first_witness, record["independent_validation"] = witness, validation
    record["witness"] = first_witness
    record["exact"] = True
    record["result"] = "positive" if first_witness is not None else "negative"
    return record, first_witness


def _timeout(_signum: int, _frame: object) -> None:
    raise TimeoutError


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--max-seconds", type=int, default=720)
    parser.add_argument("--max-states", type=int, default=1_000_000)
    parser.add_argument("--result", type=Path, default=DEFAULT_RESULT)
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    args = parser.parse_args()
    if not 1 <= args.max_seconds <= 720:
        parser.error("--max-seconds must be in 1..720")
    if args.max_states < 1:
        parser.error("--max-states must be positive")

    started = time.monotonic()
    record = None
    witness = None
    old_handler = signal.signal(signal.SIGALRM, _timeout)
    signal.alarm(args.max_seconds)
    try:
        record, witness = solve(args.max_states, report=not args.quiet)
        stop_reason = "completed"
    except (TimeoutError, MemoryGuardError) as error:
        stop_reason = (
            "time limit reached" if isinstance(error, TimeoutError) else str(error)
        ) + "; exact search incomplete; no negative claim"
        rows = phase_rows()
        record = {
            "schema": "grid-graphs.residue-two-five-column-bidirectional.v1",
            "exact": False,
            "result": "incomplete",
            "provenance": provenance(rows),
            "scope": scope(rows),
            "memory_guard_states_per_layer": args.max_states,
            "stop_reason": stop_reason,
            "witness": None,
            "independent_validation": None,
        }
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
    assert record is not None
    record["run"] = {
        "max_seconds": args.max_seconds,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "stop_reason": stop_reason,
    }
    args.result.write_text(json.dumps(record, indent=2) + "\n")
    if witness is not None:
        args.witness.write_text("\n".join(witness) + "\n")
    if not record["exact"]:
        print(f"INCOMPLETE: {stop_reason}")
        print(f"result={args.result}")
        raise SystemExit(2)
    print(f"EXACT {record['result'].upper()} cut={record['chosen_cut']}")
    print(f"result={args.result}")


if __name__ == "__main__":
    main()
