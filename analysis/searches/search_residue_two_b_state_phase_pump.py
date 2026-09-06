#!/usr/bin/env python3
"""Exact fixed-schedule B20->B23 pump in the bounded phase-front row language."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from analysis.patterns.construction_lab import DSU, dual_connectivity_check, forest_completion_check
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.searches.search_residue_two_b_state_pump import SOURCE, fixed_affine_schedule, load_pattern
from analysis.searches.search_residue_two_moving_seam import (
    PACKET_NAME,
    _rank_deficit_impossible,
    row_packet_domains,
    write_result,
)
from analysis.searches.search_residue_two_phase_front import PHASE_ALPHABET, row_words
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    merge_frontier_profile,
    render_mask,
    row_mask,
)
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_b20_to_b23_phase_result.json"
N = 23
PACKETS = 7
FIXED_ROWS = (*range(6), *range(17, 23))
TARGETED_S_SITES = {
    9: (3, 4, 5),
    10: (5, 6),
    11: (3, 4, 5),
    12: (3, 4, 5),
    13: (5,),
    15: (4, 5, 6),
    16: (5, 6),
}


@dataclass(slots=True)
class Node:
    state: FrontierState
    parent: Node | None
    mask: int | None


@dataclass(frozen=True, slots=True)
class LayerStats:
    side: str
    row: int
    incoming_states: int
    row_domain: int
    attempted: int
    live: int
    deduplicated_states: int
    cost_prunes: int
    rank_prunes: int


def permitted_words(target_row: int, mode: str) -> tuple[str, ...]:
    if mode != "targeted":
        return row_words(PACKETS, mode)
    sites = set(TARGETED_S_SITES.get(target_row, ()))
    return tuple(
        word
        for word in row_words(PACKETS, "phase")
        if word.count("S") <= 1
        and all(index in sites for index, symbol in enumerate(word) if symbol == "S")
    )


def phase_masks_for_edge(
    source_row: str, target_row: int, seam: int, radius: int, mode: str
) -> tuple[int, ...]:
    specification = row_packet_domains(source_row, seam, radius)
    if specification is None:
        return ()
    prefix, suffix, domains = specification
    if prefix != "." or suffix != ".":
        return ()
    names_to_binary = {
        symbol: PACKET_NAME[pattern] for symbol, pattern in PHASE_ALPHABET.items()
    }
    masks = set()
    for word in permitted_words(target_row, mode):
        packet_names = tuple(names_to_binary[symbol] for symbol in word)
        if all(name in domain for name, domain in zip(packet_names, domains, strict=True)):
            row = prefix + "".join(PHASE_ALPHABET[symbol] for symbol in word) + suffix
            masks.add(row_mask(row))
    return tuple(sorted(masks))


def row_domains(radius: int, mode: str):
    source = load_pattern(SOURCE)
    affine = tuple(residue_two_affine_pattern(N))
    schedule = fixed_affine_schedule(source, radius)
    domains = []
    for edge in schedule.transitions:
        if edge.target_row in FIXED_ROWS:
            masks = (row_mask(affine[edge.target_row]),)
        else:
            masks = phase_masks_for_edge(
                source[edge.source_row], edge.target_row, edge.seam, radius, mode
            )
        if not masks:
            raise ValueError(f"row {edge.target_row} has an empty intersected domain")
        domains.append(masks)
    return source, affine, schedule, tuple(domains)


def cost_bounds(domains: tuple[tuple[int, ...], ...]):
    minimum = [min(mask.bit_count() for mask in domain) for domain in domains]
    prefix = [0]
    for value in minimum:
        prefix.append(prefix[-1] + value)
    suffix = [0] * (len(domains) + 1)
    for row in range(len(domains) - 1, -1, -1):
        suffix[row] = suffix[row + 1] + minimum[row]
    return prefix, suffix


def expand_side(
    side: str,
    cut: int,
    domains: tuple[tuple[int, ...], ...],
    limit: int,
    prefix_min: list[int],
    suffix_min: list[int],
    report: bool,
):
    layer = [Node(initial_state(N), None, None)]
    rows = range(cut) if side == "top" else range(N - 1, cut - 1, -1)
    stats = []
    for row in rows:
        incoming = len(layer)
        children: dict[FrontierState, Node] = {}
        attempted = live = cost_prunes = rank_prunes = 0
        other_minimum = suffix_min[row + 1] if side == "top" else prefix_min[row]
        for node in layer:
            if node.state.u_cost + other_minimum > limit:
                cost_prunes += 1
                continue
            for mask in domains[row]:
                attempted += 1
                if node.state.u_cost + mask.bit_count() + other_minimum > limit:
                    cost_prunes += 1
                    continue
                outgoing = advance_row(node.state, mask)
                if outgoing is None:
                    continue
                live += 1
                if _rank_deficit_impossible(outgoing, limit):
                    rank_prunes += 1
                    continue
                children.setdefault(outgoing, Node(outgoing, node, mask))
        layer = list(children.values())
        item = LayerStats(
            side,
            row,
            incoming,
            len(domains[row]),
            attempted,
            live,
            len(layer),
            cost_prunes,
            rank_prunes,
        )
        stats.append(item)
        if report:
            print(json.dumps(asdict(item), sort_keys=True), flush=True)
        if not layer:
            break
    return layer, tuple(stats)


def path_masks(node: Node, reverse: bool = False) -> list[int]:
    masks = []
    while node.parent is not None:
        assert node.mask is not None
        masks.append(node.mask)
        node = node.parent
    if not reverse:
        masks.reverse()
    return masks


def joined_rows(top_node: Node, bottom_node: Node) -> list[str]:
    masks = (*path_masks(top_node), *path_masks(bottom_node, reverse=True))
    return [render_mask(mask, N) for mask in masks]


def dual_diagnostics(rows: list[str]) -> dict:
    """Describe components, a deterministic cycle basis, and absent cut edges."""
    faces = ["OUT", *((row, col) for row in range(N - 1) for col in range(N - 1))]
    dsu = DSU(faces)
    edges = []

    def horizontal(row: int, col: int):
        if row == 0:
            return "OUT", (0, col)
        if row == N - 1:
            return "OUT", (N - 2, col)
        return (row - 1, col), (row, col)

    def vertical(row: int, col: int):
        if col == 0:
            return "OUT", (row, 0)
        if col == N - 1:
            return "OUT", (row, N - 2)
        return (row, col - 1), (row, col)

    for row in range(N):
        for col in range(N - 1):
            endpoints = horizontal(row, col)
            cells = ((row, col), (row, col + 1))
            edges.append((endpoints, cells, rows[row][col] == rows[row][col + 1] == "U"))
    for row in range(N - 1):
        for col in range(N):
            endpoints = vertical(row, col)
            cells = ((row, col), (row + 1, col))
            edges.append((endpoints, cells, rows[row][col] == rows[row + 1][col] == "U"))

    redundant = []
    present = []
    for endpoints, cells, selected in edges:
        if not selected:
            continue
        present.append((endpoints, cells))
        if not dsu.union(*endpoints):
            redundant.append({"dual_endpoints": list(endpoints), "primal_cells": list(cells)})

    roots = {face: dsu.find(face) for face in faces}
    ordered_roots = []
    for face in faces:
        if roots[face] not in ordered_roots:
            ordered_roots.append(roots[face])
    labels = {root: label for label, root in enumerate(ordered_roots)}
    components = []
    for root in ordered_roots:
        members = [face for face in faces if roots[face] == root]
        edge_count = sum(roots[a] == root and roots[b] == root for (a, b), _ in present)
        components.append(
            {
                "label": labels[root],
                "contains_out": "OUT" in members,
                "vertices": len(members),
                "edges": edge_count,
                "cycle_excess": edge_count - len(members) + 1,
                "sample_faces": members[:12],
            }
        )

    missing = []
    for endpoints, cells, selected in edges:
        if selected or roots[endpoints[0]] == roots[endpoints[1]]:
            continue
        needed = [list(cell) for cell in cells if rows[cell[0]][cell[1]] != "U"]
        missing.append(
            {
                "component_pair": sorted(labels[roots[endpoint]] for endpoint in endpoints),
                "dual_endpoints": list(endpoints),
                "primal_cells": list(cells),
                "needed_u_cells": needed,
                "additions": len(needed),
            }
        )
    missing.sort(key=lambda item: (item["additions"], item["component_pair"], item["primal_cells"]))
    forest_ok, forest_reason = forest_completion_check(rows)
    return {
        "u_count": sum(row.count("U") for row in rows),
        "dual_edges": len(present),
        "components": components,
        "component_count": len(components),
        "cycle_excess": len(present) - len(faces) + len(components),
        "deterministic_redundant_edges": redundant,
        "missing_cut_edges": missing,
        "forest_ok": forest_ok,
        "forest_reason": forest_reason,
    }


def join(top: list[Node], bottom: list[Node], budget: int):
    by_cost: dict[int, list[Node]] = defaultdict(list)
    for node in bottom:
        by_cost[node.state.u_cost].append(node)
    tested = connected = cache_hits = evaluations = 0
    cache = {}
    witness = None
    best_profile = None
    best_examples = []
    best_hashes = set()
    for top_node in top:
        for bottom_node in by_cost[budget - top_node.state.u_cost]:
            tested += 1
            key = (
                top_node.state.partition,
                bottom_node.state.partition,
                top_node.state.previous_u_mask & bottom_node.state.previous_u_mask,
            )
            if key in cache:
                profile = cache[key]
                cache_hits += 1
            else:
                profile = merge_frontier_profile(top_node.state, bottom_node.state)
                cache[key] = profile
                evaluations += 1
            if best_profile is None or profile < best_profile:
                best_profile = profile
                best_examples = []
                best_hashes = set()
            if profile == best_profile and len(best_examples) < 8:
                rows = joined_rows(top_node, bottom_node)
                digest = hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()
                if digest not in best_hashes:
                    best_hashes.add(digest)
                    best_examples.append(
                        {"sha256": digest, "rows": rows, "dual": dual_diagnostics(rows)}
                    )
            if profile[0] != 1:
                continue
            connected += 1
            if witness is None:
                rows = joined_rows(top_node, bottom_node)
                dual_ok, dual_connected, dual_total = dual_connectivity_check(rows)
                forest_ok, forest_reason = forest_completion_check(rows)
                if not dual_ok or not forest_ok or sum(row.count("U") for row in rows) != budget:
                    raise AssertionError("joined witness failed independent validation")
                witness = rows
                validation = {
                    "u_count": budget,
                    "dual_connected": dual_connected,
                    "dual_total": dual_total,
                    "forest_ok": forest_ok,
                    "forest_reason": forest_reason,
                }
    return {
        "conclusion": "SAT" if witness is not None else "UNSAT_IN_LANGUAGE",
        "tested_state_pairs": tested,
        "connected_state_pairs": connected,
        "cache_hits": cache_hits,
        "merge_evaluations": evaluations,
        "best_profile": list(best_profile) if best_profile is not None else None,
        "best_examples": best_examples,
        "witness": witness,
        "validation": validation if witness is not None else None,
    }


def run(radius: int, mode: str, cut: int, output: Path, report: bool) -> dict:
    started = time.monotonic()
    source, affine, schedule, domains = row_domains(radius, mode)
    prefix_min, suffix_min = cost_bounds(domains)
    top, top_stats = expand_side(
        "top", cut, domains, 335, prefix_min, suffix_min, report
    )
    bottom, bottom_stats = expand_side(
        "bottom", cut, domains, 335, prefix_min, suffix_min, report
    )
    results = {str(budget): join(top, bottom, budget) for budget in (335, 333)}
    record = {
        "schema": "grid-graphs.residue-two-b-state-phase-pump.v1",
        "exact_in_declared_language": True,
        "source": {
            "path": SOURCE.name,
            "u_count": sum(row.count("U") for row in source),
            "sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        },
        "target_n": N,
        "radius": radius,
        "mode": mode,
        "cut": cut,
        "fixed_rows": list(FIXED_ROWS),
        "targeted_s_sites": (
            {str(row): list(sites) for row, sites in TARGETED_S_SITES.items()}
            if mode == "targeted"
            else None
        ),
        "maximum_s_packets_per_row": 1 if mode == "targeted" else None,
        "schedule": [
            {
                "target_row": edge.target_row,
                "operation": edge.operation,
                "source_row": edge.source_row,
                "seam": edge.seam,
            }
            for edge in schedule.transitions
        ],
        "row_domain_sizes": [len(domain) for domain in domains],
        "affine_335_in_every_row_domain": all(
            row_mask(row) in domain for row, domain in zip(affine, domains, strict=True)
        ),
        "top_states": len(top),
        "bottom_states": len(bottom),
        "top_stats": [asdict(item) for item in top_stats],
        "bottom_stats": [asdict(item) for item in bottom_stats],
        "budgets": results,
        "elapsed_seconds": time.monotonic() - started,
        "scope_note": (
            "Exact only for the fixed radius-three B20-to-affine23 schedule, affine "
            "depth-six caps, and bounded phase-front row language."
        ),
    }
    write_result(output, record)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radius", type=int, default=3)
    parser.add_argument(
        "--mode", choices=("basic", "targeted", "phase"), default="phase"
    )
    parser.add_argument("--cut", type=int, default=11)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()
    record = run(args.radius, args.mode, args.cut, args.output, not args.quiet)
    print(
        {
            "output": str(args.output),
            "top_states": record["top_states"],
            "bottom_states": record["bottom_states"],
            "335": record["budgets"]["335"]["conclusion"],
            "333": record["budgets"]["333"]["conclusion"],
            "elapsed_seconds": record["elapsed_seconds"],
        }
    )


if __name__ == "__main__":
    main()
