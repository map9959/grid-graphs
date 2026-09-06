#!/usr/bin/env python3
"""Cap-aware bidirectional search of the n=20 full-middle packet grammar."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    q_old_formula as q_formula,
)
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.tiles.tile_grammar import (
    ROW_PACKET_ALPHABET,
    FrontierState,
    advance_row,
    initial_state,
    merge_frontier_profile,
    render_mask,
    row_mask,
    stream_row_packets,
)


BASIC_ALPHABET = ROW_PACKET_ALPHABET
PHASE_ALPHABET = {
    **ROW_PACKET_ALPHABET,
    "S": ".U.",
}
BALANCED_ALPHABET = {
    **ROW_PACKET_ALPHABET,
    "A": "U..",
    "S": ".U.",
    "B": "..U",
}

KNOWN_250 = [
    ".U..................",
    ".UUUUUUUUUUUUUUUUUUU",
    ".UUUU.UU.UU.UU.UU.UU",
    ".UU.U.UU.UU.UU.UUUU.",
    ".UUUU.UU.UU.UUUU.UU.",
    ".U.UU.UU.UUUU.UU.UU.",
    ".UUUU.UUUU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.U.U.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UUUUUU.UU.UU.UU.UU.",
    ".U.U.UU.UU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.UU.",
    ".U.UUUU.UU.UU.UU.UU.",
    ".UUUU.U.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UUUUUUUUUUUUUUUUUU.",
    ".U................U.",
]

# Unique deterministic n=20, target-249, basic-alphabet beam-100 join at split
# 8. This is a near candidate, not a valid witness.
KNOWN_249_NEAR = [
    ".U..................",
    ".UUUUUUUUUUUUUUUUUUU",
    ".UUUU.UU.UU.UU.UU.UU",
    ".UU.U.UU.UU.UU.UUUU.",
    ".UUUU.UU.UU.UUUU.UU.",
    ".U.UU.UU.UUUU.UU.UU.",
    ".UUUU.UUUU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.U.U.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.U.U.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UU.UUU.UU.UU.UU.UU.",
    ".UUUU.U.UU.UU.UU.UU.",
    ".U.UUUU.UU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.UU.",
    ".UUUUUUUUUUUUUUUUUU.",
    ".U................U.",
]


@dataclass(frozen=True, slots=True)
class Node:
    state: FrontierState
    charge: int
    defects: int
    masks: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class JoinedCandidate:
    top: Node
    bottom: Node
    profile: tuple[int, int]
    rows: tuple[str, ...]


def state_key(node: Node) -> tuple[int, tuple[int, ...], int]:
    return node.state.previous_u_mask, node.state.partition, node.charge


def topology_metric(node: Node) -> tuple[int, int, int, int, int]:
    state = node.state
    out = state.partition[0]
    components = len(set(state.partition))
    out_size = sum(label == out for label in state.partition)
    return (
        node.defects,
        components,
        len(state.partition) - out_size,
        state.cycle_excess,
        state.previous_u_mask,
    )


def join_metric(
    node: Node,
    targets: list[Node],
    target_charge: int,
    target_u: int,
    max_defects: int | None,
) -> tuple:
    compatible = [
        target
        for target in targets
        if node.charge + target.charge == target_charge
        and node.state.u_cost + target.state.u_cost == target_u
        and (max_defects is None or node.defects + target.defects <= max_defects)
    ]
    profiles = [merge_frontier_profile(node.state, target.state) for target in compatible]
    return min(profiles, default=(node.state.n + 1, node.state.n + 1))


def select_diverse(
    nodes: list[Node],
    width: int,
    desired_charge: float,
    join_targets: list[Node] | None = None,
    target_charge: int = 0,
    target_u: int = 0,
    max_defects: int | None = None,
) -> list[Node]:
    if len(nodes) <= width:
        return nodes
    buckets = defaultdict(list)
    for node in nodes:
        buckets[(node.charge, node.defects)].append(node)
    for bucket in buckets.values():
        bucket.sort(
            key=lambda node: (
                join_metric(node, join_targets, target_charge, target_u, max_defects)
                if join_targets is not None
                else (),
                topology_metric(node),
            )
        )
    selected = []
    keys = sorted(
        buckets,
        key=lambda key: (abs(key[0] - desired_charge), key[1], key[0]),
    )
    while len(selected) < width:
        changed = False
        for key in keys:
            if buckets[key]:
                selected.append(buckets[key].pop(0))
                changed = True
                if len(selected) == width:
                    break
        if not changed:
            break
    return selected


def cap_state(n: int, rows: list[str]) -> Node:
    state = initial_state(n)
    masks = []
    for row in rows:
        mask = row_mask(row)
        state = advance_row(state, mask)
        if state is None:
            raise AssertionError("fixed cap sealed a dual component")
        masks.append(mask)
    return Node(state, 0, 0, tuple(masks))


def _face_json(face: str | tuple[int, int]) -> str | list[int]:
    return face if isinstance(face, str) else list(face)


def _graph_diagnostics(rows: list[str]) -> tuple[dict[str, Any], dict[Any, int]]:
    """Return explicit dual edges and deterministically ordered components."""
    n = len(rows)
    faces: list[Any] = ["OUT", *((r, c) for r in range(n - 1) for c in range(n - 1))]
    parent = {face: face for face in faces}

    def root(item: Any) -> Any:
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def union(a: Any, b: Any) -> None:
        a, b = root(a), root(b)
        if a != b:
            parent[b] = a

    edges: list[dict[str, Any]] = []
    for r in range(n):
        for c in range(n - 1):
            if rows[r][c : c + 2] != "UU":
                continue
            a = "OUT" if r == 0 else (r - 1, c)
            b = "OUT" if r == n - 1 else (r, c)
            edges.append({"orientation": "H", "primal": [r, c], "faces": [_face_json(a), _face_json(b)]})
            union(a, b)
    for r in range(n - 1):
        for c in range(n):
            if rows[r][c] != "U" or rows[r + 1][c] != "U":
                continue
            a = "OUT" if c == 0 else (r, c - 1)
            b = "OUT" if c == n - 1 else (r, c)
            edges.append({"orientation": "V", "primal": [r, c], "faces": [_face_json(a), _face_json(b)]})
            union(a, b)

    groups: dict[Any, list[Any]] = defaultdict(list)
    for face in faces:
        groups[root(face)].append(face)
    ordered = sorted(
        groups.values(),
        key=lambda group: ("OUT" not in group, min((face for face in group if face != "OUT"), default=(-1, -1))),
    )
    component_of: dict[Any, int] = {}
    components = []
    for index, group in enumerate(ordered):
        coordinates = sorted(face for face in group if face != "OUT")
        for face in group:
            component_of[face] = index
        bbox = None
        if coordinates:
            bbox = {
                "row_min": min(r for r, _ in coordinates),
                "row_max": max(r for r, _ in coordinates),
                "col_min": min(c for _, c in coordinates),
                "col_max": max(c for _, c in coordinates),
            }
        components.append(
            {
                "id": index,
                "contains_out": "OUT" in group,
                "size": len(group),
                "face_coordinates": [list(face) for face in coordinates],
                "bounding_box": bbox,
            }
        )
    vertices = len(faces)
    connected_to_out = next(len(group) for group in ordered if "OUT" in group)
    return (
        {
            "ok": len(components) == 1,
            "vertex_count": vertices,
            "edge_count": len(edges),
            "connected_to_out": connected_to_out,
            "component_count": len(components),
            "cycle_excess": len(edges) - vertices + len(components),
            "components": components,
            "edges": edges,
        },
        component_of,
    )


def _forest_diagnostics(rows: list[str]) -> dict[str, Any]:
    """Describe every forced/optional primal edge and the greedy completion."""
    n = len(rows)
    parent = list(range(n * n))

    def root(item: int) -> int:
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def union(a: int, b: int) -> bool:
        a, b = root(a), root(b)
        if a == b:
            return False
        parent[b] = a
        return True

    forced: list[list[list[int]]] = []
    optional: list[list[list[int]]] = []
    for r in range(n):
        for c in range(n):
            for rr, cc in ((r, c + 1), (r + 1, c)):
                if rr >= n or cc >= n:
                    continue
                edge = [[r, c], [rr, cc]]
                if rows[r][c] == rows[rr][cc] == "U":
                    optional.append(edge)
                else:
                    forced.append(edge)
    forced_cycles = []
    accepted_forced = []
    for edge in forced:
        (r, c), (rr, cc) = edge
        if union(r * n + c, rr * n + cc):
            accepted_forced.append(edge)
        else:
            forced_cycles.append(edge)
    forced_component_count = len({root(vertex) for vertex in range(n * n)})
    completion_edges = []
    for edge in optional:
        (r, c), (rr, cc) = edge
        if union(r * n + c, rr * n + cc):
            completion_edges.append(edge)
    completion_component_count = len({root(vertex) for vertex in range(n * n)})
    ok, reason = forest_completion_check(rows)
    return {
        "ok": ok,
        "reason": reason,
        "vertex_count": n * n,
        "forced_edge_count": len(forced),
        "optional_u_u_edge_count": len(optional),
        "forced_component_count": forced_component_count,
        "forced_cycle_edge_count": len(forced_cycles),
        "forced_edges": forced,
        "forced_cycle_edges": forced_cycles,
        "accepted_forced_edges": accepted_forced,
        "greedy_completion_edges": completion_edges,
        "greedy_completion_edge_count": len(accepted_forced) + len(completion_edges),
        "greedy_completion_component_count": completion_component_count,
    }


def candidate_diagnostic(
    candidate: JoinedCandidate,
    parameters: dict[str, Any],
    tied_best_count: int,
) -> dict[str, Any]:
    rows = list(candidate.rows)
    n = len(rows)
    dual, component_of = _graph_diagnostics(rows)
    if (dual["component_count"], dual["cycle_excess"]) != candidate.profile:
        raise AssertionError("reconstructed rows disagree with the retained join profile")
    cut_row = len(candidate.top.masks) - 1
    deficits = []
    for c in range(n):
        left: Any = "OUT" if c == 0 else (cut_row, c - 1)
        right: Any = "OUT" if c + 1 == n else (cut_row, c)
        top_u = rows[cut_row][c] == "U"
        bottom_u = rows[cut_row + 1][c] == "U"
        if component_of[left] != component_of[right] and not (top_u and bottom_u):
            deficits.append(
                {
                    "column": c,
                    "faces": [_face_json(left), _face_json(right)],
                    "component_ids": [component_of[left], component_of[right]],
                    "top_u": top_u,
                    "bottom_u": bottom_u,
                    "missing_endpoints": [
                        endpoint
                        for endpoint, present in (("top", top_u), ("bottom", bottom_u))
                        if not present
                    ],
                }
            )
    source = Path(__file__)
    return {
        "format": "search_residue_two_middle.best-join.v1",
        "parameters": parameters,
        "source": {"path": source.name, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()},
        "tied_best_count": tied_best_count,
        "join": {
            "profile": {"components": candidate.profile[0], "cycle_excess": candidate.profile[1]},
            "charge": {
                "top": candidate.top.charge,
                "bottom": candidate.bottom.charge,
                "total": candidate.top.charge + candidate.bottom.charge,
            },
            "cost": {
                "top": candidate.top.state.u_cost,
                "bottom": candidate.bottom.state.u_cost,
                "total": candidate.top.state.u_cost + candidate.bottom.state.u_cost,
            },
            "cycles": {
                "top": candidate.top.state.cycle_excess,
                "bottom": candidate.bottom.state.cycle_excess,
                "crossing": candidate.profile[1]
                - candidate.top.state.cycle_excess
                - candidate.bottom.state.cycle_excess,
                "total": candidate.profile[1],
            },
            "defects": {
                "top": candidate.top.defects,
                "bottom": candidate.bottom.defects,
                "total": candidate.top.defects + candidate.bottom.defects,
            },
            "masks": {
                "top": list(candidate.top.masks),
                "bottom_reflected": list(candidate.bottom.masks),
                "reconstructed": [row_mask(row) for row in rows],
            },
            "partitions": {
                "top": list(candidate.top.state.partition),
                "bottom_reflected": list(candidate.bottom.state.partition),
            },
            "cut": {"between_rows": [cut_row, cut_row + 1], "endpoint_deficits": deficits},
        },
        "u_u_edge_count": dual["edge_count"],
        "rows": rows,
        "dual": dual,
        "forest": _forest_diagnostics(rows),
    }


def expand_side(
    seed: Node,
    rows: int,
    other_rows: int,
    beam: int,
    target_charge: int,
    target_u: int,
    total_mutable_rows: int,
    packets: int,
    alphabet: dict[str, str],
    max_defects: int | None,
    label: str,
    report: bool,
    join_targets: list[Node] | None = None,
) -> list[Node]:
    layer = [seed]
    packet_charges = [packet.count("U") - 2 for packet in alphabet.values()]
    minimum_packet_charge = min(packet_charges)
    maximum_packet_charge = max(packet_charges)
    side_min = max(
        minimum_packet_charge * packets * rows,
        target_charge - maximum_packet_charge * packets * other_rows,
    )
    side_max = min(
        maximum_packet_charge * packets * rows,
        target_charge - minimum_packet_charge * packets * other_rows,
    )
    packet_domains = [tuple(alphabet)] * packets
    for index in range(rows):
        remaining = rows - index - 1
        candidates: dict[tuple[int, tuple[int, ...], int], Node] = {}
        attempted = 0
        for node in layer:
            remaining_min = minimum_packet_charge * packets * remaining
            remaining_max = maximum_packet_charge * packets * remaining
            minimum_add = max(
                minimum_packet_charge * packets,
                side_min - node.charge - remaining_max,
            )
            maximum_add = min(
                maximum_packet_charge * packets,
                side_max - node.charge - remaining_min,
            )
            if minimum_add > maximum_add:
                continue
            transitions, count = stream_row_packets(
                node.state,
                ".",
                ".",
                packet_domains,
                packet_alphabet=alphabet,
                packet_charge_bounds=(minimum_add, maximum_add),
            )
            attempted += count
            for transition in transitions:
                charge = node.charge + transition.packet_charge
                defects = node.defects + sum(
                    alphabet[name].count("U") == 1 for name in transition.packet_names
                )
                if max_defects is not None and defects > max_defects:
                    continue
                candidate = Node(
                    transition.outgoing,
                    charge,
                    defects,
                    (*node.masks, transition.row_mask),
                )
                key = state_key(candidate)
                old = candidates.get(key)
                if old is None or (
                    candidate.defects,
                    candidate.state.cycle_excess,
                ) < (old.defects, old.state.cycle_excess):
                    candidates[key] = candidate
        is_join_layer = join_targets is not None and index + 1 == rows
        if is_join_layer:
            compatible_charges = {target_charge - node.charge for node in join_targets}
            candidates = {
                key: node
                for key, node in candidates.items()
                if node.charge in compatible_charges
                and any(
                    node.charge + target.charge == target_charge
                    and node.state.u_cost + target.state.u_cost == target_u
                    and (
                        max_defects is None
                        or node.defects + target.defects <= max_defects
                    )
                    for target in join_targets
                )
            }
        desired_charge = target_charge * (index + 1) / total_mutable_rows
        layer = select_diverse(
            list(candidates.values()),
            beam,
            desired_charge,
            join_targets if is_join_layer else None,
            target_charge,
            target_u,
            max_defects,
        )
        if report:
            signatures = sorted({(node.charge, node.defects) for node in layer})
            print(
                f"{label}_row={index + 1}/{rows} packet_extensions={attempted} "
                f"successors={len(candidates)} retained={len(layer)} "
                f"charge_defects={signatures}",
                flush=True,
            )
        if not layer:
            break
    return layer


def search(
    n: int,
    target_u: int,
    beam: int,
    split: int,
    report: bool,
    alphabet: dict[str, str],
    max_defects: int | None,
    save_best: Path | None = None,
    alphabet_name: str = "custom",
) -> list[str] | None:
    affine = residue_two_affine_pattern(n)
    fixed_top = affine[:3]
    fixed_bottom = affine[-2:]
    mutable_rows = n - len(fixed_top) - len(fixed_bottom)
    backward_rows = mutable_rows - split
    packets = (n - 2) // 3
    fixed_u = sum(row.count("U") for row in (*fixed_top, *fixed_bottom))
    baseline_u = fixed_u + mutable_rows * packets * 2
    target_charge = target_u - baseline_u
    if target_u not in (q_formula(n), q_formula(n) + 1):
        raise ValueError("target must be q(n) or q(n)+1")
    packet_charges = [packet.count("U") - 2 for packet in alphabet.values()]
    if not (
        min(packet_charges) * mutable_rows * packets
        <= target_charge
        <= max(packet_charges) * mutable_rows * packets
    ):
        raise ValueError("target is outside the packet language's attainable count range")

    backward_seed = cap_state(n, list(reversed(fixed_bottom)))
    backward = expand_side(
        backward_seed,
        backward_rows,
        split,
        beam,
        target_charge,
        target_u,
        mutable_rows,
        packets,
        alphabet,
        max_defects,
        "backward",
        report,
    )
    forward_seed = cap_state(n, fixed_top)
    forward = expand_side(
        forward_seed,
        split,
        backward_rows,
        beam,
        target_charge,
        target_u,
        mutable_rows,
        packets,
        alphabet,
        max_defects,
        "forward",
        report,
        backward,
    )

    backward_by_charge = defaultdict(list)
    for node in backward:
        backward_by_charge[node.charge].append(node)
    best_candidate: JoinedCandidate | None = None
    tied_best_count = 0
    joined = 0
    for top in forward:
        for bottom in backward_by_charge[target_charge - top.charge]:
            if top.state.u_cost + bottom.state.u_cost != target_u:
                continue
            if max_defects is not None and top.defects + bottom.defects > max_defects:
                continue
            joined += 1
            profile = merge_frontier_profile(top.state, bottom.state)
            masks = (*top.masks, *reversed(bottom.masks))
            candidate = JoinedCandidate(
                top,
                bottom,
                profile,
                tuple(render_mask(mask, n) for mask in masks),
            )
            if best_candidate is None or profile < best_candidate.profile:
                best_candidate = candidate
                tied_best_count = 1
            elif profile == best_candidate.profile:
                tied_best_count += 1
                candidate_key = (
                    candidate.top.masks,
                    candidate.bottom.masks,
                    candidate.top.state.partition,
                    candidate.bottom.state.partition,
                )
                best_key = (
                    best_candidate.top.masks,
                    best_candidate.bottom.masks,
                    best_candidate.top.state.partition,
                    best_candidate.bottom.state.partition,
                )
                if candidate_key < best_key:
                    best_candidate = candidate
            if profile[0] != 1:
                continue
            rows = list(candidate.rows)
            dual_ok, connected, total = dual_connectivity_check(rows)
            forest_ok, reason = forest_completion_check(rows)
            print(
                f"candidate dual={connected}/{total} forest={forest_ok} "
                f"cycle_excess={profile[1]} reason={reason}"
            )
            if dual_ok and forest_ok:
                return rows
    if report and best_candidate is not None:
        print(
            f"joined_pairs={joined} best_join_components={best_candidate.profile[0]} "
            f"best_cycle_excess={best_candidate.profile[1]} tied_best={tied_best_count}",
            flush=True,
        )
    elif report:
        print("joined_pairs=0; no compatible retained charge/defect pair", flush=True)
    if save_best is not None:
        if best_candidate is None:
            raise RuntimeError("cannot save a best join because no compatible pair was retained")
        diagnostic = candidate_diagnostic(
            best_candidate,
            {
                "n": n,
                "target_u": target_u,
                "beam": beam,
                "split": split,
                "mutable_rows": mutable_rows,
                "alphabet": alphabet_name,
                "alphabet_packets": dict(alphabet),
                "max_defects": max_defects,
                "joined_pairs": joined,
            },
            tied_best_count,
        )
        save_best.write_text(json.dumps(diagnostic, indent=2, sort_keys=True) + "\n")
        if report:
            print(f"saved best joined-pair diagnostic to {save_best}", flush=True)
    return None


def check_known() -> None:
    n = 20
    affine = residue_two_affine_pattern(n)
    if len(KNOWN_250) != n or any(len(row) != n for row in KNOWN_250):
        raise AssertionError("known candidate is not 20x20")
    if KNOWN_250[:3] != affine[:3] or KNOWN_250[-2:] != affine[-2:]:
        raise AssertionError("known candidate caps differ from the n=20 affine caps")
    mutable = KNOWN_250[3:-2]
    if any(row[0] != "." or row[-1] != "." for row in mutable):
        raise AssertionError("known candidate has a non-dot mutable boundary")
    packets = [row[start : start + 3] for row in mutable for start in range(1, 19, 3)]
    if any(packet not in BASIC_ALPHABET.values() for packet in packets):
        raise AssertionError("known candidate is outside the basic packet language")
    charge = sum(packet.count("U") - 2 for packet in packets)
    actual_u = sum(row.count("U") for row in KNOWN_250)
    dual_ok, connected, total = dual_connectivity_check(KNOWN_250)
    forest_ok, reason = forest_completion_check(KNOWN_250)
    edges = sum(
        row[c] == row[c + 1] == "U"
        for row in KNOWN_250
        for c in range(n - 1)
    ) + sum(
        KNOWN_250[r][c] == KNOWN_250[r + 1][c] == "U"
        for r in range(n - 1)
        for c in range(n)
    )
    cycle_excess = edges - (1 + (n - 1) ** 2) + 1
    if actual_u != 250 or charge != 16 or cycle_excess != 2 or not dual_ok or not forest_ok:
        raise AssertionError(
            f"known candidate failed: U={actual_u} charge={charge} cycles={cycle_excess} "
            f"dual={connected}/{total} forest={forest_ok} reason={reason}"
        )
    print(
        f"known target-250 candidate: U={actual_u} charge={charge} "
        f"dual={connected}/{total} cycles={cycle_excess} forest={reason}"
    )


def check_near() -> None:
    """Check the recorded bounded-search near candidate without blessing it."""
    n = 20
    affine = residue_two_affine_pattern(n)
    if len(KNOWN_249_NEAR) != n or any(len(row) != n for row in KNOWN_249_NEAR):
        raise AssertionError("known near candidate is not 20x20")
    if KNOWN_249_NEAR[:3] != affine[:3] or KNOWN_249_NEAR[-2:] != affine[-2:]:
        raise AssertionError("known near candidate caps differ from the n=20 affine caps")
    mutable = KNOWN_249_NEAR[3:-2]
    if any(row[0] != "." or row[-1] != "." for row in mutable):
        raise AssertionError("known near candidate has a non-dot mutable boundary")
    packets = [row[start : start + 3] for row in mutable for start in range(1, 19, 3)]
    if any(packet not in BASIC_ALPHABET.values() for packet in packets):
        raise AssertionError("known near candidate is outside the basic packet language")

    actual_u = sum(row.count("U") for row in KNOWN_249_NEAR)
    dual_ok, connected, total = dual_connectivity_check(KNOWN_249_NEAR)
    forest_ok, reason = forest_completion_check(KNOWN_249_NEAR)
    dual, _ = _graph_diagnostics(KNOWN_249_NEAR)
    sizes = sorted(component["size"] for component in dual["components"])
    detached = next(component for component in dual["components"] if not component["contains_out"])
    expected_faces = [[r, c] for r in range(9, 12) for c in range(3, 7)]
    if (
        actual_u != 249
        or dual_ok
        or (connected, total) != (350, 362)
        or sizes != [12, 350]
        or detached["face_coordinates"] != expected_faces
        or detached["bounding_box"]
        != {"row_min": 9, "row_max": 11, "col_min": 3, "col_max": 6}
        or forest_ok
    ):
        raise AssertionError(
            f"known near candidate failed: U={actual_u} dual={connected}/{total} "
            f"components={sizes} detached_box={detached['bounding_box']} "
            f"forest={forest_ok} reason={reason}"
        )
    print(
        f"known target-249 near candidate: U={actual_u} dual={connected}/{total} "
        f"components={sizes} detached_faces=rows9..11,cols3..6 forest={reason}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=20)
    parser.add_argument("--surplus", type=int, choices=(0, 1), default=1)
    parser.add_argument("--beam", type=int, default=50)
    parser.add_argument("--split", type=int, help="mutable rows expanded from top")
    parser.add_argument("--report", action="store_true")
    parser.add_argument(
        "--alphabet", choices=("basic", "phase", "balanced"), default="basic"
    )
    parser.add_argument("--check-known", action="store_true")
    parser.add_argument("--check-near", action="store_true")
    parser.add_argument(
        "--save-best",
        type=Path,
        metavar="PATH",
        help="write the best failed joined pair and full diagnostics as JSON",
    )
    parser.add_argument(
        "--max-defects",
        type=int,
        help="maximum one-U packets across all mutable rows",
    )
    args = parser.parse_args()
    if args.check_known and args.check_near:
        parser.error("choose only one known-candidate check")
    if args.check_known:
        check_known()
        return
    if args.check_near:
        check_near()
        return
    if args.beam < 1:
        parser.error("--beam must be positive")
    if args.max_defects is not None and args.max_defects < 0:
        parser.error("--max-defects must be nonnegative")
    if args.n < 17 or args.n % 3 != 2:
        parser.error("--n must be at least 17 and congruent to 2 mod 3")
    mutable_rows = args.n - 5
    split = (mutable_rows + 1) // 2 if args.split is None else args.split
    if not 1 <= split < mutable_rows:
        parser.error(f"--split must lie in 1..{mutable_rows - 1}")
    target = q_formula(args.n) + args.surplus
    alphabet = {
        "basic": BASIC_ALPHABET,
        "phase": PHASE_ALPHABET,
        "balanced": BALANCED_ALPHABET,
    }[args.alphabet]
    rows = search(
        args.n,
        target,
        args.beam,
        split,
        args.report,
        alphabet,
        args.max_defects,
        args.save_best,
        args.alphabet,
    )
    if rows is None:
        print(
            f"no n={args.n} target-{target} candidate retained by bidirectional beam "
            f"{args.beam} at split {split}/{mutable_rows} alphabet={args.alphabet} "
            "(not exhaustive)"
        )
        raise SystemExit(1)
    print("\n".join(rows))


if __name__ == "__main__":
    main()
