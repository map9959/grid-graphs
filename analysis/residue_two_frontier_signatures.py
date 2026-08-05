#!/usr/bin/env python3
"""Extract exact per-component frontier traces for known residue-two controls."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from analyze_residue_constructions import analyze
from census_moving_seam_alignment import (
    PHASE_FRONT_WITNESS,
    d4_orientations,
    find_alignment,
    load_square_pattern,
    replay_alignment,
)
from construction_lab import q_formula
from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from open_slab_signature import extract_open_slab_signature
from tile_grammar import FrontierState, advance_row, initial_state, render_mask, row_mask


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DEFAULT_OUTPUT = HERE / "residue_two_frontier_traces.json"
SCHEMA = "grid-graphs.residue-two-frontier-traces.v1"


@dataclass(frozen=True, slots=True)
class ComponentPayload:
    vertices: int
    edges: int

    @property
    def cycle_rank(self) -> int:
        return self.edges - self.vertices + 1


@dataclass(frozen=True, slots=True)
class RankedFrontierState:
    n: int
    row_index: int
    previous_u_mask: int
    partition: tuple[int, ...]
    u_cost: int
    components: tuple[ComponentPayload, ...]

    @property
    def cycle_excess(self) -> int:
        return sum(component.cycle_rank for component in self.components)

    @property
    def introduced_vertices(self) -> int:
        return sum(component.vertices for component in self.components)

    @property
    def edge_count(self) -> int:
        return sum(component.edges for component in self.components)


class _Dsu:
    def __init__(self, size: int):
        self.parent = list(range(size))

    def root(self, node: int) -> int:
        while self.parent[node] != node:
            self.parent[node] = self.parent[self.parent[node]]
            node = self.parent[node]
        return node

    def union(self, left: int, right: int) -> tuple[bool, int, int]:
        left = self.root(left)
        right = self.root(right)
        if left == right:
            return False, left, right
        self.parent[right] = left
        return True, left, right


def initial_ranked_state(n: int) -> RankedFrontierState:
    if n < 2:
        raise ValueError("frontier grammar requires n >= 2")
    return RankedFrontierState(n, 0, 0, (0,), 0, (ComponentPayload(1, 0),))


def ranked_advance_row(
    state: RankedFrontierState, current_u_mask: int
) -> RankedFrontierState | None:
    """Advance an exact frontier while retaining edge/vertex payload per component."""
    n = state.n
    if state.row_index == n:
        raise ValueError("cannot advance a finished frontier")
    if current_u_mask < 0 or current_u_mask >= 1 << n:
        raise ValueError("row mask does not fit the grid width")
    if len(state.components) != len(set(state.partition)):
        raise ValueError("component payload count does not match the partition")

    row = state.row_index
    has_old = row > 0
    has_new = row + 1 < n
    old_start = 1
    new_start = old_start + (n - 1 if has_old else 0)
    node_count = 1 + (n - 1 if has_old else 0) + (n - 1 if has_new else 0)
    dsu = _Dsu(node_count)

    if has_old:
        if len(state.partition) != n:
            raise ValueError("frontier partition has the wrong size")
        representatives: dict[int, int] = {}
        for node, label in enumerate(state.partition):
            if label in representatives:
                dsu.union(node, representatives[label])
            else:
                representatives[label] = node
    elif state.partition != (0,):
        raise ValueError("initial frontier partition must contain only OUT")

    payloads: dict[int, ComponentPayload] = {}
    if has_old:
        for label, component in enumerate(state.components):
            representative = next(
                node for node, observed in enumerate(state.partition) if observed == label
            )
            payloads[dsu.root(representative)] = component
    else:
        payloads[0] = state.components[0]
    if has_new:
        for node in range(new_start, new_start + n - 1):
            payloads[node] = ComponentPayload(1, 0)

    def add_edge(left: int, right: int) -> None:
        left_root = dsu.root(left)
        right_root = dsu.root(right)
        if left_root == right_root:
            payload = payloads[left_root]
            payloads[left_root] = ComponentPayload(payload.vertices, payload.edges + 1)
            return
        left_payload = payloads.pop(left_root)
        right_payload = payloads.pop(right_root)
        merged, root, retired = dsu.union(left_root, right_root)
        assert merged and root == left_root and retired == right_root
        payloads[root] = ComponentPayload(
            left_payload.vertices + right_payload.vertices,
            left_payload.edges + right_payload.edges + 1,
        )

    if has_old:
        both_u = state.previous_u_mask & current_u_mask
        for column in range(n):
            if not both_u & (1 << column):
                continue
            left = 0 if column == 0 else old_start + column - 1
            right = 0 if column + 1 == n else old_start + column
            add_edge(left, right)

    adjacent_u = current_u_mask & (current_u_mask >> 1)
    for column in range(n - 1):
        if not adjacent_u & (1 << column):
            continue
        above = old_start + column if has_old else 0
        below = new_start + column if has_new else 0
        add_edge(above, below)

    retained_nodes = [0]
    if has_new:
        retained_nodes.extend(range(new_start, new_start + n - 1))
    retained_roots = {dsu.root(node) for node in retained_nodes}
    if has_old and any(
        dsu.root(node) not in retained_roots
        for node in range(old_start, old_start + n - 1)
    ):
        return None

    labels: dict[int, int] = {}
    partition = tuple(
        labels.setdefault(dsu.root(node), len(labels)) for node in retained_nodes
    )
    if not has_new and partition != (0,):
        return None
    components = tuple(
        payloads[root]
        for root, _ in sorted(labels.items(), key=lambda item: item[1])
    )
    outgoing = RankedFrontierState(
        n=n,
        row_index=row + 1,
        previous_u_mask=current_u_mask,
        partition=partition,
        u_cost=state.u_cost + current_u_mask.bit_count(),
        components=components,
    )
    if outgoing.introduced_vertices != 1 + min(row + 1, n - 1) * (n - 1):
        raise AssertionError("ranked frontier introduced-vertex count is inconsistent")
    return outgoing


def ordinary_state(state: RankedFrontierState) -> FrontierState:
    return FrontierState(
        n=state.n,
        row_index=state.row_index,
        previous_u_mask=state.previous_u_mask,
        partition=state.partition,
        u_cost=state.u_cost,
        cycle_excess=state.cycle_excess,
    )


def replay_rows(rows: list[str] | tuple[str, ...]) -> list[RankedFrontierState]:
    n = len(rows)
    ranked = initial_ranked_state(n)
    ordinary = initial_state(n)
    trace = [ranked]
    for row in rows:
        mask = row_mask(row)
        ranked_next = ranked_advance_row(ranked, mask)
        ordinary_next = advance_row(ordinary, mask)
        if ranked_next is None or ordinary_next is None:
            raise ValueError("pattern seals a dual component or fails final connectivity")
        if ordinary_state(ranked_next) != ordinary_next:
            raise AssertionError("ranked and ordinary frontier transitions disagree")
        ranked = ranked_next
        ordinary = ordinary_next
        trace.append(ranked)
    return trace


def _rows_sha256(rows: list[str] | tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def _component_record(
    state: RankedFrontierState, label: int, component: ComponentPayload
) -> dict:
    return {
        "label": label,
        "contains_out": state.partition[0] == label,
        "frontier_slots": [
            slot for slot, observed in enumerate(state.partition) if observed == label
        ],
        "vertices": component.vertices,
        "edges": component.edges,
        "cycle_rank": component.cycle_rank,
    }


def state_record(state: RankedFrontierState) -> dict:
    return {
        "row_index": state.row_index,
        "previous_u_mask": state.previous_u_mask,
        "previous_u_bits": render_mask(state.previous_u_mask, state.n),
        "partition": list(state.partition),
        "u_cost": state.u_cost,
        "introduced_vertices": state.introduced_vertices,
        "edge_count": state.edge_count,
        "cycle_excess": state.cycle_excess,
        "components": [
            _component_record(state, label, component)
            for label, component in enumerate(state.components)
        ],
    }


def known_witnesses() -> dict[str, tuple[str, tuple[str, ...]]]:
    return {
        "n08-explicit-exact": ("explicit-exact", tuple(residue_two_explicit_pattern(8))),
        "n11-explicit-exact": ("explicit-exact", tuple(residue_two_explicit_pattern(11))),
        "n14-explicit-exact": ("explicit-exact", tuple(residue_two_explicit_pattern(14))),
        "n17-affine-surplus-one": ("affine-surplus-one", tuple(residue_two_affine_pattern(17))),
        "n20-phase-front-surplus-one": (
            "phase-front-surplus-one",
            tuple(load_square_pattern(PHASE_FRONT_WITNESS)),
        ),
    }


def _orientation(rows: tuple[str, ...], name: str) -> tuple[str, ...]:
    return next(item.rows for item in d4_orientations(rows) if item.name == name)


def known_alignment_inputs() -> tuple[dict, ...]:
    witnesses = known_witnesses()
    return (
        {
            "id": "n08-to-n11",
            "source": witnesses["n08-explicit-exact"][1],
            "target": witnesses["n11-explicit-exact"][1],
            "source_orientation": "rotate_0",
            "target_orientation": "rotate_0",
            "radius": 1,
        },
        {
            "id": "n11-to-n14",
            "source": witnesses["n11-explicit-exact"][1],
            "target": witnesses["n14-explicit-exact"][1],
            "source_orientation": "rotate_90",
            "target_orientation": "rotate_0_reflect_lr",
            "radius": 1,
        },
        {
            "id": "n14-to-n17",
            "source": witnesses["n14-explicit-exact"][1],
            "target": witnesses["n17-affine-surplus-one"][1],
            "source_orientation": "rotate_0",
            "target_orientation": "rotate_0",
            "radius": 1,
        },
        {
            "id": "n17-to-n20",
            "source": witnesses["n17-affine-surplus-one"][1],
            "target": witnesses["n20-phase-front-surplus-one"][1],
            "source_orientation": "rotate_0",
            "target_orientation": "rotate_0",
            "radius": 3,
        },
    )


def ranked_open_signature_record(
    state: RankedFrontierState,
    slab_start: int,
    removed_u_cost: int,
) -> dict:
    ordinary_signature = extract_open_slab_signature(
        ordinary_state(state), slab_start, 3, removed_u_cost
    )
    hidden_indices = set(range(1 + slab_start, 1 + slab_start + 3))
    retained_indices = [
        index for index in range(state.n) if index not in hidden_indices
    ]
    retained_original = tuple(state.partition[index] for index in retained_indices)
    projected_count = len(set(ordinary_signature.projected_partition))
    original_by_projected = [None] * projected_count
    for projected, original in zip(
        ordinary_signature.projected_partition, retained_original, strict=True
    ):
        if original_by_projected[projected] is None:
            original_by_projected[projected] = original
    token_original = [
        *original_by_projected,
        *(state.partition[index] for index in sorted(hidden_indices)),
    ]
    original_to_attachment = {}
    for original, attachment in zip(
        token_original, ordinary_signature.attachment_partition, strict=True
    ):
        original_to_attachment.setdefault(original, attachment)
        if original_to_attachment[original] != attachment:
            raise AssertionError("one component received inconsistent attachment labels")
    if len(original_to_attachment) != len(state.components):
        raise AssertionError("open-slab tokens omitted a live component")
    payloads = [None] * len(state.components)
    for original, attachment in original_to_attachment.items():
        component = state.components[original]
        payloads[attachment] = {
            "attachment_label": attachment,
            "contains_out": original == state.partition[0],
            "vertices": component.vertices,
            "edges": component.edges,
            "cycle_rank": component.cycle_rank,
        }
    if any(payload is None for payload in payloads):
        raise AssertionError("attachment payload labels are not contiguous")
    visible_attachment_labels = set(
        ordinary_signature.attachment_partition[:projected_count]
    )
    forgotten_only = sorted(set(range(len(payloads))) - visible_attachment_labels)
    return {
        **asdict(ordinary_signature),
        "component_payloads": payloads,
        "forgotten_only_components": forgotten_only,
    }


def build_alignment_records() -> tuple[dict, dict]:
    records = {}
    summaries = {}
    for item in known_alignment_inputs():
        source = _orientation(item["source"], item["source_orientation"])
        target = _orientation(item["target"], item["target_orientation"])
        alignment = find_alignment(
            source,
            target,
            item["radius"],
            allow_boundary_rewrites=True,
            source_orientation=item["source_orientation"],
            target_orientation=item["target_orientation"],
        )
        if alignment is None:
            raise AssertionError(f"{item['id']}: frozen alignment no longer exists")
        rewrite_census = replay_alignment(source, target, alignment)
        source_trace = replay_rows(source)
        target_trace = replay_rows(target)
        cumulative_inserted_u = 0
        cumulative_aligned_rewrite_delta = 0
        cumulative_boundary_rewrite_delta = 0
        rows = []
        counts = {
            "mask_equal": 0,
            "partition_equal": 0,
            "normalized_cost_equal": 0,
            "cycle_excess_equal": 0,
            "all_visible_channels_equal": 0,
            "rows_with_forgotten_only_components": 0,
        }
        for step in alignment.steps:
            cumulative_inserted_u += step.row_census.inserted_u
            cumulative_aligned_rewrite_delta += (
                step.row_census.rewrites_to_u - step.row_census.rewrites_to_dot
            )
            cumulative_boundary_rewrite_delta += (
                step.row_census.boundary_rewrites_to_u
                - step.row_census.boundary_rewrites_to_dot
            )
            logical_source_rows = step.source_cursor_before + (
                step.operation == "ADVANCE"
            )
            source_state = source_trace[logical_source_rows]
            target_state = target_trace[step.target_row + 1]
            record = {
                "target_row": step.target_row,
                "operation": step.operation,
                "source_row": step.source_row,
                "source_cursor_before": step.source_cursor_before,
                "logical_source_rows": logical_source_rows,
                "seam": step.seam,
                "packet_start": 1 + 3 * step.seam,
                "row_census": asdict(step.row_census),
                "cumulative_inserted_u": cumulative_inserted_u,
                "cost_channels": {
                    "deleted_packet_u": cumulative_inserted_u,
                    "aligned_rewrite_delta": cumulative_aligned_rewrite_delta,
                    "boundary_rewrite_delta": cumulative_boundary_rewrite_delta,
                    "target_minus_source": target_state.u_cost - source_state.u_cost,
                    "note": "HOLD duplication is included only in target_minus_source",
                },
                "source_state": state_record(source_state),
                "target_state": state_record(target_state),
                "normalized_target": None,
                "comparison": None,
            }
            if len(target_state.partition) == target_state.n:
                normalized = ranked_open_signature_record(
                    target_state,
                    record["packet_start"],
                    cumulative_inserted_u,
                )
                comparison = {
                    "mask_equal": (
                        normalized["compressed_previous_u_mask"]
                        == source_state.previous_u_mask
                    ),
                    "partition_equal": (
                        tuple(normalized["projected_partition"])
                        == source_state.partition
                    ),
                    "normalized_cost_equal": (
                        normalized["normalized_u_cost"] == source_state.u_cost
                    ),
                    "cycle_excess_equal": (
                        normalized["cycle_excess"] == source_state.cycle_excess
                    ),
                }
                comparison["all_visible_channels_equal"] = all(comparison.values())
                for field, value in comparison.items():
                    counts[field] += value
                counts["rows_with_forgotten_only_components"] += bool(
                    normalized["forgotten_only_components"]
                )
                record["normalized_target"] = normalized
                record["comparison"] = comparison
            rows.append(record)
        records[item["id"]] = {
            "source_n": len(source),
            "target_n": len(target),
            "source_orientation": item["source_orientation"],
            "target_orientation": item["target_orientation"],
            "radius": item["radius"],
            "allow_boundary_rewrites": True,
            "rewrite_census": rewrite_census,
            "hold_rows": [
                {"target_row": step.target_row, "source_row": step.source_row}
                for step in alignment.steps
                if step.operation == "HOLD"
            ],
            "seam_schedule": [step.seam for step in alignment.steps],
            "rows": rows,
        }
        comparable_rows = len(target) - 1
        summaries[item["id"]] = {
            "comparable_rows": comparable_rows,
            **counts,
        }
    return records, summaries


def build_claim() -> dict:
    witnesses = {}
    for identifier, (kind, rows) in sorted(known_witnesses().items()):
        trace = replay_rows(rows)
        metric = analyze(identifier, list(rows))
        final = trace[-1]
        if (
            final.edge_count != metric.edges
            or final.cycle_excess != metric.cycle_rank
            or final.introduced_vertices != metric.dual_vertices
        ):
            raise AssertionError(f"{identifier}: ranked endpoint disagrees with direct analysis")
        witnesses[identifier] = {
            "kind": kind,
            "n": len(rows),
            "u_count": sum(row.count("U") for row in rows),
            "q_old": q_formula(len(rows)),
            "surplus": sum(row.count("U") for row in rows) - q_formula(len(rows)),
            "rows_sha256": _rows_sha256(rows),
            "direct_metrics": {
                "dual_vertices": metric.dual_vertices,
                "dual_edges": metric.edges,
                "components": metric.components,
                "component_sizes": metric.component_sizes,
                "component_cycle_ranks": metric.component_cycle_ranks,
            },
            "trace": [state_record(state) for state in trace],
        }
    alignments, comparisons = build_alignment_records()
    return {
        "semantics": {
            "processing": "top-down-row-v1",
            "out_slot": 0,
            "partition_labels": "canonical-first-frontier-occurrence-v1",
            "cycle_rank": "dual-multigraph-component-rank-v1",
            "scope": "five-known-witnesses-diagnostic-only-v1",
            "alignment_selection": "d4-advance-hold-lower-seam-first-v1",
            "cost_normalization": "cumulative-row-dependent-deleted-packet-u-v1",
        },
        "witnesses": witnesses,
        "alignments": alignments,
        "comparisons": comparisons,
    }


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("utf-8")


def build_artifact() -> dict:
    claim = build_claim()
    identity = {"schema": SCHEMA, "claim": claim}
    dependencies = [
        "analysis/residue_two_frontier_signatures.py",
        "analysis/analyze_residue_constructions.py",
        "analysis/census_moving_seam_alignment.py",
        "analysis/construction_lab.py",
        "analysis/diagonal_patterns.py",
        "analysis/open_slab_signature.py",
        "analysis/residue_two_phase_front_witness.txt",
        "analysis/tile_grammar.py",
    ]
    artifact = {
        "schema": SCHEMA,
        "claim": claim,
        "provenance": {
            "producer": "analysis/residue_two_frontier_signatures.py",
            "dependencies": [
                {
                    "path": path,
                    "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
                }
                for path in dependencies
            ],
            "command": [
                "python3",
                "analysis/residue_two_frontier_signatures.py",
                "--output",
                "analysis/residue_two_frontier_traces.json",
            ],
        },
        "performance": {
            "elapsed_seconds": None,
            "peak_rss_bytes": None,
            "workers": 1,
        },
        "integrity": {
            "algorithm": "sha256",
            "canonicalization": "canonical-json-v1",
            "claim_sha256": hashlib.sha256(_canonical_json_bytes(identity)).hexdigest(),
        },
    }
    return json.loads(_canonical_json_bytes(artifact))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    artifact = build_artifact()
    args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    print(
        f"wrote {args.output}: witnesses={len(artifact['claim']['witnesses'])} "
        f"claim={artifact['integrity']['claim_sha256']}"
    )


if __name__ == "__main__":
    main()
