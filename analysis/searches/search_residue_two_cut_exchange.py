#!/usr/bin/env python3
"""Exact bounded exchanges around the n=20 target-249 two-component join.

This exhausts only the declared local exchange neighborhoods.  It is not a
global optimizer and a negative result is not a global impossibility result.
Primal rows 8..13 and columns 1..9 are the removal window (zero-based,
inclusive).  Additions are restricted to missing endpoints of cut edges on the
boundary of the detached 3x4 face rectangle.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import time
from dataclasses import asdict, dataclass, field
from itertools import combinations
from math import comb
from pathlib import Path
from typing import Iterable

from analysis._paths import analysis_path
from analysis.patterns.construction_lab import forest_completion_check, run_check
from analysis.patterns.construction_lab import q_old_formula as q_formula

N = 20
WINDOW_ROWS = range(8, 14)
WINDOW_COLUMNS = range(1, 10)
DETACHED_FACES = frozenset((r, c) for r in range(9, 12) for c in range(3, 7))
RESULT_SCHEMA = "grid-graphs.search_residue_two_cut_exchange.result.v1"
DEFAULT_RESULT_PATH = analysis_path("search_residue_two_cut_exchange_result.json")
BASELINE_SHA256 = "34d8fb20c9a6cd395060f82cfafd27f229239a137119f9c2f9dfe16946e6b68a"
BASELINE_HASH_ENCODING = "ASCII rows joined by LF, including one trailing LF"
ORDER3_REGRESSION_STRIDE = 64
ORDER4_REGRESSION_STRIDE = 1024
DEFAULT_MAX_RUNTIME_SECONDS = 8 * 60

# Unique deterministic n=20, target-249, basic-alphabet beam-100 best join at
# split 8.  It is a near candidate, not a valid witness.
EMBEDDED_249_NEAR = (
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
)


class DSU:
    def __init__(self, size: int):
        self.parent = list(range(size))
        self.components = size

    def find(self, value: int) -> int:
        while self.parent[value] != value:
            self.parent[value] = self.parent[self.parent[value]]
            value = self.parent[value]
        return value

    def union(self, left: int, right: int) -> bool:
        left, right = self.find(left), self.find(right)
        if left == right:
            return False
        self.parent[right] = left
        self.components -= 1
        return True


@dataclass(frozen=True, slots=True)
class DualEdge:
    vertices: tuple[int, int]
    faces: tuple[int, int]

    @property
    def vertex_mask(self) -> int:
        return (1 << self.vertices[0]) | (1 << self.vertices[1])


@dataclass(slots=True)
class Counts:
    generated: int = 0
    unique: int = 0
    duplicate: int = 0
    edge_pruned: int = 0
    rank_pruned: int = 0
    contracted_pruned: int = 0
    exact_checks: int = 0
    forest_rejected: int = 0
    hits: int = 0
    regression_checked: int = 0
    regression_checked_by_class: dict[str, int] = field(
        default_factory=lambda: {
            "edge_pruned": 0,
            "rank_pruned": 0,
            "contracted_pruned": 0,
            "exact_check": 0,
        }
    )


@dataclass(frozen=True, slots=True)
class CutDeficit:
    primal_edge: tuple[int, int]
    dual_faces: tuple[int, int]
    missing_endpoints: tuple[int, ...]


class SearchTimeout(RuntimeError):
    pass


def rows_to_bits(rows: Iterable[str]) -> int:
    return sum(
        1 << (r * N + c)
        for r, row in enumerate(rows)
        for c, value in enumerate(row)
        if value == "U"
    )


def bits_to_rows(bits: int) -> list[str]:
    return [
        "".join("U" if bits & (1 << (r * N + c)) else "." for c in range(N))
        for r in range(N)
    ]


def baseline_sha256(rows: Iterable[str]) -> str:
    payload = ("\n".join(rows) + "\n").encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def face_id(row: int, column: int) -> int:
    return 1 + row * (N - 1) + column


def dual_edges() -> tuple[DualEdge, ...]:
    edges = []
    for r in range(N):
        for c in range(N - 1):
            faces = (
                0 if r == 0 else face_id(r - 1, c),
                0 if r == N - 1 else face_id(r, c),
            )
            edges.append(DualEdge((r * N + c, r * N + c + 1), faces))
    for r in range(N - 1):
        for c in range(N):
            faces = (
                0 if c == 0 else face_id(r, c - 1),
                0 if c == N - 1 else face_id(r, c),
            )
            edges.append(DualEdge((r * N + c, (r + 1) * N + c), faces))
    return tuple(edges)


DUAL_EDGES = dual_edges()
FACE_COUNT = 1 + (N - 1) ** 2


def active(edge: DualEdge, bits: int) -> bool:
    return bits & edge.vertex_mask == edge.vertex_mask


def dual_components(bits: int) -> tuple[DSU, int]:
    dsu = DSU(FACE_COUNT)
    edge_count = 0
    for edge in DUAL_EDGES:
        if active(edge, bits):
            edge_count += 1
            dsu.union(*edge.faces)
    return dsu, edge_count


def load_candidate() -> tuple[str, ...]:
    """Prefer a populated producer constant, while retaining a robust embed."""
    try:
        from analysis.searches.search_residue_two_middle import KNOWN_249_NEAR
    except ImportError:
        KNOWN_249_NEAR = []
    if KNOWN_249_NEAR and tuple(KNOWN_249_NEAR) != EMBEDDED_249_NEAR:
        raise AssertionError("producer KNOWN_249_NEAR differs from the embedded candidate")
    return tuple(KNOWN_249_NEAR) if KNOWN_249_NEAR else EMBEDDED_249_NEAR


def verify_baseline(rows: tuple[str, ...]) -> tuple[int, tuple[int, ...]]:
    if len(rows) != N or any(len(row) != N for row in rows):
        raise AssertionError("near candidate must be 20x20")
    bits = rows_to_bits(rows)
    actual_sha256 = baseline_sha256(rows)
    if actual_sha256 != BASELINE_SHA256:
        raise AssertionError(
            f"near candidate SHA-256 changed: {actual_sha256} != {BASELINE_SHA256}"
        )
    if bits.bit_count() != q_formula(N):
        raise AssertionError("near candidate is not at the exact 249-U target")
    dsu, edge_count = dual_components(bits)
    groups: dict[int, set[int]] = {}
    for face in range(FACE_COUNT):
        groups.setdefault(dsu.find(face), set()).add(face)
    expected_detached = {face_id(r, c) for r, c in DETACHED_FACES}
    components = sorted(groups.values(), key=len)
    if len(components) != 2 or components[0] != expected_detached:
        raise AssertionError(
            f"expected detached 3x4 rectangle, got component sizes "
            f"{sorted(map(len, components))}"
        )
    if edge_count != 361:
        raise AssertionError(f"expected 361 U-U edges, got {edge_count}")
    forest_ok, reason = forest_completion_check(list(rows))
    if forest_ok or reason != "forced edges contain a cycle":
        raise AssertionError(f"unexpected baseline forest result: {forest_ok}, {reason}")
    return bits, tuple(sorted(map(len, components)))


def cut_additions(bits: int) -> tuple[tuple[int, ...], tuple[CutDeficit, ...]]:
    detached_ids = {face_id(r, c) for r, c in DETACHED_FACES}
    deficits = []
    eligible = set()
    for edge in DUAL_EDGES:
        if (edge.faces[0] in detached_ids) == (edge.faces[1] in detached_ids):
            continue
        missing = tuple(v for v in edge.vertices if not bits & (1 << v))
        if not missing:
            raise AssertionError("baseline already activates a detached cut edge")
        if len(missing) not in (1, 2):
            raise AssertionError("invalid cut-edge endpoint deficit")
        deficits.append(CutDeficit(edge.vertices, edge.faces, missing))
        eligible.update(missing)
    deficit_counts = tuple(
        sum(len(deficit.missing_endpoints) == size for deficit in deficits)
        for size in (1, 2)
    )
    if deficit_counts != (8, 6):
        raise AssertionError(f"unexpected cut deficits: {deficits}")
    if any(
        divmod(v, N)[0] not in WINDOW_ROWS
        or divmod(v, N)[1] not in WINDOW_COLUMNS
        for v in eligible
    ):
        raise AssertionError("eligible cut endpoint lies outside the declared window")
    return tuple(sorted(eligible)), tuple(deficits)


class ContractedDual:
    """Dual graph contracted through edges immutable under this search."""

    def __init__(self, baseline: int, mutable_vertices: set[int]):
        static = DSU(FACE_COUNT)
        for edge in DUAL_EDGES:
            if not mutable_vertices.intersection(edge.vertices) and active(edge, baseline):
                static.union(*edge.faces)
        roots = sorted({static.find(face) for face in range(FACE_COUNT)})
        root_index = {root: index for index, root in enumerate(roots)}
        self.component_count = len(roots)
        self.edges = tuple(
            (
                edge.vertex_mask,
                root_index[static.find(edge.faces[0])],
                root_index[static.find(edge.faces[1])],
            )
            for edge in DUAL_EDGES
            if mutable_vertices.intersection(edge.vertices)
        )
        self.static_edge_count = sum(
            active(edge, baseline)
            for edge in DUAL_EDGES
            if not mutable_vertices.intersection(edge.vertices)
        )
        self.nonloop_mask = sum(
            1 << index
            for index, (_, left, right) in enumerate(self.edges)
            if left != right
        )
        incident_masks = [0] * (N * N)
        for index, edge in enumerate(DUAL_EDGES):
            if not mutable_vertices.intersection(edge.vertices):
                continue
            dynamic_index = sum(
                bool(mutable_vertices.intersection(previous.vertices))
                for previous in DUAL_EDGES[:index]
            )
            for vertex in edge.vertices:
                incident_masks[vertex] |= 1 << dynamic_index
        self.incident_masks = tuple(incident_masks)

    def active_mask(self, bits: int) -> int:
        return sum(
            1 << index
            for index, (mask, _, _) in enumerate(self.edges)
            if bits & mask == mask
        )

    def metrics_from_mask(self, active_mask: int) -> tuple[int, int, bool]:
        edge_count, rank_upper = self.edge_rank_from_mask(active_mask)
        return edge_count, rank_upper, self.connected_from_mask(active_mask)

    def edge_rank_from_mask(self, active_mask: int) -> tuple[int, int]:
        return (
            self.static_edge_count + active_mask.bit_count(),
            (active_mask & self.nonloop_mask).bit_count(),
        )

    def connected_from_mask(self, active_mask: int) -> bool:
        dsu = DSU(self.component_count)
        remaining = active_mask & self.nonloop_mask
        while remaining:
            edge_bit = remaining & -remaining
            index = edge_bit.bit_length() - 1
            _, left, right = self.edges[index]
            dsu.union(left, right)
            remaining ^= edge_bit
        return dsu.components == 1

    def metrics(self, bits: int) -> tuple[int, int, bool]:
        """Return exact edge count, dynamic rank upper bound, and connectivity."""
        return self.metrics_from_mask(self.active_mask(bits))


def independent_forced_forest(bits: int) -> bool:
    """Independent cycle test for all forced (not U-U) primal edges."""
    dsu = DSU(N * N)
    for r in range(N):
        for c in range(N):
            vertex = r * N + c
            for other in (vertex + 1 if c + 1 < N else -1, vertex + N if r + 1 < N else -1):
                if other < 0 or active(DualEdge((vertex, other), (0, 0)), bits):
                    continue
                if not dsu.union(vertex, other):
                    return False
    return True


def exact_validate(bits: int) -> tuple[bool, str]:
    rows = bits_to_rows(bits)
    independent_ok = independent_forced_forest(bits)
    forest_ok, reason = forest_completion_check(rows)
    if independent_ok != forest_ok:
        raise AssertionError("independent forced-forest result disagrees with canonical check")
    info = run_check(N, rows, verbose=False)
    if not info["dual_ok"] or not info["u_match"]:
        raise AssertionError("contracted connected candidate failed canonical dual/count check")
    if info["forest_ok"] != forest_ok:
        raise AssertionError("run_check forest result disagrees with direct forest check")
    return info["all_ok"], reason


def full_dual_regression(
    bits: int, contracted_edge_count: int, contracted_connected: bool
) -> None:
    """Assert contracted metrics against a fresh full 362-face dual DSU."""
    full_dsu, full_edge_count = dual_components(bits)
    full_connected = full_dsu.components == 1
    if (contracted_edge_count, contracted_connected) != (
        full_edge_count,
        full_connected,
    ):
        raise AssertionError(
            "contracted/full dual disagreement: "
            f"contracted=({contracted_edge_count}, {contracted_connected}) "
            f"full=({full_edge_count}, {full_connected})"
        )


def prune_class(
    edge_count: int, rank_upper: int, connected: bool, contracted_components: int
) -> str:
    if edge_count < FACE_COUNT - 1:
        return "edge_pruned"
    if rank_upper < contracted_components - 1:
        return "rank_pruned"
    if not connected:
        return "contracted_pruned"
    return "exact_check"


def search_order(
    order: int,
    baseline: int,
    additions: tuple[int, ...],
    removals: tuple[int, ...],
    contracted: ContractedDual,
    deadline: float,
) -> tuple[Counts, list[tuple[tuple[int, ...], tuple[int, ...], int]], float]:
    started = time.perf_counter()
    counts = Counts()
    hits = []
    removal_sets = tuple(combinations(removals, order))
    for added in combinations(additions, order):
        with_additions = baseline | sum(1 << vertex for vertex in added)
        with_additions_active = contracted.active_mask(with_additions)
        for removed in removal_sets:
            counts.generated += 1
            if counts.generated % 65536 == 0 and time.perf_counter() >= deadline:
                raise SearchTimeout(
                    f"runtime limit reached during order {order} after "
                    f"{counts.generated} generated candidates"
                )
            candidate = with_additions & ~sum(1 << vertex for vertex in removed)
            removed_edges = 0
            for vertex in removed:
                removed_edges |= contracted.incident_masks[vertex]
            candidate_active = with_additions_active & ~removed_edges
            counts.unique += 1
            edge_count, rank_upper = contracted.edge_rank_from_mask(candidate_active)
            regression_stride = {
                3: ORDER3_REGRESSION_STRIDE,
                4: ORDER4_REGRESSION_STRIDE,
            }.get(order)
            regression_selected = order in (1, 2) or (
                regression_stride is not None
                and (counts.generated - 1) % regression_stride == 0
            )
            rank_passes = rank_upper >= contracted.component_count - 1
            edge_passes = edge_count >= FACE_COUNT - 1
            connected = False
            if (edge_passes and rank_passes) or regression_selected:
                connected = contracted.connected_from_mask(candidate_active)
            classification = prune_class(
                edge_count, rank_upper, connected, contracted.component_count
            )
            if regression_selected:
                full_dual_regression(candidate, edge_count, connected)
                counts.regression_checked += 1
                counts.regression_checked_by_class[classification] += 1
            if classification == "edge_pruned":
                counts.edge_pruned += 1
                continue
            if classification == "rank_pruned":
                counts.rank_pruned += 1
                continue
            if classification == "contracted_pruned":
                counts.contracted_pruned += 1
                continue
            counts.exact_checks += 1
            valid, reason = exact_validate(candidate)
            if not valid:
                counts.forest_rejected += 1
                continue
            counts.hits += 1
            hits.append((added, removed, candidate))
            print(f"hit order={order} add={coordinates(added)} remove={coordinates(removed)}")
            print("\n".join(bits_to_rows(candidate)))
            print(
                "validated by contracted dual, independent forced forest, "
                f"forest_completion_check, and run_check ({reason})"
            )
    expected = comb(len(additions), order) * comb(len(removals), order)
    if counts.generated != expected or counts.unique + counts.duplicate != expected:
        raise AssertionError(
            f"order-{order} enumeration incomplete: {counts.generated}/{expected}"
        )
    return counts, hits, time.perf_counter() - started


def coordinates(vertices: Iterable[int]) -> tuple[tuple[int, int], ...]:
    return tuple(divmod(vertex, N) for vertex in vertices)


def face_coordinates(face: int) -> str | tuple[int, int]:
    return "OUT" if face == 0 else divmod(face - 1, N - 1)


def cut_deficit_json(deficit: CutDeficit) -> dict:
    return {
        "deficit": len(deficit.missing_endpoints),
        "primal_edge": coordinates(deficit.primal_edge),
        "dual_faces": tuple(face_coordinates(face) for face in deficit.dual_faces),
        "missing_endpoints": coordinates(deficit.missing_endpoints),
    }


def result_document(
    rows: tuple[str, ...],
    component_sizes: tuple[int, ...],
    additions: tuple[int, ...],
    removals: tuple[int, ...],
    deficits: tuple[CutDeficit, ...],
    contracted: ContractedDual,
    orders: tuple[int, ...],
    order_results: list[tuple[int, Counts]],
) -> dict:
    deficit_counts = {
        str(size): sum(len(item.missing_endpoints) == size for item in deficits)
        for size in (1, 2)
    }
    total_hits = sum(counts.hits for _, counts in order_results)
    return {
        "schema": {"id": RESULT_SCHEMA, "version": 1},
        "scope": {
            "bounded": True,
            "global_optimizer": False,
            "negative_claim": (
                "No hit exists only in the explicitly listed cardinality-preserving "
                "exchange neighborhoods; this is not a global impossibility result."
            ),
            "coordinates": "zero-based",
            "n": N,
            "executed_orders": orders,
            "exchange": "k additions and k removals",
            "removal_window": {
                "rows": [WINDOW_ROWS.start, WINDOW_ROWS.stop - 1],
                "columns": [WINDOW_COLUMNS.start, WINDOW_COLUMNS.stop - 1],
                "bounds": "inclusive",
            },
            "addition_rule": (
                "Missing endpoints of boundary cut edges of the detached 3x4 "
                "face rectangle; each addition activates or contributes to such an edge."
            ),
            "eligible_additions": coordinates(additions),
            "eligible_removals": coordinates(removals),
        },
        "baseline": {
            "sha256": BASELINE_SHA256,
            "sha256_encoding": BASELINE_HASH_ENCODING,
            "rows": rows,
            "u_count": sum(row.count("U") for row in rows),
            "u_u_edge_count": 361,
            "dual_component_sizes": component_sizes,
            "detached_face_rectangle": {
                "rows": [9, 11],
                "columns": [3, 6],
                "bounds": "inclusive",
                "face_count": len(DETACHED_FACES),
            },
        },
        "cut": {
            "deficit_counts": deficit_counts,
            "boundary_edges": [cut_deficit_json(item) for item in deficits],
        },
        "pruning": {
            "unchanged_order": [
                "U-U edge lower bound",
                "contracted nonloop-edge rank upper bound",
                "exact contracted-component connectivity",
                "forest_completion_check and run_check",
            ],
            "static_contracted_components": contracted.component_count,
        },
        "regression": {
            "method": "fresh full-face dual DSU versus contracted edge/connectivity metrics",
            "orders_1_2": "every unique candidate",
            "order_3": {
                "selection": "zero-based enumeration index divisible by stride",
                "stride": ORDER3_REGRESSION_STRIDE,
            },
            "order_4": {
                "selection": "zero-based enumeration index divisible by stride",
                "stride": ORDER4_REGRESSION_STRIDE,
            },
        },
        "orders": [
            {
                "order": order,
                "expected_generated": comb(len(additions), order)
                * comb(len(removals), order),
                "counts": asdict(counts),
            }
            for order, counts in order_results
        ],
        "result": {
            "connected_valid_hits": total_hits,
            "neighborhoods_exhausted": True,
            "bounded_only": True,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--orders",
        type=int,
        nargs="+",
        choices=(1, 2, 3, 4),
        default=(1, 2, 3, 4),
        help="exchange orders to exhaust (default: 1 2 3 4)",
    )
    parser.add_argument(
        "--result-json",
        type=Path,
        default=DEFAULT_RESULT_PATH,
        help=f"reproducible result artifact (default: {DEFAULT_RESULT_PATH})",
    )
    parser.add_argument(
        "--max-runtime-seconds",
        type=float,
        default=DEFAULT_MAX_RUNTIME_SECONDS,
        help="stop without writing a partial artifact after this wall time (default: 480)",
    )
    args = parser.parse_args()
    if args.max_runtime_seconds <= 0:
        parser.error("--max-runtime-seconds must be positive")
    orders = tuple(dict.fromkeys(args.orders))
    run_started = time.perf_counter()
    deadline = run_started + args.max_runtime_seconds

    rows = load_candidate()
    baseline, component_sizes = verify_baseline(rows)
    additions, deficits = cut_additions(baseline)
    deficit_counts = tuple(
        sum(len(item.missing_endpoints) == size for item in deficits)
        for size in (1, 2)
    )
    window = {r * N + c for r in WINDOW_ROWS for c in WINDOW_COLUMNS}
    removals = tuple(sorted(vertex for vertex in window if baseline & (1 << vertex)))
    contracted = ContractedDual(baseline, window)
    print(
        "exact bounded local search (not a global optimizer): "
        f"baseline_U={baseline.bit_count()} dual_components={component_sizes} "
        f"window=rows8..13,cols1..9 eligible_additions={len(additions)} "
        f"removals={len(removals)} cut_deficits(one,two)={deficit_counts} "
        f"static_contracted_components={contracted.component_count}"
    )
    print(f"eligible addition coordinates={coordinates(additions)}")

    total_hits = 0
    order_results = []
    try:
        for order in orders:
            counts, hits, elapsed = search_order(
                order, baseline, additions, removals, contracted, deadline
            )
            total_hits += len(hits)
            order_results.append((order, counts))
            print(
                f"order={order} generated={counts.generated} unique={counts.unique} "
                f"duplicates={counts.duplicate} edge_pruned={counts.edge_pruned} "
                f"rank_pruned={counts.rank_pruned} "
                f"contracted_pruned={counts.contracted_pruned} "
                f"exact_checks={counts.exact_checks} "
                f"forest_rejected={counts.forest_rejected} hits={counts.hits} "
                f"regression_checked={counts.regression_checked} "
                f"regression_by_class={counts.regression_checked_by_class} "
                f"elapsed_seconds={elapsed:.3f}",
                flush=True,
            )
    except SearchTimeout as error:
        print(
            f"STOPPED: {error}; no partial exhaustion claim and result artifact "
            f"left unchanged at {args.result_json}",
            flush=True,
        )
        raise SystemExit(2) from error
    document = result_document(
        rows,
        component_sizes,
        additions,
        removals,
        deficits,
        contracted,
        orders,
        order_results,
    )
    temporary_result = args.result_json.with_name(args.result_json.name + ".tmp")
    temporary_result.write_text(
        json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    os.replace(temporary_result, args.result_json)
    print(f"wrote reproducible bounded result to {args.result_json}")
    print(
        f"exhausted orders={orders}; connected valid hits={total_hits}. "
        f"total_elapsed_seconds={time.perf_counter() - run_started:.3f}. "
        "This result covers only the declared bounded neighborhoods, not the global search space."
    )


if __name__ == "__main__":
    main()
