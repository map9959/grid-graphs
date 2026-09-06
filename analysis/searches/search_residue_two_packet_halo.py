#!/usr/bin/env python3
"""Exact radius-four packet search around the n=20 249-U near candidate.

Only rows 8..13 and interior packet columns 0..2 are mutable.  The search
enumerates every candidate at packet Hamming distance at most four, subject to
zero net packet charge and at least one changed packet incident to the detached
3x4 face rectangle's cut.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from itertools import combinations
from math import comb
from pathlib import Path

from analysis.patterns.construction_lab import forest_completion_check, q_old_formula as q_formula, run_check
from analysis.searches.search_residue_two_middle import KNOWN_249_NEAR
from analysis._paths import analysis_path


N = 20
ROW_START = 8
ROW_STOP = 14
PACKET_STARTS = (1, 4, 7)
MAX_CHANGED = 4
RESULT_PATH = analysis_path("residue_two_packet_halo_result.json")
NEAR_SHA256 = "34d8fb20c9a6cd395060f82cfafd27f229239a137119f9c2f9dfe16946e6b68a"
ALPHABET = {
    "L": "UU.",
    "X": "U.U",
    "R": ".UU",
    "H": "UUU",
    "A": "U..",
    "S": ".U.",
    "B": "..U",
    "E": "...",
}
DETACHED_FACES = frozenset((row, column) for row in range(9, 12) for column in range(3, 7))


@dataclass
class Counts:
    position_sets: int = 0
    nominal: int = 0
    zero_charge: int = 0
    cut_open: int = 0
    dual_connected: int = 0
    forest: int = 0


@dataclass
class RegressionCounts:
    exhaustive_low_radius: int = 0
    sampled_high_radius: int = 0
    radius_3_zero_charge_seen: int = 0
    radius_4_zero_charge_seen: int = 0
    sampled_radius_3: int = 0
    sampled_radius_4: int = 0


def dual_endpoints(first: int, second: int) -> tuple[int, int]:
    """Return integer dual-face IDs for one adjacent primal edge."""
    r1, c1 = divmod(first, N)
    r2, _ = divmod(second, N)
    if r1 == r2:
        return (
            0 if r1 == 0 else 1 + (r1 - 1) * (N - 1) + c1,
            0 if r1 + 1 == N else 1 + r1 * (N - 1) + c1,
        )
    return (
        0 if c1 == 0 else 1 + r1 * (N - 1) + c1 - 1,
        0 if c1 + 1 == N else 1 + r1 * (N - 1) + c1,
    )


def primal_edges() -> list[tuple[int, int, int, int]]:
    edges = []
    for row in range(N):
        for column in range(N - 1):
            first = row * N + column
            left, right = dual_endpoints(first, first + 1)
            edges.append((first, first + 1, left, right))
    for row in range(N - 1):
        for column in range(N):
            first = row * N + column
            left, right = dual_endpoints(first, first + N)
            edges.append((first, first + N, left, right))
    return edges


def cut_edges(edges: list[tuple[int, int, int, int]]) -> list[tuple[int, int, int, int]]:
    detached_ids = {1 + row * (N - 1) + column for row, column in DETACHED_FACES}
    return [edge for edge in edges if (edge[2] in detached_ids) != (edge[3] in detached_ids)]


def incident_packets(edges: list[tuple[int, int, int, int]]) -> frozenset[int]:
    crossing_vertices = {vertex for edge in cut_edges(edges) for vertex in edge[:2]}
    return frozenset(
        index
        for index, (row, start) in enumerate(
            (row, start)
            for row in range(ROW_START, ROW_STOP)
            for start in PACKET_STARTS
        )
        if any(row * N + column in crossing_vertices for column in range(start, start + 3))
    )


class ContractedDual:
    """Exact dual connectivity with all fixed active edges precontracted."""

    def __init__(self, baseline_bits: int, mutable_mask: int, edges: list[tuple[int, int, int, int]]):
        total_faces = 1 + (N - 1) ** 2
        parent = list(range(total_faces))

        def find(value: int) -> int:
            while parent[value] != value:
                parent[value] = parent[parent[value]]
                value = parent[value]
            return value

        def union(left: int, right: int) -> None:
            left, right = find(left), find(right)
            if left != right:
                parent[right] = left

        dynamic = []
        for first, second, left, right in edges:
            endpoint_mask = (1 << first) | (1 << second)
            if endpoint_mask & mutable_mask:
                dynamic.append((endpoint_mask, left, right))
            elif baseline_bits & endpoint_mask == endpoint_mask:
                union(left, right)

        roots = sorted({find(face) for face in range(total_faces)})
        root_id = {root: index for index, root in enumerate(roots)}
        self.dynamic = [
            (mask, root_id[find(left)], root_id[find(right)])
            for mask, left, right in dynamic
            if find(left) != find(right)
        ]
        self.vertices = len(roots)

    def connected(self, bits: int) -> bool:
        parent = list(range(self.vertices))
        components = self.vertices

        def find(value: int) -> int:
            while parent[value] != value:
                parent[value] = parent[parent[value]]
                value = parent[value]
            return value

        for endpoint_mask, left, right in self.dynamic:
            if bits & endpoint_mask != endpoint_mask:
                continue
            left, right = find(left), find(right)
            if left != right:
                parent[right] = left
                components -= 1
                if components == 1:
                    return True
        return components == 1


def rows_to_bits(rows: list[str]) -> int:
    return sum(
        1 << (row * N + column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "U"
    )


def dual_components(bits: int, edges: list[tuple[int, int, int, int]]) -> list[set[int]]:
    adjacency = [set() for _ in range(1 + (N - 1) ** 2)]
    for first, second, left, right in edges:
        if bits & (1 << first) and bits & (1 << second):
            adjacency[left].add(right)
            adjacency[right].add(left)
    unseen = set(range(len(adjacency)))
    components = []
    while unseen:
        component = {unseen.pop()}
        stack = list(component)
        while stack:
            new = adjacency[stack.pop()] & unseen
            unseen.difference_update(new)
            component.update(new)
            stack.extend(new)
        components.append(component)
    return components


def bits_to_rows(bits: int) -> list[str]:
    return [
        "".join("U" if bits & (1 << (row * N + column)) else "." for column in range(N))
        for row in range(N)
    ]


def independent_validate(rows: list[str]) -> None:
    """Recheck a witness using graph traversal and a separate forced-cycle test."""
    if sum(row.count("U") for row in rows) != q_formula(N):
        raise AssertionError("independent U-count validation failed")
    bits = rows_to_bits(rows)
    adjacency = [set() for _ in range(1 + (N - 1) ** 2)]
    for first, second, left, right in primal_edges():
        if bits & (1 << first) and bits & (1 << second):
            adjacency[left].add(right)
            adjacency[right].add(left)
    seen = {0}
    stack = [0]
    while stack:
        stack.extend(adjacency[stack.pop()] - seen)
        seen.update(stack)
    if len(seen) != len(adjacency):
        raise AssertionError("independent dual traversal failed")

    parent = list(range(N * N))

    def find(value: int) -> int:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    for first, second, _, _ in primal_edges():
        if bits & (1 << first) and bits & (1 << second):
            continue
        left, right = find(first), find(second)
        if left == right:
            raise AssertionError("independent forced-forest validation failed")
        parent[right] = left


def mixed_bits(value: int) -> int:
    """Stable integer mixer used for deterministic higher-radius sampling."""
    value ^= value >> 127
    value ^= value >> 61
    value ^= value >> 29
    return value


def search(output: Path = RESULT_PATH) -> list[list[str]]:
    near = list(KNOWN_249_NEAR)
    if len(near) != N or any(len(row) != N for row in near):
        raise AssertionError("KNOWN_249_NEAR must be the frozen 20x20 near candidate")
    near_sha256 = hashlib.sha256(("\n".join(near) + "\n").encode("ascii")).hexdigest()
    if near_sha256 != NEAR_SHA256:
        raise AssertionError(
            f"KNOWN_249_NEAR provenance changed: {near_sha256}, expected {NEAR_SHA256}"
        )
    print(f"KNOWN_249_NEAR sha256={near_sha256}", flush=True)
    baseline_bits = rows_to_bits(near)
    if baseline_bits.bit_count() != q_formula(N):
        raise AssertionError("near candidate no longer has 249 U")

    positions = [(row, start) for row in range(ROW_START, ROW_STOP) for start in PACKET_STARTS]
    packet_cell_masks = [
        sum(1 << (row * N + column) for column in range(start, start + 3))
        for row, start in positions
    ]
    mutable_mask = sum(packet_cell_masks)
    edges = primal_edges()
    components = dual_components(baseline_bits, edges)
    detached_ids = {1 + row * (N - 1) + column for row, column in DETACHED_FACES}
    if len(components) != 2 or detached_ids not in components:
        raise AssertionError("near candidate no longer has the declared detached rectangle")
    incident = incident_packets(edges)
    if len(positions) != 18 or len(incident) != 10:
        raise AssertionError(f"packet geometry changed: positions={len(positions)} incident={len(incident)}")

    options = []
    for index, (row, start) in enumerate(positions):
        pattern = near[row][start : start + 3]
        if pattern not in ALPHABET.values():
            raise AssertionError(f"near packet {(row, start)}={pattern!r} is outside the alphabet")
        old_count = pattern.count("U")
        choices = []
        for name, replacement in ALPHABET.items():
            if replacement == pattern:
                continue
            replacement_bits = sum(
                1 << (row * N + start + offset)
                for offset, value in enumerate(replacement)
                if value == "U"
            )
            choices.append((name, replacement_bits, replacement.count("U") - old_count))
        options.append(tuple(choices))

    contracted = ContractedDual(baseline_bits, mutable_mask, edges)
    crossing_masks = [((1 << first) | (1 << second)) for first, second, _, _ in cut_edges(edges)]
    counts = [Counts() for _ in range(MAX_CHANGED + 1)]
    regression = RegressionCounts()
    witnesses: list[list[str]] = []

    def validate_contracted(bits: int, changed_count: int) -> None:
        exact = len(dual_components(bits, edges)) == 1
        if contracted.connected(bits) != exact:
            raise AssertionError("contracted and full dual connectivity disagree")
        if changed_count >= 3:
            regression.sampled_high_radius += 1
            if changed_count == 3:
                regression.sampled_radius_3 += 1
            else:
                regression.sampled_radius_4 += 1
        else:
            regression.exhaustive_low_radius += 1

    for changed_count in range(MAX_CHANGED + 1):
        for selected in combinations(range(len(positions)), changed_count):
            if not any(index in incident for index in selected):
                continue
            count = counts[changed_count]
            count.position_sets += 1
            selected_options = [options[index] for index in selected]
            nominal = 1
            for choices in selected_options:
                nominal *= len(choices)
            count.nominal += nominal
            suffix_min = [0] * (changed_count + 1)
            suffix_max = [0] * (changed_count + 1)
            for depth in range(changed_count - 1, -1, -1):
                deltas = [choice[2] for choice in selected_options[depth]]
                suffix_min[depth] = suffix_min[depth + 1] + min(deltas)
                suffix_max[depth] = suffix_max[depth + 1] + max(deltas)

            def enumerate_quota(depth: int, charge: int, bits: int) -> None:
                if not suffix_min[depth] <= -charge <= suffix_max[depth]:
                    return
                if depth == changed_count:
                    if bits.bit_count() != q_formula(N):
                        raise AssertionError("zero packet charge did not preserve total U")
                    count.zero_charge += 1
                    if changed_count <= 2:
                        validate_contracted(bits, changed_count)
                    else:
                        if changed_count == 3:
                            regression.radius_3_zero_charge_seen += 1
                            ordinal = regression.radius_3_zero_charge_seen
                        else:
                            regression.radius_4_zero_charge_seen += 1
                            ordinal = regression.radius_4_zero_charge_seen
                        if ordinal <= 2_500 or mixed_bits(bits) % 64 == 0:
                            validate_contracted(bits, changed_count)
                    if not any(bits & mask == mask for mask in crossing_masks):
                        return
                    count.cut_open += 1
                    if not contracted.connected(bits):
                        return
                    count.dual_connected += 1
                    rows = bits_to_rows(bits)
                    forest_ok, _ = forest_completion_check(rows)
                    if not forest_ok:
                        return
                    count.forest += 1
                    witnesses.append(rows)
                    return

                packet_index = selected[depth]
                cleared = bits & ~packet_cell_masks[packet_index]
                for _, replacement_bits, delta in selected_options[depth]:
                    enumerate_quota(depth + 1, charge + delta, cleared | replacement_bits)

            enumerate_quota(0, 0, baseline_bits)

    expected_position_sets = [0] + [comb(18, k) - comb(8, k) for k in range(1, MAX_CHANGED + 1)]
    for changed_count, count in enumerate(counts):
        if count.position_sets != expected_position_sets[changed_count]:
            raise AssertionError("incomplete packet-position enumeration")
        print(
            f"changed={changed_count} position_sets={count.position_sets} nominal={count.nominal} "
            f"zero_charge={count.zero_charge} cut_open={count.cut_open} "
            f"dual_connected={count.dual_connected} forest={count.forest}",
            flush=True,
        )
    if regression.exhaustive_low_radius != sum(count.zero_charge for count in counts[1:3]):
        raise AssertionError("low-radius dual regression did not cover every zero-charge candidate")
    if regression.sampled_high_radius < 5_000:
        raise AssertionError("higher-radius dual regression sample is smaller than 5,000")
    if regression.sampled_radius_3 < 2_500 or regression.sampled_radius_4 < 2_500:
        raise AssertionError("higher-radius dual regression did not cover both radii")
    print(
        f"exhausted radius={MAX_CHANGED} packets={len(positions)} incident={len(incident)} "
        f"contracted_dual_vertices={contracted.vertices} witnesses={len(witnesses)}"
    )
    print(
        "contracted_vs_full_dual "
        f"exhaustive_radius_1_2={regression.exhaustive_low_radius} "
        f"sampled_radius_3_4={regression.sampled_high_radius}"
    )

    for number, rows in enumerate(witnesses, start=1):
        info = run_check(N, rows)
        if not info["all_ok"]:
            raise AssertionError("contracted search witness failed full project validation")
        independent_validate(rows)
        print(f"witness={number} independently_validated")
        print("\n".join(rows))

    artifact = {
        "schema": "grid-graphs.residue-two-packet-halo.v1",
        "provenance": {
            "candidate": "search_residue_two_middle.KNOWN_249_NEAR",
            "sha256": near_sha256,
            "canonical_encoding": "ASCII rows joined by LF with one final LF",
        },
        "scope": {
            "n": N,
            "target_u": q_formula(N),
            "packet_rows_inclusive": [ROW_START, ROW_STOP - 1],
            "packet_column_indices": [0, 1, 2],
            "packet_primal_column_starts": list(PACKET_STARTS),
            "packet_count": len(positions),
            "incident_packet_count": len(incident),
            "incident_packets": [
                {"row": positions[index][0], "packet_column": index % len(PACKET_STARTS)}
                for index in sorted(incident)
            ],
            "maximum_changed_packets": MAX_CHANGED,
            "radius_metric": "packet Hamming distance from the provenance candidate",
            "outside_packet_window": "frozen exactly to the provenance candidate",
            "packet_charge": "packet U count minus 2",
            "requires_exact_zero_packet_charge_change": True,
            "requires_changed_packet_incident_to_detached_cut": True,
            "detached_face_rectangle": {
                "rows_inclusive": [9, 11],
                "columns_inclusive": [3, 6],
            },
        },
        "alphabet": ALPHABET,
        "method": {
            "enumeration": "position combinations with exact charge quota pruning",
            "dual_check": "exact dynamic dual after contraction of all fixed active edges",
            "contracted_dual_vertices": contracted.vertices,
            "regression": {
                "full_dual_method": "fresh full 362-vertex adjacency and component traversal",
                "exhaustive_zero_charge_radii": [1, 2],
                "exhaustive_candidates_checked": regression.exhaustive_low_radius,
                "sampled_zero_charge_radii": [3, 4],
                "deterministic_sample_rule": (
                    "first 2500 at each of radii 3 and 4, plus mixed candidate bits "
                    "congruent to 0 mod 64"
                ),
                "higher_radius_zero_charge_seen": {
                    "3": regression.radius_3_zero_charge_seen,
                    "4": regression.radius_4_zero_charge_seen,
                },
                "sampled_candidates_checked": regression.sampled_high_radius,
                "sampled_candidates_by_radius": {
                    "3": regression.sampled_radius_3,
                    "4": regression.sampled_radius_4,
                },
                "disagreements": 0,
            },
        },
        "counts_by_radius": [
            {"changed_packets": changed_count, **asdict(count)}
            for changed_count, count in enumerate(counts)
        ],
        "result": {
            "exhaustive": True,
            "witness_count": len(witnesses),
            "status": "witness_found" if witnesses else "no_witness",
            "witnesses": witnesses,
        },
    }
    output.write_text(json.dumps(artifact, indent=2) + "\n")
    rebuilt = json.loads(output.read_text())
    if rebuilt != artifact:
        raise AssertionError("JSON result artifact failed round-trip validation")
    print(f"result_artifact={output}")
    return witnesses


if __name__ == "__main__":
    search()
