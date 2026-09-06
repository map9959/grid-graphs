#!/usr/bin/env python3
"""Exact finite rooted open-slab census for the revised residue-two controls."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.residue_certificates.residue_two_frontier_signatures import (
    RankedFrontierState,
    ranked_open_signature_record,
    replay_rows,
)
from analysis.transport.census_moving_seam_alignment import (
    d4_orientations,
    load_square_pattern,
)

HERE = ANALYSIS_ROOT
ROOT = HERE.parent
DEFAULT_OUTPUT = HERE / "residue_two_open_slab_census.json"
SCHEMA = "grid-graphs.residue-two-open-slab-census.v1"
CHANNELS = ("mask", "partition", "closed", "charge", "cycle")


@dataclass(frozen=True, slots=True)
class RootedOpenSlabSignature:
    """A lossless rooted state after three consecutive face ports are opened.

    OUT is retained as projected-partition slot zero.  ``attachment_partition``
    records how every opened port attaches to visible rooted components; an
    interface is closed exactly when no component occurs only on opened ports.
    Cost is normalized by all U cells in the deleted three-column prefix slab.
    """

    compressed_u_mask: int
    projected_partition: tuple[int, ...]
    attachment_partition: tuple[int, ...]
    forgotten_only_components: tuple[int, ...]
    normalized_u_cost: int
    cycle_excess: int

    @classmethod
    def extract(
        cls,
        state: RankedFrontierState,
        slab_start: int,
        removed_u_cost: int,
    ) -> "RootedOpenSlabSignature":
        record = ranked_open_signature_record(state, slab_start, removed_u_cost)
        return cls(
            compressed_u_mask=record["compressed_previous_u_mask"],
            projected_partition=tuple(record["projected_partition"]),
            attachment_partition=tuple(record["attachment_partition"]),
            forgotten_only_components=tuple(record["forgotten_only_components"]),
            normalized_u_cost=record["normalized_u_cost"],
            cycle_excess=record["cycle_excess"],
        )


def rows_sha256(rows: tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def pattern_inputs() -> dict[str, tuple[str, ...]]:
    return {
        "A17": tuple(residue_two_affine_pattern(17)),
        "B20": tuple(load_square_pattern(HERE / "residue_two_phase_front_witness.txt")),
        "A23": tuple(residue_two_affine_pattern(23)),
    }


def removed_prefix_cost(rows: tuple[str, ...], depth: int, slab_start: int) -> int:
    return sum(row[slab_start : slab_start + 3].count("U") for row in rows[:depth])


def mismatch(
    source: RankedFrontierState, signature: RootedOpenSlabSignature
) -> tuple[int, int, int, int, int]:
    return (
        (source.previous_u_mask ^ signature.compressed_u_mask).bit_count(),
        sum(
            left != right
            for left, right in zip(
                source.partition, signature.projected_partition, strict=True
            )
        ),
        len(signature.forgotten_only_components),
        abs(source.u_cost - signature.normalized_u_cost),
        abs(source.cycle_excess - signature.cycle_excess),
    )


def _candidate_record(
    source_name: str,
    target_name: str,
    source_orientation: str,
    target_orientation: str,
    source_depth: int,
    target_depth: int,
    slab_start: int,
    vector: tuple[int, ...],
) -> dict:
    return {
        "source": source_name,
        "target": target_name,
        "source_orientation": source_orientation,
        "target_orientation": target_orientation,
        "source_depth": source_depth,
        "target_depth": target_depth,
        "slab_start": slab_start,
        "mismatch": dict(zip(CHANNELS, vector, strict=True)),
    }


def census_pair(
    source_name: str,
    source_rows: tuple[str, ...],
    target_name: str,
    target_rows: tuple[str, ...],
) -> dict:
    if len(target_rows) != len(source_rows) + 3:
        raise ValueError("open-slab transfer pairs must differ in width by three")
    tested = 0
    exact = []
    best_vector: tuple[int, ...] | None = None
    best_samples = []
    best_exact_charge_topology: tuple[int, ...] | None = None
    best_exact_charge_samples = []
    zero_counts = Counter()
    source_images = d4_orientations(source_rows)
    target_images = d4_orientations(target_rows)
    source_traces = {item.name: replay_rows(item.rows) for item in source_images}
    target_traces = {item.name: replay_rows(item.rows) for item in target_images}
    for source_image in source_images:
        source_trace = source_traces[source_image.name]
        for target_image in target_images:
            target_trace = target_traces[target_image.name]
            for source_depth in range(1, len(source_rows)):
                source = source_trace[source_depth]
                for target_depth in range(1, len(target_rows)):
                    target = target_trace[target_depth]
                    for slab_start in range(len(target_rows) - 3):
                        removed = removed_prefix_cost(
                            target_image.rows, target_depth, slab_start
                        )
                        signature = RootedOpenSlabSignature.extract(
                            target, slab_start, removed
                        )
                        vector = mismatch(source, signature)
                        tested += 1
                        for channel, value in zip(CHANNELS, vector, strict=True):
                            zero_counts[channel] += value == 0
                        record = _candidate_record(
                            source_name,
                            target_name,
                            source_image.name,
                            target_image.name,
                            source_depth,
                            target_depth,
                            slab_start,
                            vector,
                        )
                        if not any(vector):
                            exact.append(record)
                        if vector[3] == 0:
                            topology = (vector[0], vector[1], vector[2], vector[4])
                            if (
                                best_exact_charge_topology is None
                                or topology < best_exact_charge_topology
                            ):
                                best_exact_charge_topology = topology
                                best_exact_charge_samples = [record]
                            elif (
                                topology == best_exact_charge_topology
                                and len(best_exact_charge_samples) < 32
                            ):
                                best_exact_charge_samples.append(record)
                        if best_vector is None or vector < best_vector:
                            best_vector = vector
                            best_samples = [record]
                        elif vector == best_vector and len(best_samples) < 32:
                            best_samples.append(record)
    expected = (
        len(source_images)
        * len(target_images)
        * (len(source_rows) - 1)
        * (len(target_rows) - 1)
        * (len(target_rows) - 3)
    )
    if tested != expected:
        raise AssertionError(f"incomplete pair census: {tested} != {expected}")
    return {
        "id": f"{source_name}-to-{target_name}",
        "source_n": len(source_rows),
        "target_n": len(target_rows),
        "source_sha256": rows_sha256(source_rows),
        "target_sha256": rows_sha256(target_rows),
        "orientation_counts": [len(source_images), len(target_images)],
        "candidates_tested": tested,
        "exact_compatible_count": len(exact),
        "exact_compatible": exact,
        "per_channel_zero_counts": dict(zero_counts),
        "minimum_mismatch": dict(zip(CHANNELS, best_vector, strict=True)),
        "minimum_mismatch_samples": best_samples,
        "exact_charge_candidate_count": zero_counts["charge"],
        "minimum_topology_mismatch_at_exact_charge": dict(
            zip(("mask", "partition", "closed", "cycle"), best_exact_charge_topology, strict=True)
        ),
        "minimum_topology_mismatch_at_exact_charge_samples": best_exact_charge_samples,
    }


def build_artifact() -> dict:
    patterns = pattern_inputs()
    pairs = (
        ("A17", "B20", "cross"),
        ("B20", "A23", "cross"),
        ("A17", "A23", "two-step-control"),
    )
    records = []
    for source, target, kind in pairs:
        if len(patterns[target]) != len(patterns[source]) + 3:
            records.append(
                {
                    "id": f"{source}-to-{target}",
                    "kind": kind,
                    "searched": False,
                    "reason": "width difference is not one three-cell slab",
                }
            )
            continue
        record = census_pair(source, patterns[source], target, patterns[target])
        record["kind"] = kind
        record["searched"] = True
        records.append(record)

    # The affine control is the known self-family positive control.  Its count
    # misses revised exact charge by one, so it is classified before interface
    # matching rather than being mistaken for an exact-charge candidate.
    affine20 = tuple(residue_two_affine_pattern(20))
    affine_increment = sum(row.count("U") for row in affine20) - sum(
        row.count("U") for row in patterns["A17"]
    )
    records.append(
        {
            "id": "A17-to-affine20",
            "kind": "self-family",
            "searched": False,
            "source_n": 17,
            "target_n": 20,
            "actual_increment": affine_increment,
            "required_increment": 71,
            "minimum_charge_mismatch": abs(affine_increment - 71),
            "reason": "globally non-exact charge; known attachment-compatible affine control",
        }
    )
    claim = {
        "scope": {
            "bounded": True,
            "slab_width": 3,
            "depths": "every nonempty nonfinal top-down frontier",
            "shifts": "every legal consecutive three-column face-port interval",
            "orientations": "all distinct D4 images independently on source and target",
            "channels": list(CHANNELS),
            "compatibility": (
                "zero mask Hamming distance, canonical rooted partition distance, "
                "forgotten-only component count, normalized U-cost distance, and "
                "dual cycle-excess distance"
            ),
            "negative_claim": "only the explicitly enumerated A17/B20/affine-A23 straight-cut family",
        },
        "patterns": {
            name: {
                "n": len(rows),
                "u_count": sum(row.count("U") for row in rows),
                "sha256": rows_sha256(rows),
            }
            for name, rows in patterns.items()
        },
        "pairs": records,
    }
    identity = {"schema": SCHEMA, "claim": claim}
    canonical = json.dumps(
        identity, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return {
        "schema": SCHEMA,
        "claim": claim,
        "integrity": {
            "algorithm": "sha256",
            "canonicalization": "canonical-json-v1",
            "claim_sha256": hashlib.sha256(canonical).hexdigest(),
        },
        "provenance": {
            "producer": "analysis/transport/residue_two_open_slab_census.py",
            "dependencies": [
                {
                    "path": path,
                    "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
                }
                for path in (
                    "analysis/residue_two_phase_front_witness.txt",
                    "analysis/residue_certificates/residue_two_frontier_signatures.py",
                    "analysis/transport/open_slab_signature.py",
                    "analysis/patterns/diagonal_patterns.py",
                )
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    artifact = build_artifact()
    args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    print(
        f"wrote {args.output}: "
        + ", ".join(
            f"{pair['id']}={pair.get('exact_compatible_count', 'not-searched')}"
            for pair in artifact["claim"]["pairs"]
        )
    )


if __name__ == "__main__":
    main()
