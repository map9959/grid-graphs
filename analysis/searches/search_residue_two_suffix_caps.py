#!/usr/bin/env python3
"""Exhaust three exact two-row cap languages after the n=20 basic corridor.

The prefix is every exact target-249 frontier state after row 17 from the
declared 14-packet suffix corridor. Rows 18 and 19 range over all 20-bit masks
with U-count distributions (19,1), (18,2), and (17,3). This is a bounded cap
language search, not a global optimization.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from itertools import combinations
from pathlib import Path

from analysis.patterns.construction_lab import forest_completion_check, run_check
from analysis.searches.search_residue_two_suffix_corridor import (
    LAST_MUTABLE_ROW,
    MUTABLE_PACKET_COLUMNS,
    N,
    PACKET_COUNT,
    PathNode,
    TARGET_U,
    _add_candidate,
    _reconstruct,
    exact_state_key,
    known_250_sha256,
    layer_after_row17,
)
from analysis.tiles.tile_grammar import FrontierState, advance_row
from analysis._paths import ANALYSIS_ROOT, analysis_path, source_path


DISTRIBUTIONS = ((19, 1), (18, 2), (17, 3))
DEFAULT_WITNESS = analysis_path("residue_two_suffix_caps_witness.txt")
DEFAULT_CERTIFICATE = analysis_path("residue_two_suffix_caps_result.json")


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def provenance() -> dict:
    directory = ANALYSIS_ROOT
    paths = {
        "generator": Path(__file__),
        "corridor_search": source_path('search_residue_two_suffix_corridor.py'),
        "base_pattern_source": source_path('search_residue_two_middle.py'),
        "frontier_kernel": source_path('tile_grammar.py'),
    }
    return {
        "known_250_rows_sha256": known_250_sha256(),
        "source_files": {
            name: {"path": path.name, "sha256": _sha256_file(path)}
            for name, path in paths.items()
        },
    }


@dataclass(frozen=True, slots=True)
class DistributionStats:
    row18_u: int
    row19_u: int
    row18_masks_attempted: int
    row18_transitions_attempted: int
    row18_live: int
    row18_exact_states: int
    row18_assignment_multiplicity: int
    row19_masks: int
    row19_pairs_attempted: int
    row19_pairs_live: int
    row19_pairs_accepted: int
    row19_exact_states: int
    row19_live_assignment_multiplicity: int
    accepted_exact_states: int
    accepted_assignment_multiplicity: int


@dataclass(frozen=True, slots=True)
class SearchResult:
    witness: list[str] | None
    distributions: list[DistributionStats]
    corridor_exact_states: int
    corridor_assignment_multiplicity: int

    @property
    def found(self) -> bool:
        return self.witness is not None


def masks_with_u_count(count: int) -> tuple[int, ...]:
    """Enumerate each width-20 mask of the requested cost exactly once."""

    if not 0 <= count <= N:
        raise ValueError("U count must fit the row width")
    return tuple(sum(1 << column for column in columns) for columns in combinations(range(N), count))


def _accepted_final_states(
    layer: dict[FrontierState, PathNode],
) -> dict[FrontierState, PathNode]:
    accepted = {}
    for state, node in layer.items():
        rows = _reconstruct(node)
        forest_ok, _ = forest_completion_check(rows)
        if state.u_cost == TARGET_U and forest_ok:
            accepted[state] = node
    return accepted


def search(*, report: bool = True) -> SearchResult:
    corridor, _ = layer_after_row17(target_u=TARGET_U, report=report)
    if any(state.row_index != LAST_MUTABLE_ROW + 1 or state.u_cost != 229 for state in corridor):
        raise AssertionError("corridor layer is not the exact row-17, cost-229 frontier")

    witness = None
    results = []
    for row18_u, row19_u in DISTRIBUTIONS:
        row18_masks = masks_with_u_count(row18_u)
        row18: dict[FrontierState, PathNode] = {}
        row18_live = 0
        for parent in corridor.values():
            for mask in row18_masks:
                child = advance_row(parent.state, mask)
                if child is None:
                    continue
                row18_live += 1
                _add_candidate(row18, child, parent, mask)

        row19_masks = masks_with_u_count(row19_u)
        final: dict[FrontierState, PathNode] = {}
        final_pair_counts: dict[FrontierState, int] = {}
        row19_live = 0
        for parent in row18.values():
            for mask in row19_masks:
                child = advance_row(parent.state, mask)
                if child is None:
                    continue
                row19_live += 1
                key = exact_state_key(child)
                final_pair_counts[key] = final_pair_counts.get(key, 0) + 1
                _add_candidate(final, child, parent, mask)

        accepted = _accepted_final_states(final)
        accepted_pairs = sum(final_pair_counts[state] for state in accepted)

        if witness is None and accepted:
            witness = _reconstruct(next(iter(accepted.values())))

        stats = DistributionStats(
            row18_u=row18_u,
            row19_u=row19_u,
            row18_masks_attempted=len(row18_masks),
            row18_transitions_attempted=len(corridor) * len(row18_masks),
            row18_live=row18_live,
            row18_exact_states=len(row18),
            row18_assignment_multiplicity=sum(node.ways for node in row18.values()),
            row19_masks=len(row19_masks),
            row19_pairs_attempted=len(row18) * len(row19_masks),
            row19_pairs_live=row19_live,
            row19_pairs_accepted=accepted_pairs,
            row19_exact_states=len(final),
            row19_live_assignment_multiplicity=sum(node.ways for node in final.values()),
            accepted_exact_states=len(accepted),
            accepted_assignment_multiplicity=sum(node.ways for node in accepted.values()),
        )
        results.append(stats)
        if report:
            print(
                f"distribution=({row18_u},{row19_u}) "
                f"row18_masks={stats.row18_masks_attempted} "
                f"row18_transitions={stats.row18_transitions_attempted} "
                f"row18_live={stats.row18_live} row18_exact={stats.row18_exact_states} "
                f"row18_assignments={stats.row18_assignment_multiplicity} "
                f"row19_pairs={stats.row19_pairs_attempted} "
                f"row19_live={stats.row19_pairs_live} "
                f"row19_accepted={stats.row19_pairs_accepted} "
                f"row19_exact={stats.row19_exact_states} "
                f"row19_assignments={stats.row19_live_assignment_multiplicity} "
                f"accepted_assignments={stats.accepted_assignment_multiplicity}",
                flush=True,
            )

    if witness is not None:
        forest_ok, reason = forest_completion_check(witness)
        if not forest_ok:
            raise AssertionError(f"independent forest check rejected witness: {reason}")
        info = run_check(N, witness, verbose=report)
        if not info["all_ok"]:
            raise AssertionError(f"independent run_check rejected witness: {info}")

    return SearchResult(
        witness,
        results,
        len(corridor),
        sum(node.ways for node in corridor.values()),
    )


def certificate(result: SearchResult) -> dict:
    return {
        "schema": "grid-graphs.residue-two-suffix-caps.v1",
        "exact": True,
        "provenance": provenance(),
        "scope": {
            "search_kind": "bounded_cap_language_not_global_optimization",
            "base": "search_residue_two_middle.KNOWN_250",
            "n": N,
            "target_u": TARGET_U,
            "fixed_rows": [[0, 10]],
            "corridor_mutable_rows": [11, LAST_MUTABLE_ROW],
            "corridor_mutable_packet_columns": list(MUTABLE_PACKET_COLUMNS),
            "corridor_mutable_packets": 2 * (LAST_MUTABLE_ROW - 10),
            "corridor_packet_count_per_row": PACKET_COUNT,
            "corridor_alphabet": ["L", "X", "R", "H"],
            "cap_rows": [18, 19],
            "cap_mask_width": N,
            "cap_u_count_distributions": [list(item) for item in DISTRIBUTIONS],
            "cap_masks": "all masks of each declared exact row U count",
            "deduplication_key": "full FrontierState",
            "path_multiplicities_retained": True,
            "predecessor_retained_for_reconstruction": True,
            "beam": None,
            "state_cap": None,
            "partition_projection": None,
        },
        "result": "positive" if result.found else "negative",
        "corridor_after_row17": {
            "exact_states": result.corridor_exact_states,
            "assignment_multiplicity": result.corridor_assignment_multiplicity,
        },
        "distributions": [asdict(item) for item in result.distributions],
        "witness": result.witness,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true", help="suppress progress")
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    args = parser.parse_args()

    result = search(report=not args.quiet)
    args.certificate.write_text(json.dumps(certificate(result), indent=2) + "\n")
    if result.witness is None:
        print("EXACT NEGATIVE: no target-249 witness in the three declared cap distributions.")
    else:
        args.witness.write_text("\n".join(result.witness) + "\n")
        print("EXACT POSITIVE")
        print("\n".join(result.witness))
        print(f"witness={args.witness}")
    print(f"certificate={args.certificate}")


if __name__ == "__main__":
    main()
