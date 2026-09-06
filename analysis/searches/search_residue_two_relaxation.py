#!/usr/bin/env python3
"""Bounded exchange search for an n=17 strengthened 178-U relaxation witness.

This is deliberately not a global optimizer.  It exhausts one-for-one
exchanges from the selected fixed near patterns, then optionally explores a
bounded beam of a second sequential one-for-one exchange.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path

from analysis.searches.certify_residue_two_relaxation import (
    SCHEMA_V2,
    dual_edges,
    interval_measurements,
    make_certificate,
    rectangle_measurements,
    seam_measurements,
    singleton_measurements,
    verify,
    window_measurements,
)
from analysis.searches.search_residue_two_near import (
    NEAR_MACRO,
    NEAR_PHASECROP,
    NEAR_PUMP,
)

N = 17
U_COUNT = 178
SIDE = N - 1
FILTERS = ("scalar", "singleton", "interval", "rectangle", "seam", "window")
PATTERNS = {
    "macro": NEAR_MACRO,
    "phasecrop": NEAR_PHASECROP,
    "pump": NEAR_PUMP,
}


@dataclass
class Counts:
    generated: int = 0
    passed: dict[str, int] = field(default_factory=lambda: {name: 0 for name in FILTERS})

    def report(self, label: str) -> None:
        values = " ".join(f"{name}={self.passed[name]}" for name in FILTERS)
        print(f"{label}: generated={self.generated} {values}", flush=True)


@dataclass(frozen=True)
class NearCandidate:
    rank: tuple[int, int]
    bits: int
    edge_count: int
    origin: str
    exchanges: tuple[tuple[int, int], ...]


def rows_to_bits(rows: list[str]) -> int:
    return sum(
        1 << (row * N + column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "U"
    )


def bits_to_rows(bits: int) -> list[str]:
    return [
        "".join("U" if bits & (1 << (row * N + column)) else "." for column in range(N))
        for row in range(N)
    ]


def neighbor_count(bits: int, vertex: int) -> int:
    row, column = divmod(vertex, N)
    total = 0
    if row and bits & (1 << (vertex - N)):
        total += 1
    if row + 1 < N and bits & (1 << (vertex + N)):
        total += 1
    if column and bits & (1 << (vertex - 1)):
        total += 1
    if column + 1 < N and bits & (1 << (vertex + 1)):
        total += 1
    return total


def exchanged(bits: int, edge_count: int, removed: int, added: int) -> tuple[int, int]:
    without = bits & ~(1 << removed)
    child_edges = edge_count - neighbor_count(bits, removed) + neighbor_count(without, added)
    return without | (1 << added), child_edges


def violation_count(name: str, measurement: dict) -> int:
    if name == "interval":
        return sum(
            len(measurement[orientation]["violations"])
            for orientation in ("horizontal", "vertical")
        )
    return len(measurement["violations"])


def evaluate(bits: int, edge_count: int, counts: Counts) -> tuple[bool, tuple[int, int]]:
    counts.generated += 1
    # For fixed U=178, the exact run identity gives run_sum = 356 - edge_count.
    run_sum = 2 * U_COUNT - edge_count
    if edge_count < 256 or run_sum > 100:
        return False, (0, max(256 - edge_count, run_sum - 100))
    counts.passed["scalar"] += 1

    rows = bits_to_rows(bits)
    edges = dual_edges(rows)
    if len(edges) != edge_count:
        raise AssertionError("incremental dual edge count disagrees with recomputation")
    families = (
        ("singleton", lambda: singleton_measurements(edges, SIDE)),
        ("interval", lambda: interval_measurements(edges, SIDE)),
        ("rectangle", lambda: rectangle_measurements(edges, SIDE, 4)),
        ("seam", lambda: seam_measurements(edges, SIDE)),
        ("window", lambda: window_measurements(edges, SIDE)),
    )
    for index, (name, measure) in enumerate(families, start=1):
        failures = violation_count(name, measure())
        if failures:
            return False, (-index, failures)
        counts.passed[name] += 1
    return True, (-len(FILTERS), 0)


def write_verified_certificate(bits: int, output: Path, origin: str, exchanges: tuple[tuple[int, int], ...]) -> None:
    rows = bits_to_rows(bits)
    certificate = make_certificate(rows, level="window", max_rectangle_side=4)
    if certificate["schema"] != SCHEMA_V2 or not certificate["relaxation_feasible"]:
        raise AssertionError("candidate passed staged checks but failed complete certification")
    verify(certificate)
    output.write_text(json.dumps(certificate, indent=2) + "\n")
    verify(json.loads(output.read_text()))

    metrics = certificate["measurements"]
    print(f"FEASIBLE strengthened relaxation from {origin} exchanges={exchanges}")
    print("\n".join(rows))
    print(
        f"metrics: U={metrics['u_count']} dots={metrics['dot_count']} "
        f"runs={metrics['row_runs']}+{metrics['column_runs']}={metrics['run_sum']} "
        f"edges={metrics['dual_edge_count']}"
    )
    print(
        "post-pass global diagnostic: "
        f"rank={metrics['full_dual']['rank']}/256 "
        f"components={metrics['full_dual']['components']} "
        f"connected={certificate['global_dual_connected']}"
    )
    print(f"verified v2 certificate: {output}")


def one_exchange_search(
    selected: list[str], beam_width: int, output: Path
) -> tuple[bool, list[NearCandidate], set[int]]:
    counts = Counts()
    near = []
    seen_children: set[int] = set()
    for name in selected:
        bits = rows_to_bits(PATTERNS[name])
        if bits.bit_count() != U_COUNT:
            raise AssertionError(f"fixed near pattern {name} no longer has 178 U")
        edge_count = len(dual_edges(PATTERNS[name]))
        us = [vertex for vertex in range(N * N) if bits & (1 << vertex)]
        dots = [vertex for vertex in range(N * N) if not bits & (1 << vertex)]
        for removed in us:
            for added in dots:
                child, child_edges = exchanged(bits, edge_count, removed, added)
                feasible, rank = evaluate(child, child_edges, counts)
                seen_children.add(child)
                if feasible:
                    counts.report("one-for-one cumulative passes before success")
                    write_verified_certificate(child, output, name, ((removed, added),))
                    return True, [], seen_children
                near.append(NearCandidate(rank, child, child_edges, name, ((removed, added),)))

    expected = len(selected) * U_COUNT * (N * N - U_COUNT)
    if counts.generated != expected:
        raise AssertionError(f"one-for-one enumeration was incomplete: {counts.generated}/{expected}")
    print("one-for-one search exhaustively negative")
    counts.report("exact one-for-one candidate counts by cumulative filter")
    near.sort(key=lambda candidate: (candidate.rank, candidate.origin, candidate.exchanges))
    return False, near[:beam_width], seen_children


def two_exchange_beam(
    beam: list[NearCandidate], seen: set[int], maximum: int, output: Path
) -> bool:
    counts = Counts()
    for parent in beam:
        us = [vertex for vertex in range(N * N) if parent.bits & (1 << vertex)]
        dots = [vertex for vertex in range(N * N) if not parent.bits & (1 << vertex)]
        for removed in us:
            for added in dots:
                child, child_edges = exchanged(parent.bits, parent.edge_count, removed, added)
                if child in seen:
                    continue
                seen.add(child)
                feasible, _ = evaluate(child, child_edges, counts)
                if feasible:
                    counts.report("bounded second-hop cumulative passes before success")
                    write_verified_certificate(
                        child,
                        output,
                        parent.origin,
                        parent.exchanges + ((removed, added),),
                    )
                    return True
                if counts.generated >= maximum:
                    counts.report("bounded second-hop candidate counts")
                    print("second-hop beam stopped at its explicit non-exhaustive candidate bound")
                    return False
    counts.report("bounded second-hop candidate counts")
    print("second-hop beam exhausted all children of the retained beam only; search remains non-global")
    return False


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "Scope: exact one-for-one exchanges from fixed near patterns; optional "
            "bounded two-hop beam. This search is non-global and proves nothing "
            "outside the reported first-hop enumeration."
        ),
    )
    parser.add_argument(
        "--candidate",
        choices=("all", *PATTERNS),
        default="all",
        help="fixed starting pattern(s); default: all three",
    )
    parser.add_argument("--no-beam", action="store_true", help="stop after exhaustive first-hop search")
    parser.add_argument("--beam-width", type=int, default=8, help="first-hop states retained for hop two")
    parser.add_argument(
        "--beam-max-candidates",
        type=int,
        default=100_000,
        help="hard non-exhaustive bound on unique second-hop candidates",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/opencode/residue_two_relaxation_v2.json"),
    )
    args = parser.parse_args()
    if args.beam_width < 0 or args.beam_max_candidates < 1:
        parser.error("beam width must be nonnegative and beam candidate bound must be positive")

    selected = list(PATTERNS) if args.candidate == "all" else [args.candidate]
    print(
        "NON-GLOBAL bounded search: exhaustive one-for-one exchanges from "
        f"{','.join(selected)}; "
        + (
            "second hop disabled"
            if args.no_beam or args.beam_width == 0
            else f"non-exhaustive second-hop beam width={args.beam_width} "
            f"candidate_bound={args.beam_max_candidates}"
        ),
        flush=True,
    )
    found, beam, seen = one_exchange_search(selected, args.beam_width, args.output)
    if found:
        return
    if not args.no_beam and beam and two_exchange_beam(
        beam, seen, args.beam_max_candidates, args.output
    ):
        return
    raise SystemExit("no feasible candidate found within the explicitly bounded, non-global scope")


if __name__ == "__main__":
    main()
