#!/usr/bin/env python3
"""Focused moving-boundary search for residue-two middle rows.

The language is deliberately local rather than a global optimizer.  For
``n=3k+2``, every mutable row is

    . L^a C R^(k-a-|C|) .

in packet notation, where ``1 <= |C| <= 5``.  In basic mode C is a word over
X/H; in phase mode it is a word over X/H/S, with S=.U.  The bound five is
derived below from all mutable rows of both frozen n=20 candidates and is then
used unchanged at every width.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    q_old_formula as q_formula,
)
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.searches.search_residue_two_middle import KNOWN_249_NEAR, KNOWN_250
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
from analysis._paths import ANALYSIS_ROOT, analysis_path, source_path


PHASE_ALPHABET = {**ROW_PACKET_ALPHABET, "S": ".U."}
RESULT_SCHEMA = "grid-graphs.residue-two-phase-front.v2"
DEFAULT_RESULT = analysis_path("search_residue_two_phase_front_result.json")
DEFAULT_WITNESS = analysis_path("residue_two_phase_front_witness.txt")


def _packet_names(row: str) -> str:
    inverse = {value: name for name, value in ROW_PACKET_ALPHABET.items()}
    try:
        return "".join(inverse[row[start : start + 3]] for start in range(1, len(row) - 1, 3))
    except KeyError as error:
        raise AssertionError(f"observed row is outside L/X/R/H packets: {row}") from error


def _central_width(word: str) -> int:
    left = len(word) - len(word.lstrip("L"))
    right = len(word) - len(word.rstrip("R"))
    center = word[left : len(word) - right if right else None]
    if not center or any(name not in "XH" for name in center):
        raise AssertionError(f"observed row is not L*(X|H)+R*: {word}")
    return len(center)


OBSERVED_MUTABLE_WORDS = tuple(
    dict.fromkeys(
        _packet_names(row)
        for rows in (KNOWN_250, KNOWN_249_NEAR)
        for row in rows[3:-2]
    )
)
MAX_CENTER_WIDTH = max(map(_central_width, OBSERVED_MUTABLE_WORDS))
if MAX_CENTER_WIDTH != 5:
    raise AssertionError(f"frozen candidates now derive central bound {MAX_CENTER_WIDTH}, expected 5")


def row_words(packet_count: int, mode: str = "basic") -> tuple[str, ...]:
    """Return the complete finite row domain in deterministic order."""
    if packet_count < 1:
        raise ValueError("packet count must be positive")
    center_alphabet = "XH" if mode == "basic" else "XHS" if mode == "phase" else None
    if center_alphabet is None:
        raise ValueError("mode must be 'basic' or 'phase'")
    words = []
    for width in range(1, min(MAX_CENTER_WIDTH, packet_count) + 1):
        for left in range(packet_count - width + 1):
            for ordinal in range(len(center_alphabet) ** width):
                value = ordinal
                center = []
                for _ in range(width):
                    center.append(center_alphabet[value % len(center_alphabet)])
                    value //= len(center_alphabet)
                words.append("L" * left + "".join(center) + "R" * (packet_count - left - width))
    return tuple(words)


def validate_language() -> None:
    domain = set(row_words(6, "basic"))
    missing = sorted(set(OBSERVED_MUTABLE_WORDS) - domain)
    if missing:
        raise AssertionError(f"derived language omitted observed rows: {missing}")


@dataclass(slots=True)
class Node:
    state: FrontierState
    masks: tuple[int, ...]
    ways: int = 1


@dataclass(frozen=True, slots=True)
class LayerStats:
    side: str
    row: int
    incoming_states: int
    packet_extensions: int
    live_transitions: int
    exact_states: int
    retained_states: int
    assignments_represented: int


@dataclass(frozen=True, slots=True)
class SearchResult:
    n: int
    target_u: int
    mode: str
    label: str
    conclusion: str
    beam: int | None
    split: int
    domain_size: int
    forward_states: int
    backward_states: int
    joined_pairs: int
    joined_assignment_pairs: int
    best_join: tuple[int, int] | None
    tied_best: int
    tied_best_assignment_pairs: int
    first_row_unconstrained_legal_rows: int | None
    witness: list[str] | None
    layers: tuple[LayerStats, ...]


def _cap_state(n: int, rows: Iterable[str]) -> Node:
    state = initial_state(n)
    masks = []
    for row in rows:
        mask = row_mask(row)
        child = advance_row(state, mask)
        if child is None:
            raise AssertionError("fixed affine cap sealed a dual component")
        state = child
        masks.append(mask)
    return Node(state, tuple(masks))


def _stream_phase_rows(
    incoming: FrontierState,
    packet_count: int,
    mode: str,
    u_bounds: tuple[int, int],
):
    """Stream the disjoint L*/center/R* decomposition without projection."""
    alphabet = ROW_PACKET_ALPHABET if mode == "basic" else PHASE_ALPHABET
    center = ("X", "H") if mode == "basic" else ("X", "H", "S")
    transitions = []
    attempted = 0
    for width in range(1, min(MAX_CENTER_WIDTH, packet_count) + 1):
        for left in range(packet_count - width + 1):
            domains = [("L",)] * left + [center] * width
            domains += [("R",)] * (packet_count - left - width)
            streamed, count = stream_row_packets(
                incoming,
                ".",
                ".",
                domains,
                packet_alphabet=alphabet,
                u_cost_bounds=u_bounds,
            )
            transitions.extend(streamed)
            attempted += count
    return transitions, attempted


def _rank(node: Node, desired_u: float) -> tuple:
    state = node.state
    out = state.partition[0]
    return (
        abs(state.u_cost - desired_u),
        len(set(state.partition)),
        sum(label != out for label in state.partition),
        state.cycle_excess,
        state.previous_u_mask,
        state.partition,
    )


def _expand(
    seed: Node,
    rows: int,
    other_rows: int,
    target_u: int,
    row_min: int,
    row_max: int,
    packet_count: int,
    mode: str,
    beam: int | None,
    side: str,
    total_fixed_u: int,
    mutable_rows: int,
    report: bool,
) -> tuple[list[Node], list[LayerStats]]:
    layer = [seed]
    stats = []
    side_min = max(rows * row_min, target_u - total_fixed_u - other_rows * row_max)
    side_max = min(rows * row_max, target_u - total_fixed_u - other_rows * row_min)
    seed_u = seed.state.u_cost
    for depth in range(rows):
        incoming_states = len(layer)
        remaining = rows - depth - 1
        exact: dict[FrontierState, Node] = {}
        attempted = live = 0
        for node in layer:
            lower_add = max(row_min, side_min - (node.state.u_cost - seed_u) - remaining * row_max)
            upper_add = min(row_max, side_max - (node.state.u_cost - seed_u) - remaining * row_min)
            if lower_add > upper_add:
                continue
            transitions, count = _stream_phase_rows(
                node.state,
                packet_count,
                mode,
                (node.state.u_cost + lower_add, node.state.u_cost + upper_add),
            )
            attempted += count
            live += len(transitions)
            for transition in transitions:
                old = exact.get(transition.outgoing)
                if old is None:
                    exact[transition.outgoing] = Node(
                        transition.outgoing, (*node.masks, transition.row_mask), node.ways
                    )
                else:
                    old.ways += node.ways
        exact_nodes = list(exact.values())
        desired_mutable = (target_u - total_fixed_u) * (depth + 1) / mutable_rows
        desired_u = seed_u + desired_mutable
        if beam is not None and len(exact_nodes) > beam:
            exact_nodes.sort(key=lambda node: _rank(node, desired_u))
            layer = exact_nodes[:beam]
        else:
            layer = exact_nodes
        item = LayerStats(
            side,
            depth + 1,
            incoming_states,
            attempted,
            live,
            len(exact),
            len(layer),
            sum(node.ways for node in layer),
        )
        stats.append(item)
        if report:
            print(
                f"{side}_row={depth + 1}/{rows} incoming={item.incoming_states} "
                f"packet_extensions={attempted} live={live} exact_states={len(exact)} "
                f"retained={len(layer)} assignments={item.assignments_represented}",
                flush=True,
            )
        if not layer:
            break
    return layer, stats


def search(
    n: int,
    target_u: int,
    *,
    mode: str = "basic",
    beam: int | None = None,
    split: int | None = None,
    report: bool = True,
) -> SearchResult:
    if n < 17 or n % 3 != 2:
        raise ValueError("n must be at least 17 and congruent to 2 mod 3")
    if target_u not in (q_formula(n), q_formula(n) + 1):
        raise ValueError("target must be q(n) or q(n)+1")
    if beam is not None and beam < 1:
        raise ValueError("beam must be positive or None for exact search")
    validate_language()
    affine = residue_two_affine_pattern(n)
    top_rows, bottom_rows = affine[:3], affine[-2:]
    mutable_rows = n - 5
    split = (mutable_rows + 1) // 2 if split is None else split
    if not 1 <= split < mutable_rows:
        raise ValueError(f"split must lie in 1..{mutable_rows - 1}")
    packet_count = (n - 2) // 3
    words = row_words(packet_count, mode)
    alphabet = ROW_PACKET_ALPHABET if mode == "basic" else PHASE_ALPHABET
    costs = [sum(alphabet[name].count("U") for name in word) for word in words]
    row_min, row_max = min(costs), max(costs)
    fixed_u = sum(row.count("U") for row in (*top_rows, *bottom_rows))
    if not fixed_u + mutable_rows * row_min <= target_u <= fixed_u + mutable_rows * row_max:
        raise ValueError("target is outside the phase-front language's U-count range")
    label = "EXACT bounded-language" if beam is None else f"BEAM-{beam} bounded-language"
    if report:
        print(
            f"{label}: n={n} target={target_u} mode={mode} packets={packet_count} "
            f"center_bound={MAX_CENTER_WIDTH} domain={len(words)} row_u={row_min}..{row_max}",
            flush=True,
        )

    backward_rows = mutable_rows - split
    forward, forward_stats = _expand(
        _cap_state(n, top_rows), split, backward_rows, target_u,
        row_min, row_max, packet_count, mode, beam, "forward", fixed_u,
        mutable_rows, report,
    )
    if forward:
        backward, backward_stats = _expand(
            _cap_state(n, reversed(bottom_rows)), backward_rows, split, target_u,
            row_min, row_max, packet_count, mode, beam, "backward", fixed_u,
            mutable_rows, report,
        )
    else:
        backward, backward_stats = [], []

    by_cost: dict[int, list[Node]] = defaultdict(list)
    bottom_fixed_u = sum(row.count("U") for row in bottom_rows)
    for node in backward:
        by_cost[node.state.u_cost - bottom_fixed_u].append(node)
    best_profile = None
    tied_best = joined = 0
    tied_best_assignment_pairs = joined_assignment_pairs = 0
    witness = None
    witness_profile = None
    for top in forward:
        needed = target_u - (top.state.u_cost + bottom_fixed_u)
        for bottom in by_cost[needed]:
            joined += 1
            represented_pairs = top.ways * bottom.ways
            joined_assignment_pairs += represented_pairs
            profile = merge_frontier_profile(top.state, bottom.state)
            if best_profile is None or profile < best_profile:
                best_profile, tied_best = profile, 1
                tied_best_assignment_pairs = represented_pairs
            elif profile == best_profile:
                tied_best += 1
                tied_best_assignment_pairs += represented_pairs
            if profile[0] != 1:
                continue
            masks = (*top.masks, *reversed(bottom.masks))
            rows = [render_mask(mask, n) for mask in masks]
            dual_ok, _, _ = dual_connectivity_check(rows)
            forest_ok, _ = forest_completion_check(rows)
            direct_edges = sum(
                row[column] == row[column + 1] == "U"
                for row in rows
                for column in range(n - 1)
            ) + sum(
                rows[row][column] == rows[row + 1][column] == "U"
                for row in range(n - 1)
                for column in range(n)
            )
            direct_cycles = direct_edges - (1 + (n - 1) ** 2) + 1
            if direct_cycles != profile[1]:
                raise AssertionError(
                    f"joined cycle excess {profile[1]} differs from direct {direct_cycles}"
                )
            if dual_ok and forest_ok and (
                witness_profile is None or profile < witness_profile
            ):
                witness = rows
                witness_profile = profile
    if report:
        print(
            f"join forward={len(forward)} backward={len(backward)} "
            f"deduplicated_state_pairs={joined} represented_assignment_pairs={joined_assignment_pairs} "
            f"best={best_profile} tied_best_state_pairs={tied_best} "
            f"tied_best_assignment_pairs={tied_best_assignment_pairs} "
            f"witness={witness is not None}",
            flush=True,
        )
    if witness is not None:
        dual_ok, connected, total = dual_connectivity_check(witness)
        forest_ok, reason = forest_completion_check(witness)
        actual_u = sum(row.count("U") for row in witness)
        if actual_u != target_u or not dual_ok or not forest_ok:
            raise AssertionError(
                f"full validation rejected retained witness: U={actual_u}/{target_u} "
                f"dual={connected}/{total} forest={forest_ok} reason={reason}"
            )
    first_row_unconstrained_legal_rows = None
    if witness is not None:
        conclusion = f"{label} POSITIVE"
    elif forward_stats and forward_stats[0].exact_states == 0:
        seed = _cap_state(n, top_rows)
        unconstrained, _ = _stream_phase_rows(
            seed.state,
            packet_count,
            mode,
            (seed.state.u_cost + row_min, seed.state.u_cost + row_max),
        )
        first_row_unconstrained_legal_rows = len(unconstrained)
        if first_row_unconstrained_legal_rows == 0:
            conclusion = "EXACT NEGATIVE: no legal first mutable row after the fixed top cap"
        else:
            conclusion = "EXACT NEGATIVE: no target-feasible legal first mutable row"
    elif beam is None:
        conclusion = "EXACT NEGATIVE in the bounded row language"
    else:
        conclusion = f"{label} NO RETAINED WITNESS"
    return SearchResult(
        n, target_u, mode, label, conclusion, beam, split, len(words), len(forward), len(backward),
        joined, joined_assignment_pairs, best_profile, tied_best, tied_best_assignment_pairs,
        first_row_unconstrained_legal_rows, witness, tuple((*backward_stats, *forward_stats)),
    )


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _rows_sha256(rows: Iterable[str]) -> str:
    return _sha256_bytes(("\n".join(rows) + "\n").encode("ascii"))


def provenance() -> dict:
    directory = ANALYSIS_ROOT
    files = {
        "generator_source": Path(__file__),
        "base_witness_source": source_path('search_residue_two_middle.py'),
        "frontier_kernel": source_path('tile_grammar.py'),
    }
    return {
        "known_250_rows_sha256": _rows_sha256(KNOWN_250),
        "known_249_near_rows_sha256": _rows_sha256(KNOWN_249_NEAR),
        "canonical_row_encoding": "ASCII rows joined by LF with one final LF",
        "source_files": {
            name: {"path": path.name, "sha256": _sha256_bytes(path.read_bytes())}
            for name, path in files.items()
        },
    }


def result_json(results: Iterable[SearchResult], *, output: dict | None = None) -> dict:
    serialized = []
    for result in results:
        item = asdict(result)
        item["best_join"] = list(result.best_join) if result.best_join is not None else None
        item["layers"] = [asdict(layer) for layer in result.layers]
        serialized.append(item)
    return {
        "schema": RESULT_SCHEMA,
        "provenance": provenance(),
        "scope": {
            "kind": "bounded width-independent row language; not global optimization",
            "row_rule": ". L^a C R^(k-a-|C|) .",
            "center_bound": MAX_CENTER_WIDTH,
            "basic_center_alphabet": ["X", "H"],
            "phase_center_alphabet": ["X", "H", "S"],
            "S": ".U.",
            "observed_mutable_words": list(OBSERVED_MUTABLE_WORDS),
            "all_observed_rows_in_basic_domain": True,
            "state_key": "full unprojected FrontierState",
            "join_counts": {
                "joined_pairs": "compatible pairs of deduplicated forward/backward FrontierState nodes",
                "tied_best": "best-profile pairs of deduplicated forward/backward FrontierState nodes",
                "joined_assignment_pairs": "sum of top.ways * bottom.ways over joined state pairs",
                "tied_best_assignment_pairs": "sum of top.ways * bottom.ways over tied-best state pairs",
            },
            "first_row_unconstrained_check": (
                "enumerates the complete declared row domain without target-feasibility pruning"
            ),
        },
        "searches": serialized,
        **({"output": output} if output is not None else {}),
    }


def _prior_result_owns_witness(result_path: Path, witness_path: Path) -> bool:
    """Recognize only a witness cryptographically tied to the paired prior result."""
    if not result_path.is_file() or not witness_path.is_file():
        return False
    try:
        record = json.loads(result_path.read_text())
        payload_hash = _sha256_bytes(witness_path.read_bytes())
        output = record.get("output", {}).get("witness", {})
        recorded_path = Path(output["path"])
        if not recorded_path.is_absolute():
            recorded_path = result_path.parent / recorded_path
        if (
            output.get("producer") == record.get("schema")
            and output.get("status") == "current"
            and recorded_path.resolve() == witness_path.resolve()
            and output.get("sha256") == payload_hash
        ):
            return True
        # Version 1 embedded the generated rows but did not record output metadata.
        searches = record.get("searches", [])
        return (
            record.get("schema") == "grid-graphs.residue-two-phase-front.v1"
            and len(searches) == 1
            and searches[0].get("witness") is not None
            and _rows_sha256(searches[0]["witness"]) == payload_hash
        )
    except (KeyError, OSError, TypeError, ValueError, json.JSONDecodeError):
        return False


def write_artifacts(result: SearchResult, result_path: Path, witness_path: Path) -> dict:
    try:
        recorded_witness_path = str(witness_path.resolve().relative_to(result_path.parent.resolve()))
    except ValueError:
        recorded_witness_path = str(witness_path.resolve())
    if result.witness is not None:
        witness_path.write_text("\n".join(result.witness) + "\n")
        witness_output = {
            "producer": RESULT_SCHEMA,
            "path": recorded_witness_path,
            "status": "current",
            "sha256": _sha256_bytes(witness_path.read_bytes()),
        }
    else:
        removed = _prior_result_owns_witness(result_path, witness_path)
        if removed:
            witness_path.unlink()
        witness_output = {
            "producer": RESULT_SCHEMA,
            "path": recorded_witness_path,
            "status": "removed_prior_generated" if removed else (
                "stale_unmanaged_not_current" if witness_path.exists() else "absent"
            ),
            "sha256": None,
        }
    rerun = {
        "n": result.n,
        "surplus": result.target_u - q_formula(result.n),
        "mode": result.mode,
        "beam": result.beam,
        "split": result.split,
    }
    record = result_json([result], output={"witness": witness_output, "rerun": rerun})
    result_path.write_text(json.dumps(record, indent=2) + "\n")
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=20)
    parser.add_argument("--surplus", type=int, choices=(0, 1), default=0)
    parser.add_argument("--mode", choices=("basic", "phase"), default="basic")
    parser.add_argument("--beam", type=int, help="omit for exact bounded-language search")
    parser.add_argument("--split", type=int)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--result", type=Path, default=DEFAULT_RESULT)
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    args = parser.parse_args()
    result = search(
        args.n, q_formula(args.n) + args.surplus, mode=args.mode, beam=args.beam,
        split=args.split, report=not args.quiet,
    )
    write_artifacts(result, args.result, args.witness)
    if result.witness is not None:
        print(f"{result.conclusion} witness={args.witness}")
    else:
        print(result.conclusion)
    print(f"result={args.result}")


if __name__ == "__main__":
    main()
