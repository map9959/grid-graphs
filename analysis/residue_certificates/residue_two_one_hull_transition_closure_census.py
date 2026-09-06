#!/usr/bin/env python3
"""Exact finite-width census of reachable one-hull transition closure.

The silent-hull API can recognize and certify a proposed arbitrary word, but it
does not generate an arbitrary word's successor.  This census therefore makes
the strongest complete claim supported by the existing generator: exact row
BFS at residue-two widths up to the depth guard.  It does not claim global
arbitrary-width closure.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from analysis.residue_certificates.residue_two_silent_hull_language import (
    SilentHullAtom,
    classify_silent_hull_frontier,
    encode_silent_hull_frontier,
    finite_structural_atom_alphabet,
)
from analysis.residue_certificates.residue_two_stable_topology_certificate import (
    certify_silent_hull_symbolic_transition,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    render_mask,
)

SCHEMA = "grid-graphs.residue-two-one-hull-transition-closure-census.v1"
HARD_STATE_CAP = 100_000
HARD_TRANSITION_CAP = 1_000_000
HARD_DEPTH_GUARD = 12
ACTION_PACKETS = tuple(range(8))


@dataclass(frozen=True, order=True, slots=True)
class StructuralKey:
    """Canonical silent-hull state with affine counters deliberately omitted."""

    width: int
    row_index: int
    previous_cap_bits: tuple[int, int]
    left_face_role: str
    atoms: tuple[SilentHullAtom, ...]


def structural_key(state: FrontierState) -> StructuralKey:
    encoded = encode_silent_hull_frontier(state)
    return StructuralKey(
        encoded.width,
        encoded.row_index,
        encoded.previous_cap_bits,
        encoded.left_face_role,
        encoded.atoms,
    )


def _split_mask(mask: int, width: int) -> tuple[tuple[int, int], tuple[int, ...]]:
    return (
        (mask & 1, (mask >> (width - 1)) & 1),
        tuple(
            (mask >> (1 + 3 * packet_index)) & 7
            for packet_index in range((width - 2) // 3)
        ),
    )


def _action_masks(width: int):
    """Yield every row from the exact eight-symbol packet alphabet."""
    packet_length = (width - 2) // 3
    for packets in product(ACTION_PACKETS, repeat=packet_length):
        for left_cap, right_cap in product((0, 1), repeat=2):
            mask = left_cap | (right_cap << (width - 1))
            for index, packet in enumerate(packets):
                mask |= packet << (1 + 3 * index)
            yield mask


def _path(
    key: StructuralKey,
    parents: dict[StructuralKey, tuple[StructuralKey, int] | None],
) -> tuple[int, ...]:
    masks = []
    while parents[key] is not None:
        parent, mask = parents[key]  # type: ignore[misc]
        masks.append(mask)
        key = parent
    return tuple(reversed(masks))


def _state_record(state: FrontierState) -> dict:
    encoded = encode_silent_hull_frontier(state)
    return {
        "width": state.n,
        "row_index": state.row_index,
        "previous_cap_bits": list(encoded.previous_cap_bits),
        "left_face_role": encoded.left_face_role,
        "atoms": [repr(atom) for atom in encoded.atoms],
    }


def _replay_defect(width: int, masks: tuple[int, ...]) -> dict:
    """Replay from scratch and recertify every representable prefix edge."""
    state = initial_state(width)
    for index, mask in enumerate(masks):
        outgoing = advance_row(state, mask)
        if outgoing is None:
            raise AssertionError("reported closure defect replays as a sealed row")
        source_decision = classify_silent_hull_frontier(state)
        target_decision = classify_silent_hull_frontier(outgoing)
        if not source_decision.accepted or source_decision.encoded is None:
            raise AssertionError("reported defect prefix leaves the source language")
        if index + 1 < len(masks):
            if not target_decision.accepted or target_decision.encoded is None:
                raise AssertionError("reported defect occurs before its claimed row")
            caps, packets = _split_mask(mask, width)
            certify_silent_hull_symbolic_transition(
                source_decision.encoded, caps, packets, target_decision.encoded
            )
        else:
            if target_decision.accepted:
                raise AssertionError("reported closure defect target remains one-hull")
            return {
                "verified": True,
                "replayed_rows": len(masks),
                "target_maximum_face_cut_width": target_decision.maximum_face_cut_width,
                "target_reason": target_decision.reason,
            }
        state = outgoing
    raise AssertionError("a closure defect requires at least one row")


def run_census(
    *,
    state_cap: int = HARD_STATE_CAP,
    transition_cap: int = HARD_TRANSITION_CAP,
    depth_guard: int = HARD_DEPTH_GUARD,
) -> dict:
    if not 1 <= state_cap <= HARD_STATE_CAP:
        raise ValueError(f"state_cap must be in 1..{HARD_STATE_CAP}")
    if not 1 <= transition_cap <= HARD_TRANSITION_CAP:
        raise ValueError(f"transition_cap must be in 1..{HARD_TRANSITION_CAP}")
    if not 5 <= depth_guard <= HARD_DEPTH_GUARD:
        raise ValueError(f"depth_guard must be in 5..{HARD_DEPTH_GUARD}")

    widths = tuple(range(5, depth_guard + 1, 3))
    queue: deque[StructuralKey] = deque()
    states: dict[StructuralKey, FrontierState] = {}
    parents: dict[StructuralKey, tuple[StructuralKey, int] | None] = {}
    for width in widths:
        state = initial_state(width)
        key = structural_key(state)
        if len(states) == state_cap:
            return _report(
                "incomplete_due_to_cap", widths, state_cap, transition_cap,
                depth_guard, states, 0, 0, 0, 0, "state_cap", None,
            )
        states[key], parents[key] = state, None
        queue.append(key)

    expanded = transitions = sealed = certified = 0
    cap_hit: str | None = None
    defect: dict | None = None
    while queue:
        source_key = queue.popleft()
        source = states[source_key]
        if source.finished:
            continue
        if source.row_index >= depth_guard:
            cap_hit = "depth_guard"
            break
        expanded += 1
        for mask in _action_masks(source.n):
            if transitions == transition_cap:
                cap_hit = "transition_cap"
                break
            transitions += 1
            target = advance_row(source, mask)
            if target is None:
                sealed += 1
                continue
            decision = classify_silent_hull_frontier(target)
            if not decision.accepted:
                masks = (*_path(source_key, parents), mask)
                defect = {
                    "width": source.n,
                    "row": target.row_index,
                    "action_mask": mask,
                    "action_row": render_mask(mask, source.n),
                    "source": _state_record(source),
                    "shortest_representative_rows": [
                        render_mask(item, source.n) for item in masks
                    ],
                    "target_maximum_face_cut_width": decision.maximum_face_cut_width,
                    "target_reason": decision.reason,
                    "independent_replay": _replay_defect(source.n, masks),
                }
                break
            assert decision.encoded is not None
            caps, packets = _split_mask(mask, source.n)
            certify_silent_hull_symbolic_transition(
                encode_silent_hull_frontier(source), caps, packets, decision.encoded
            )
            certified += 1
            target_key = structural_key(target)
            if target_key in states:
                continue
            if len(states) == state_cap:
                cap_hit = "state_cap"
                break
            states[target_key] = target
            parents[target_key] = (source_key, mask)
            queue.append(target_key)
        if defect is not None or cap_hit is not None:
            break

    status = "closure_defect" if defect is not None else (
        "incomplete_due_to_cap" if cap_hit is not None else "closed"
    )
    return _report(
        status, widths, state_cap, transition_cap, depth_guard, states,
        expanded, transitions, sealed, certified, cap_hit, defect,
    )


def _report(
    status: str,
    widths: tuple[int, ...],
    state_cap: int,
    transition_cap: int,
    depth_guard: int,
    states: dict[StructuralKey, FrontierState],
    expanded: int,
    transitions: int,
    sealed: int,
    certified: int,
    cap_hit: str | None,
    defect: dict | None,
) -> dict:
    return {
        "schema": SCHEMA,
        "status": status,
        "coverage": {
            "kind": "complete-reachable-exact-fixed-width-census-unless-capped",
            "widths": list(widths),
            "finite_structural_atom_alphabet_available": True,
            "finite_structural_atom_alphabet_size": len(
                finite_structural_atom_alphabet()
            ),
            "arbitrary_symbolic_word_successor_generation_available": False,
            "arbitrary_width_closure_claimed": False,
            "action_packet_alphabet": list(ACTION_PACKETS),
            "action_packet_alphabet_size": len(ACTION_PACKETS),
            "row_actions": "all packet words over 0..7 and both binary cap bits",
        },
        "limits": {
            "state_cap": state_cap,
            "transition_cap": transition_cap,
            "depth_guard": depth_guard,
            "hard_state_cap": HARD_STATE_CAP,
            "hard_transition_cap": HARD_TRANSITION_CAP,
            "hard_depth_guard": HARD_DEPTH_GUARD,
            "cap_hit": cap_hit,
            "beam_or_lossy_pruning": None,
        },
        "counts": {
            "normalized_structural_states": len(states),
            "expanded_states": expanded,
            "transitions_examined": transitions,
            "sealed_actions": sealed,
            "one_hull_transitions_certified": certified,
        },
        "state_key": "canonical silent-hull structure; u_cost and cycle_excess excluded",
        "shortest_representatives": {"closure_defect": defect},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-cap", type=int, default=HARD_STATE_CAP)
    parser.add_argument("--transition-cap", type=int, default=HARD_TRANSITION_CAP)
    parser.add_argument("--depth-guard", type=int, default=HARD_DEPTH_GUARD)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        report = run_census(
            state_cap=args.state_cap,
            transition_cap=args.transition_cap,
            depth_guard=args.depth_guard,
        )
    except ValueError as error:
        parser.error(str(error))
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(rendered, end="")
    else:
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
