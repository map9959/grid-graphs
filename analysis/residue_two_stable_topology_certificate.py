#!/usr/bin/env python3
"""Finite topological transport certificates for the 19 stable affine rules.

The proof is a streaming product of the actual row graph and the claimed
outgoing compact partition.  It retains only OUT, the pending face on each
side of the cut, and the source/target one-carrier ports.  A component is
forgotten only when its actual and expected blocks close together; a retiring
old-only component is the rejection condition in ``advance_row``.

For L >= 7 a regular word is left[2], dominant^(L-6), right[4].  Each
certificate checks the fixed left part, a dominant-packet self-loop, and the
fixed right part.  Thus the result concerns exactly the generated affine
family's 19 stable rules, not the residue-two equality language.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations

from residue_two_affine_motif_grammar import BoundaryDefectAtom
from residue_two_compact_transition import ActionKey, ControlKey
from residue_two_silent_hull_language import (
    AffineRowCounters,
    SilentHullAtom,
    SilentHullFrontier,
    decode_silent_hull_frontier,
)
from residue_two_stable_counter_certificate import (
    boundary_values,
    stable_rule_certificates,
)


class TopologyCertificateError(ValueError):
    """Raised when a proposed finite topology certificate does not close."""


MAX_LIVE_ACTUAL_COMPONENTS = 7
MAX_LIVE_EXPECTED_COMPONENTS = 7


@dataclass(frozen=True, slots=True)
class CutState:
    """Canonical bounded product state at a packet cut."""

    previous_action_bit: int
    actual_components: tuple[tuple[tuple[str, ...], bool], ...]
    expected_components: tuple[tuple[str, ...], ...]
    incidence: tuple[tuple[int, int], ...]


@dataclass(frozen=True, slots=True)
class StableTopologyCertificate:
    source: ControlKey
    action: ActionKey
    target: ControlKey
    prefix_state: CutState
    loop_state: CutState
    final_state: CutState


class _DSU:
    def __init__(self) -> None:
        self.parent: dict[int, int] = {}
        self.next_node = 0

    def add(self) -> int:
        node = self.next_node
        self.next_node += 1
        self.parent[node] = node
        return node

    def find(self, node: int) -> int:
        parent = self.parent[node]
        if parent != node:
            self.parent[node] = self.find(parent)
        return self.parent[node]

    def union(self, left: int, right: int) -> None:
        left = self.find(left)
        right = self.find(right)
        if left != right:
            self.parent[right] = left


def _canonical_state(
    previous_bit: int,
    actual_attributes: dict[int, tuple[tuple[str, ...], bool]],
    expected_attributes: dict[int, tuple[str, ...]],
    incidence: set[tuple[int, int]],
) -> CutState:
    """Canonically label a tiny bipartite component graph."""
    actual = tuple(actual_attributes)
    expected = tuple(expected_attributes)
    best: tuple | None = None
    for actual_order in permutations(actual):
        ai = {value: index for index, value in enumerate(actual_order)}
        actual_values = tuple(actual_attributes[value] for value in actual_order)
        for expected_order in permutations(expected):
            ei = {value: index for index, value in enumerate(expected_order)}
            value = (
                actual_values,
                tuple(expected_attributes[item] for item in expected_order),
                tuple(sorted((ai[a], ei[e]) for a, e in incidence)),
            )
            if best is None or value < best:
                best = value
    assert best is not None
    return CutState(previous_bit, best[0], best[1], best[2])


class _StreamingProduct:
    def __init__(self, source: ControlKey, target: ControlKey) -> None:
        self.source = source
        self.target = target
        self.actual = _DSU()
        self.expected = _DSU()
        self.actual_out = self.actual.add()
        self.expected_out = self.expected.add()
        self.actual_old_nodes: set[int] = set()
        self.face_pairs: set[tuple[int, int]] = {
            (self.actual_out, self.expected_out)
        }
        self.actual_ports: dict[str, int] = {"OUT": self.actual_out}
        self.expected_ports: dict[str, int] = {"OUT": self.expected_out}
        self.source_carrier: int | None = None
        self.target_carrier: int | None = None
        self.pending_old = self.actual_out
        self.pending_new = self.actual_out
        self.pending_expected = self.expected_out
        self.previous_action_bit = 0

    def _new_old(self) -> int:
        node = self.actual.add()
        self.actual_old_nodes.add(node)
        return node

    def _new_face_pair(self) -> tuple[int, int]:
        actual = self.actual.add()
        expected = self.expected.add()
        self.face_pairs.add((actual, expected))
        return actual, expected

    def _left_faces(self) -> None:
        if self.source.left_face_role == "absent":
            old = self.actual_out
        else:
            old = self._new_old()
            if self.source.left_face_role == "out":
                self.actual.union(old, self.actual_out)
            elif self.source.left_face_role == "open":
                self.source_carrier = old
            elif self.source.left_face_role != "single":
                raise TopologyCertificateError("unknown source left-face role")

        if self.target.left_face_role == "absent":
            new, expected = self.actual_out, self.expected_out
        else:
            new, expected = self._new_face_pair()
            if self.target.left_face_role == "out":
                self.expected.union(expected, self.expected_out)
            elif self.target.left_face_role == "open":
                self.target_carrier = expected
            elif self.target.left_face_role != "single":
                raise TopologyCertificateError("unknown target left-face role")
        self._vertex(self.source.previous_cap_bits[0], self.action_left_bit, old, new, expected)

    @property
    def action_left_bit(self) -> int:
        return self._action_caps[0]

    def start(self, action_caps: tuple[int, int]) -> None:
        self._action_caps = action_caps
        self._left_faces()

    def _materialize_atom(
        self, atom: BoundaryDefectAtom | SilentHullAtom, *, source_side: bool
    ) -> tuple[int, int, int]:
        if len(atom.rooted_restriction) != 3:
            raise TopologyCertificateError("an open packet must contain three faces")
        dsu = self.actual if source_side else self.expected
        out = self.actual_out if source_side else self.expected_out
        active = self.source_carrier if source_side else self.target_carrier
        atom_roles = atom.roles if isinstance(atom, SilentHullAtom) else atom.carrier_roles
        roles = {role.local_label: role for role in atom_roles}
        silent = isinstance(atom, SilentHullAtom) and atom.silent_carry
        if silent and active is None:
            raise TopologyCertificateError("silent packet has no incoming carrier")
        local: dict[int, int] = {0: out}
        outgoing: int | None = active if silent else None
        nodes: list[int] = []
        for label in atom.rooted_restriction:
            if label not in local:
                if label not in roles:
                    raise TopologyCertificateError("packet component lacks a carrier role")
                role = roles[label]
                node = self._new_old() if source_side else dsu.add()
                if role.carries_in:
                    if active is None:
                        raise TopologyCertificateError("packet expects a missing carrier")
                    dsu.union(node, active)
                local[label] = node
                if role.carries_out:
                    if outgoing is not None and dsu.find(outgoing) != dsu.find(node):
                        raise TopologyCertificateError("packet has concurrent carriers")
                    outgoing = node
            nodes.append(local[label])
        if active is not None and not silent and not any(role.carries_in for role in roles.values()):
            raise TopologyCertificateError("incoming carrier disappears between packets")
        if source_side:
            self.source_carrier = outgoing
        else:
            self.target_carrier = outgoing
        return tuple(nodes)  # type: ignore[return-value]

    def packet(
        self,
        source_atom: BoundaryDefectAtom | SilentHullAtom,
        action_packet: int,
        target_atom: BoundaryDefectAtom | SilentHullAtom,
    ) -> None:
        if source_atom.previous_word < 0 or source_atom.previous_word >= 8:
            raise TopologyCertificateError("invalid source packet")
        old = (
            (self.actual_out,) * 3
            if self.source.left_face_role == "absent"
            else self._materialize_atom(source_atom, source_side=True)
        )
        if self.target.left_face_role == "absent":
            new = (self.actual_out,) * 3
            expected = (self.expected_out,) * 3
            if target_atom.rooted_restriction:
                raise TopologyCertificateError("terminal target has packet faces")
        else:
            expected = self._materialize_atom(target_atom, source_side=False)
            pairs = tuple(self._new_face_pair() for _ in range(3))
            new = tuple(pair[0] for pair in pairs)
            pair_expected = tuple(pair[1] for pair in pairs)
            for left, right in zip(pair_expected, expected):
                self.expected.union(left, right)
        for offset in range(3):
            self._vertex(
                (source_atom.previous_word >> offset) & 1,
                (action_packet >> offset) & 1,
                old[offset],
                new[offset],
                expected[offset],
            )

    def _vertex(
        self, previous_bit: int, action_bit: int, right_old: int, right_new: int, right_expected: int
    ) -> None:
        if previous_bit and action_bit:
            self.actual.union(self.pending_old, right_old)
        if self.previous_action_bit and action_bit:
            self.actual.union(self.pending_old, self.pending_new)
        self.pending_old = right_old
        self.pending_new = right_new
        self.pending_expected = right_expected
        self.previous_action_bit = action_bit

    def _cut_state(self, *, final: bool = False) -> CutState:
        if final:
            self.actual_ports = {"OUT": self.actual_out}
            self.expected_ports = {"OUT": self.expected_out}
        else:
            self.actual_ports = {
                "OUT": self.actual_out,
                "old-boundary": self.pending_old,
                "new-boundary": self.pending_new,
            }
            self.expected_ports = {
                "OUT": self.expected_out,
                "new-boundary": self.pending_expected,
            }
            if self.source_carrier is not None:
                self.actual_ports["source-carrier"] = self.source_carrier
            if self.target_carrier is not None:
                self.expected_ports["target-carrier"] = self.target_carrier

        a_roots = {self.actual.find(node) for node in self.actual.parent}
        e_roots = {self.expected.find(node) for node in self.expected.parent}
        live_a = {self.actual.find(node) for node in self.actual_ports.values()}
        live_e = {self.expected.find(node) for node in self.expected_ports.values()}
        relation = {
            (self.actual.find(a), self.expected.find(e)) for a, e in self.face_pairs
        }
        neighbors_a = {a: {e for aa, e in relation if aa == a} for a in a_roots}
        neighbors_e = {e: {a for a, ee in relation if ee == e} for e in e_roots}

        # Actual output components can merge but never split.  Once one actual
        # component contains faces claimed for two distinct target blocks, no
        # suffix can repair the mismatch.  Conversely, several actual blocks
        # may still merge into one expected block only while every block reaches
        # a physical cut port.
        if any(len(expected) > 1 for expected in neighbors_a.values()):
            raise TopologyCertificateError("actual output merges expected components")
        if any(
            len(actual) > 1 and not actual <= live_a
            for actual in neighbors_e.values()
        ):
            raise TopologyCertificateError("closed actual components cannot merge later")

        # A block remains live when either its actual row component or its
        # claimed output component reaches the packet cut.  Closing only one
        # side would discard the incidence needed to compare a later merge.
        while True:
            next_a = live_a | {a for a, e in relation if e in live_e}
            next_e = live_e | {e for a, e in relation if a in live_a}
            if next_a == live_a and next_e == live_e:
                break
            live_a, live_e = next_a, next_e
        if len(live_a) > MAX_LIVE_ACTUAL_COMPONENTS or len(live_e) > MAX_LIVE_EXPECTED_COMPONENTS:
            raise AssertionError("normalized packet-cut state exceeded its fixed component bound")
        old_roots = {self.actual.find(node) for node in self.actual_old_nodes}

        for root in a_roots - live_a:
            neighbors = neighbors_a[root]
            if not neighbors:
                if root in old_roots:
                    raise TopologyCertificateError("an old component is sealed")
                raise TopologyCertificateError("actual output component has no expected block")
            if len(neighbors) != 1:
                raise TopologyCertificateError("actual output merges expected components")
            expected = next(iter(neighbors))
            if expected in live_e or neighbors_e[expected] != {root}:
                raise TopologyCertificateError("actual and expected components close differently")
        for root in e_roots - live_e:
            neighbors = neighbors_e[root]
            if len(neighbors) != 1:
                raise TopologyCertificateError("expected output merges actual components")
            actual = next(iter(neighbors))
            if actual in live_a or neighbors_a[actual] != {root}:
                raise TopologyCertificateError("actual and expected components close differently")

        kept_relation = {(a, e) for a, e in relation if a in live_a and e in live_e}
        if any((a in live_a) != (e in live_e) for a, e in relation):
            raise TopologyCertificateError("one side of an output block closes early")
        actual_attributes = {
            root: (
                tuple(sorted(name for name, node in self.actual_ports.items() if self.actual.find(node) == root)),
                root in old_roots,
            )
            for root in live_a
        }
        expected_attributes = {
            root: tuple(sorted(name for name, node in self.expected_ports.items() if self.expected.find(node) == root))
            for root in live_e
        }
        state = _canonical_state(
            self.previous_action_bit, actual_attributes, expected_attributes, kept_relation
        )
        self._rebuild(live_a, live_e, kept_relation, old_roots)
        return state

    def _rebuild(
        self, live_a: set[int], live_e: set[int], relation: set[tuple[int, int]], old_roots: set[int]
    ) -> None:
        old_actual, old_expected = self.actual, self.expected
        self.actual, self.expected = _DSU(), _DSU()
        amap = {root: self.actual.add() for root in live_a}
        emap = {root: self.expected.add() for root in live_e}
        self.actual_old_nodes = {amap[root] for root in live_a & old_roots}
        self.face_pairs = {(amap[a], emap[e]) for a, e in relation}
        self.actual_ports = {
            name: amap[old_actual.find(node)] for name, node in self.actual_ports.items()
        }
        self.expected_ports = {
            name: emap[old_expected.find(node)] for name, node in self.expected_ports.items()
        }
        self.actual_out = self.actual_ports["OUT"]
        self.expected_out = self.expected_ports["OUT"]
        self.pending_old = self.actual_ports.get("old-boundary", self.actual_out)
        self.pending_new = self.actual_ports.get("new-boundary", self.actual_out)
        self.pending_expected = self.expected_ports.get("new-boundary", self.expected_out)
        self.source_carrier = self.actual_ports.get("source-carrier")
        self.target_carrier = self.expected_ports.get("target-carrier")

    def checkpoint(self) -> CutState:
        return self._cut_state()

    def finish(self, source_right_bit: int, action_right_bit: int) -> CutState:
        self._vertex(source_right_bit, action_right_bit, self.actual_out, self.actual_out, self.expected_out)
        if self.source_carrier is not None or self.target_carrier is not None:
            raise TopologyCertificateError("carrier remains open after the final packet")
        return self._cut_state(final=True)


def _validate_controls(source: ControlKey, action: ActionKey, target: ControlKey) -> None:
    if source.size_regime != "stable" or target.size_regime != "stable":
        raise TopologyCertificateError("stable topology certificates require stable controls")
    if target.row_phase != (source.row_phase + 1) % 3:
        raise TopologyCertificateError("target row phase is not the successor phase")
    successors = {
        "top": {"bulk"},
        "bulk": {"bulk", "bottom"},
        "bottom": {"closed"},
    }
    if source.cap_mode not in successors or target.cap_mode not in successors[source.cap_mode]:
        raise TopologyCertificateError("source and target cap modes are not consecutive")
    if (source.left_face_role == "absent") != (source.cap_mode == "top"):
        raise TopologyCertificateError("source face presence disagrees with its cap mode")
    if (target.left_face_role == "absent") != (target.cap_mode == "closed"):
        raise TopologyCertificateError("target face presence disagrees with its cap mode")
    if target.previous_cap_bits != action.cap_bits:
        raise TopologyCertificateError("target cap bits differ from the action")


def certify_topology(
    source: ControlKey, action: ActionKey, target: ControlKey
) -> StableTopologyCertificate:
    """Prove one regular stable rule by a finite prefix/loop/suffix product."""
    _validate_controls(source, action, target)
    source_left, source_right = boundary_values(
        source.dominant, tuple((item.endpoint, item.atom) for item in source.exceptions)
    )
    action_left, action_right = boundary_values(action.dominant_packet, action.exceptions)
    target_left, target_right = boundary_values(
        target.dominant, tuple((item.endpoint, item.atom) for item in target.exceptions)
    )
    for packet, atom in zip((*action_left, action.dominant_packet, *action_right), (*target_left, target.dominant, *target_right)):
        if atom.previous_word != packet:
            raise TopologyCertificateError("target previous-row packet differs from the action")

    product = _StreamingProduct(source, target)
    product.start(action.cap_bits)
    for values in zip(source_left, action_left, target_left):
        product.packet(*values)
    prefix = product.checkpoint()
    product.packet(source.dominant, action.dominant_packet, target.dominant)
    loop = product.checkpoint()
    if loop != prefix:
        raise TopologyCertificateError("dominant packet is not a normalized cut-state self-loop")
    for values in zip(source_right, action_right, target_right):
        product.packet(*values)
    final = product.finish(source.previous_cap_bits[1], action.cap_bits[1])
    if not (
        final.previous_action_bit == action.cap_bits[1]
        and len(final.actual_components) == 1
        and final.actual_components[0][0] == ("OUT",)
        and final.expected_components == (("OUT",),)
        and final.incidence == ((0, 0),)
    ):
        raise TopologyCertificateError("right suffix does not close to the target partition")
    return StableTopologyCertificate(source, action, target, prefix, loop, final)


def stable_topology_certificates() -> tuple[StableTopologyCertificate, ...]:
    certificates = tuple(
        certify_topology(item.source, item.action, item.target)
        for item in stable_rule_certificates()
    )
    if len(certificates) != 19:
        raise AssertionError(f"expected 19 stable topology certificates, got {len(certificates)}")
    return certificates


def _valid_final_state(final: CutState, action_right_bit: int) -> bool:
    return (
        final.previous_action_bit == action_right_bit
        and len(final.actual_components) == 1
        and final.actual_components[0][0] == ("OUT",)
        and final.expected_components == (("OUT",),)
        and final.incidence == ((0, 0),)
    )


def certify_silent_hull_symbolic_transition(
    source: SilentHullFrontier,
    action_cap_bits: tuple[int, int],
    action_packets: tuple[int, ...],
    target: SilentHullFrontier,
) -> AffineRowCounters:
    """Certify a one-hull row transition with a bounded streaming product.

    Unlike ``certify_silent_hull_transition``, this function does not call
    ``advance_row``.  Topology is checked packet by packet, while all counters
    are derived from local bits and the source/target component counts.
    """
    if source.packet_length != target.packet_length or len(action_packets) != source.packet_length:
        raise TopologyCertificateError("source, action, and target packet lengths differ")
    if source.row_index >= source.width:
        raise TopologyCertificateError("source frontier is already terminal")
    if target.row_index != source.row_index + 1:
        raise TopologyCertificateError("target row is not the successor row")
    if (source.left_face_role == "absent") != (source.row_index == 0):
        raise TopologyCertificateError("source face presence disagrees with its row")
    if (target.left_face_role == "absent") != (target.row_index == target.width):
        raise TopologyCertificateError("target face presence disagrees with its row")
    if len(action_cap_bits) != 2 or any(type(bit) is not int or bit not in (0, 1) for bit in action_cap_bits):
        raise TopologyCertificateError("action cap bits must be bits")
    if any(type(packet) is not int or not 0 <= packet < 8 for packet in action_packets):
        raise TopologyCertificateError("action packet is not a three-bit word")
    if target.previous_cap_bits != action_cap_bits or tuple(
        atom.previous_word for atom in target.atoms
    ) != action_packets:
        raise TopologyCertificateError("target previous-row word differs from the action")

    product = _StreamingProduct(source, target)  # type: ignore[arg-type]
    product.start(action_cap_bits)
    for source_atom, action_packet, target_atom in zip(
        source.atoms, action_packets, target.atoms
    ):
        product.packet(source_atom, action_packet, target_atom)
        product.checkpoint()
    final = product.finish(source.previous_cap_bits[1], action_cap_bits[1])
    if not _valid_final_state(final, action_cap_bits[1]):
        raise TopologyCertificateError("silent-hull word does not close to the claimed target")

    incoming = decode_silent_hull_frontier(source)
    outgoing = decode_silent_hull_frontier(target)
    bits = (
        action_cap_bits[0],
        *(bit for packet in action_packets for bit in (
            packet & 1, (packet >> 1) & 1, (packet >> 2) & 1
        )),
        action_cap_bits[1],
    )
    previous_bits = tuple(
        (incoming.previous_u_mask >> index) & 1 for index in range(incoming.n)
    )
    u = sum(bits)
    horizontal = sum(left * right for left, right in zip(bits, bits[1:]))
    vertical = sum(left * right for left, right in zip(previous_bits, bits))
    source_components = len(set(incoming.partition)) - 1
    target_components = len(set(outgoing.partition)) - 1
    new_faces = 0 if outgoing.row_index == outgoing.n else outgoing.n - 1
    rank = new_faces + source_components - target_components
    cycles = horizontal + vertical - rank
    counters = AffineRowCounters(
        len(action_packets), u, horizontal, vertical, source_components,
        target_components, rank, cycles, 3 * u - 2 * rank - 1,
    )
    if target.u_cost != source.u_cost + u:
        raise TopologyCertificateError("target U counter differs from the local action count")
    if target.cycle_excess != source.cycle_excess + cycles:
        raise TopologyCertificateError("target cycle counter differs from local topology")
    return counters


__all__ = [
    "CutState",
    "MAX_LIVE_ACTUAL_COMPONENTS",
    "MAX_LIVE_EXPECTED_COMPONENTS",
    "StableTopologyCertificate",
    "TopologyCertificateError",
    "certify_topology",
    "certify_silent_hull_symbolic_transition",
    "stable_topology_certificates",
]
