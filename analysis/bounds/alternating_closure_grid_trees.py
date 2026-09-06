#!/usr/bin/env python3
"""Finite one-copy grouped-hull census for square-grid spanning trees.

The executable layer builds the shared cotree-dual ancestor hull.  Its Hall
sources are used roots plus branch-excess slots (and outer collisions), not the
private collision leaves used by the historical approximation.  Lean's
``equivOfCardEq`` contour-to-spatial-gap choice is noncomputable, so every
componentwise occurrence-to-gap bijection is audited.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import time
from dataclasses import asdict, dataclass
from itertools import combinations, permutations, product
from typing import Iterable, Sequence

from analysis.bounds.cotree_row_charge import (
    Edge,
    UnionFind,
    grid_edges,
    is_tree,
    random_spanning_tree,
    spanning_trees,
)

NORTH, EAST, SOUTH, WEST = range(4)
OUT = -1
AXES = ("rows", "columns")
Vertex = int
Slot = tuple[Vertex, int]
Face = int
Resource = tuple[str, object]


@dataclass(frozen=True, order=True)
class Demand:
    kind: str
    index: int
    vertex: Vertex
    side: int


@dataclass(frozen=True, order=True)
class Source:
    """An occurrence-labelled repeated carrier contact."""

    token_rank: int
    demand: Demand
    component: int


@dataclass(frozen=True, order=True)
class SpatialGap:
    component: int
    previous: Source
    current: Source
    transition: Edge


@dataclass(frozen=True, order=True)
class GroupedSource:
    """One physical obligation in the root-plus-branch Euler ledger."""

    kind: str
    index: int
    label: object


@dataclass(frozen=True)
class Owner:
    kind: str
    label: object
    seed_faces: tuple[Face, ...]


@dataclass(frozen=True, order=True)
class ComponentContact:
    """A tree edge from a free component to cotree support."""

    edge: Edge
    faces: tuple[Face, Face]


@dataclass(frozen=True)
class FullPrunedModel:
    n: int
    axis: str
    tree: tuple[Edge, ...]
    contour: tuple[Slot, ...]
    reached_exit_ports: tuple[Resource, ...]
    tokens: tuple[Source, ...]
    collisions: tuple[Source, ...]
    residual_resources: frozenset[Resource]
    reserved_owner: dict[Resource, Owner]
    source_seed_faces: dict[Source, tuple[Face, ...]]
    face_parent: dict[Face, Face | None]
    face_resources: dict[Face, frozenset[Resource]]
    components: dict[int, tuple[Vertex, ...]]
    component_contacts: dict[int, tuple[ComponentContact, ...]]
    cotree: tuple[Edge, ...]
    fundamental_exchanges: dict[Edge, tuple[Edge, ...]]
    marked_slots: frozenset[Slot]
    collision_merger_slots: dict[Source, Slot]
    outer_boundary: tuple[Node, ...]
    outer_occurrence_resources: dict[int, Resource]
    resource_outer_occurrences: dict[Resource, tuple[int, ...]]


Node = tuple[str, object]


@dataclass(frozen=True)
class GroupedHullModel:
    base: FullPrunedModel
    occurrence_to_gap: dict[Source, SpatialGap]
    sources: tuple[GroupedSource, ...]
    source_seeds: dict[GroupedSource, Node]
    parent: dict[Node, Node | None]
    hull_nodes: frozenset[Node]
    root_reverse_seeds: dict[GroupedSource, Node]


@dataclass(frozen=True)
class HallFailure:
    source_indices: tuple[int, ...]
    sources: tuple[object, ...]
    neighborhood: tuple[Resource, ...]
    displaced_owners: tuple[Owner, ...]


@dataclass(frozen=True)
class GapChoiceFailure:
    occurrence_to_gap: tuple[tuple[Source, SpatialGap], ...]
    failure: HallFailure


@dataclass(frozen=True)
class TreeAudit:
    n: int
    axis: str
    source_count: int
    residual_count: int
    hall_failure: HallFailure | None
    closed_region_failure: HallFailure | None
    direct_hall_failure: HallFailure | None
    gap_choice_count: int
    hall_holds_for_all_gap_choices: bool
    hall_holds_for_some_gap_choices: bool
    first_failing_gap_choice: GapChoiceFailure | None
    gap_choice_total: int
    gap_choice_mode: str
    hall_method: str


def _edge(a: Vertex, b: Vertex) -> Edge:
    return tuple(sorted((a, b)))


def _neighbor(n: int, vertex: Vertex, direction: int) -> Vertex | None:
    row, column = divmod(vertex, n)
    dr, dc = ((-1, 0), (0, 1), (1, 0), (0, -1))[direction]
    row, column = row + dr, column + dc
    return row * n + column if 0 <= row < n and 0 <= column < n else None


def expanded_successor(n: int, tree: frozenset[Edge], slot: Slot) -> Slot:
    vertex, direction = slot
    target = _neighbor(n, vertex, direction)
    if target is not None and _edge(vertex, target) in tree:
        return target, ((direction + 2) % 4 + 1) % 4
    return vertex, (direction + 1) % 4


def expanded_contour(n: int, tree: frozenset[Edge], anchor: Slot = (0, NORTH)) -> tuple[Slot, ...]:
    result = []
    seen = set()
    slot = anchor
    while slot not in seen:
        seen.add(slot)
        result.append(slot)
        slot = expanded_successor(n, tree, slot)
    if slot != anchor or len(result) != 4 * n * n:
        raise AssertionError("expanded contour is not the Lean one-cycle normal form")
    return tuple(result)


def canonical_demands(n: int, axis: str) -> tuple[Demand, ...]:
    if axis == "rows":
        main = tuple(Demand("row", row, row * n, WEST) for row in range(n))
        corners = (
            Demand("corner", 0, n - 1, NORTH),
            Demand("corner", 1, n * n - 1, EAST),
            Demand("corner", 2, n * (n - 1), SOUTH),
        )
    elif axis == "columns":
        main = tuple(Demand("column", column, column, NORTH) for column in range(n))
        corners = (
            Demand("corner", 0, n - 1, EAST),
            Demand("corner", 1, n * n - 1, SOUTH),
            Demand("corner", 2, n * (n - 1), WEST),
        )
    else:
        raise ValueError(f"unknown axis: {axis}")
    return main + corners


def _support_and_components(
    n: int, tree: frozenset[Edge]
) -> tuple[frozenset[Vertex], dict[Vertex, int], dict[int, tuple[Vertex, ...]]]:
    cotree = tuple(edge for edge in grid_edges(n) if edge not in tree)
    support = frozenset(vertex for edge in cotree for vertex in edge)
    forest = UnionFind(n * n)
    for edge in grid_edges(n):
        if edge[0] not in support and edge[1] not in support:
            forest.union(*edge)
    component_of = {vertex: forest.root(vertex) for vertex in range(n * n) if vertex not in support}
    components = {
        root: tuple(sorted(vertex for vertex, item_root in component_of.items() if item_root == root))
        for root in sorted(set(component_of.values()))
    }
    return support, component_of, components


def _outer_ports(n: int, support: frozenset[Vertex]) -> frozenset[Resource]:
    result: set[Resource] = set()
    for vertex in support:
        row, column = divmod(vertex, n)
        for side, present in (
            (NORTH, row == 0), (EAST, column + 1 == n),
            (SOUTH, row + 1 == n), (WEST, column == 0),
        ):
            if present:
                result.add(("port", (vertex, side)))
    return frozenset(result)


def _edge_dual_endpoints(n: int, edge: Edge) -> tuple[Face, Face]:
    left, right = edge
    lr, lc = divmod(left, n)
    rr, rc = divmod(right, n)
    width = n - 1
    if lr == rr:
        above = (lr - 1) * width + lc if lr else OUT
        below = lr * width + lc if lr + 1 < n else OUT
        return above, below
    upper_row, column = min(lr, rr), lc
    west = upper_row * width + column - 1 if column else OUT
    east = upper_row * width + column if column + 1 < n else OUT
    return west, east


def _incident_faces(n: int, vertices: Sequence[Vertex]) -> tuple[Face, ...]:
    result: set[Face] = set()
    width = n - 1
    for vertex in vertices:
        row, column = divmod(vertex, n)
        if row in (0, n - 1) or column in (0, n - 1):
            result.add(OUT)
        for cell_row in (row - 1, row):
            for cell_column in (column - 1, column):
                if 0 <= cell_row < width and 0 <= cell_column < width:
                    result.add(cell_row * width + cell_column)
    return tuple(sorted(result))


def _dual_parent(n: int, cotree: Sequence[Edge]) -> dict[Face, Face | None]:
    adjacency = {face: [] for face in (OUT, *range((n - 1) ** 2))}
    for edge in cotree:
        a, b = _edge_dual_endpoints(n, edge)
        adjacency[a].append(b)
        adjacency[b].append(a)
    parent: dict[Face, Face | None] = {OUT: None}
    queue = [OUT]
    for face in queue:
        for other in sorted(adjacency[face]):
            if other not in parent:
                parent[other] = face
                queue.append(other)
    if len(parent) != (n - 1) ** 2 + 1 or len(cotree) != (n - 1) ** 2:
        raise AssertionError("the primal cotree is not a dual spanning tree")
    return parent


def _fundamental_exchanges(
    vertex_count: int, tree: frozenset[Edge], cotree: Sequence[Edge]
) -> dict[Edge, tuple[Edge, ...]]:
    """Index cotree insertions by the tree edges on their fundamental cycles."""
    adjacency: dict[Vertex, list[Vertex]] = {vertex: [] for vertex in range(vertex_count)}
    for left, right in tree:
        adjacency[left].append(right)
        adjacency[right].append(left)
    result: dict[Edge, list[Edge]] = {edge: [] for edge in tree}
    for omitted in cotree:
        start, target = omitted
        predecessor: dict[Vertex, Vertex | None] = {start: None}
        queue = [start]
        for vertex in queue:
            if vertex == target:
                break
            for other in adjacency[vertex]:
                if other not in predecessor:
                    predecessor[other] = vertex
                    queue.append(other)
        vertex = target
        while predecessor[vertex] is not None:
            previous = predecessor[vertex]
            assert previous is not None
            result[_edge(previous, vertex)].append(omitted)
            vertex = previous
    return {edge: tuple(sorted(omitted)) for edge, omitted in result.items()}


def _port_face(port: Resource) -> Face:
    if port[0] != "port":
        raise ValueError("not a port")
    return OUT


def _outer_boundary_occurrences(
    n: int,
    tree: frozenset[Edge],
    cotree: frozenset[Edge],
    support: frozenset[Vertex],
    component_of: dict[Vertex, int],
) -> tuple[tuple[Node, ...], dict[int, Resource], dict[Resource, tuple[int, ...]]]:
    """Interleave split sectors and primal edges around the clockwise boundary."""
    sides = (
        tuple((column, NORTH) for column in range(n)),
        tuple((row * n + n - 1, EAST) for row in range(n)),
        tuple(((n - 1) * n + column, SOUTH) for column in reversed(range(n))),
        tuple((row * n, WEST) for row in reversed(range(n))),
    )
    occurrences: list[Node] = []
    resources: dict[int, Resource] = {}
    by_resource: dict[Resource, list[int]] = {}

    def append(node: Node, resource: Resource | None) -> None:
        index = len(occurrences)
        occurrences.append(node)
        if resource is not None:
            resources[index] = resource
            by_resource.setdefault(resource, []).append(index)

    for side in sides:
        for offset, slot in enumerate(side):
            vertex, direction = slot
            sector_resource: Resource = (
                ("port", slot) if vertex in support
                else ("component", component_of[vertex])
            )
            append(("outer-sector", slot), sector_resource)
            if offset + 1 == len(side):
                continue
            edge = _edge(vertex, side[offset + 1][0])
            if edge in cotree:
                append(("outer-edge", edge), None)
            elif edge[0] in support and edge[1] in support:
                append(("outer-edge", edge), ("internal", edge))
            else:
                free_vertex = edge[0] if edge[0] not in support else edge[1]
                append(("outer-edge", edge), ("component", component_of[free_vertex]))
    return (
        tuple(occurrences),
        resources,
        {resource: tuple(indices) for resource, indices in by_resource.items()},
    )


def build_model(n: int, tree_edges: Iterable[Edge], axis: str) -> FullPrunedModel:
    tree = frozenset(_edge(*edge) for edge in tree_edges)
    if not is_tree(n * n, tuple(tree)):
        raise ValueError("input is not a spanning tree")
    contour = expanded_contour(n, tree)
    rank = {slot: index for index, slot in enumerate(contour)}
    support, component_of, components = _support_and_components(n, tree)
    ports = _outer_ports(n, support)
    marked = frozenset(port[1] for port in ports)
    demands = canonical_demands(n, axis)
    starts = {
        demand: (demand.vertex, demand.side if demand.vertex in support else (demand.side + 2) % 4)
        for demand in demands
    }
    if len(set(starts.values())) != n + 3:
        raise AssertionError("canonical start slots collided")

    reached: dict[Demand, Slot] = {}
    distance: dict[Demand, int] = {}
    for demand, start in starts.items():
        slot, steps = start, 0
        while slot not in marked:
            slot = expanded_successor(n, tree, slot)
            steps += 1
            if steps > 4 * n * n:
                raise AssertionError("canonical start did not reach an outer-port mark")
        reached[demand], distance[demand] = slot, steps

    groups: dict[Slot, list[Demand]] = {}
    for demand in demands:
        groups.setdefault(reached[demand], []).append(demand)
    merger_owner_demands: list[Demand] = []
    merger_slot_by_owner: dict[Demand, Slot] = {}
    for stop, group in sorted(groups.items()):
        farthest = max(group, key=lambda demand: (distance[demand], demand))
        for demand in group:
            if demand == farthest:
                continue
            owner = farthest if starts[demand] == stop else demand
            merger_owner_demands.append(owner)
            merger_slot_by_owner[owner] = starts[demand]
    if len(merger_owner_demands) != len(demands) - len(groups):
        raise AssertionError("full-pruned branch-excess identity failed")
    if len(set(merger_owner_demands)) != len(merger_owner_demands):
        raise AssertionError("canonical merger owners are not injective")
    if any(demand.vertex in support for demand in merger_owner_demands):
        raise AssertionError("a canonical merger owner was not an unmarked start")

    tokens = tuple(sorted((
        Source(rank[starts[demand]], demand, component_of[demand.vertex])
        for demand in merger_owner_demands
    )))
    representative = {
        component: min((token for token in tokens if token.component == component), default=None)
        for component in components
    }
    collisions = tuple(token for token in tokens if token != representative[token.component])
    cotree = tuple(edge for edge in grid_edges(n) if edge not in tree)
    face_parent = _dual_parent(n, cotree)
    fundamental_exchanges = _fundamental_exchanges(n * n, tree, cotree)

    internal_edges = frozenset(
        ("internal", edge) for edge in tree if edge[0] in support and edge[1] in support
    )
    component_resources = frozenset(("component", root) for root in components)
    component_contacts = {
        root: tuple(sorted(
            ComponentContact(edge, _edge_dual_endpoints(n, edge))
            for edge in tree
            if (edge[0] in vertices) != (edge[1] in vertices)
        ))
        for root, vertices in components.items()
    }
    all_resources = ports | internal_edges | component_resources
    reserved_owner: dict[Resource, Owner] = {}
    for stop in sorted(groups):
        resource = ("port", stop)
        reserved_owner[resource] = Owner("exit", stop, (_port_face(resource),))
    # The generic Lean API has this reservation pool.  Its canonical full-pruned
    # specialization is empty because every terminal token is noninternal.
    for token in tokens:
        inward = _neighbor(n, token.demand.vertex, (token.demand.side + 2) % 4)
        assert inward is not None
        edge_resource = ("internal", _edge(token.demand.vertex, inward))
        if edge_resource in internal_edges:
            reserved_owner[edge_resource] = Owner("internal-token", token, _edge_dual_endpoints(n, edge_resource[1]))  # type: ignore[arg-type]
    for component, token in representative.items():
        if token is not None:
            reserved_owner[("component", component)] = Owner(
                "component-representative", token, _incident_faces(n, components[component])
            )
    residual = frozenset(all_resources - reserved_owner.keys())

    face_resources: dict[Face, set[Resource]] = {
        face: set() for face in (OUT, *range((n - 1) ** 2))
    }
    for resource in ports:
        face_resources[OUT].add(resource)
    for resource in internal_edges:
        for face in _edge_dual_endpoints(n, resource[1]):  # type: ignore[arg-type]
            face_resources[face].add(resource)
    for resource in component_resources:
        for face in _incident_faces(n, components[resource[1]]):  # type: ignore[index]
            face_resources[face].add(resource)

    source_seed_faces: dict[Source, tuple[Face, ...]] = {}
    for source in collisions:
        incident_cotree = [
            edge for edge in cotree
            if edge[0] in components[source.component] or edge[1] in components[source.component]
        ]
        seeds = {
            face for edge in incident_cotree for face in _edge_dual_endpoints(n, edge)
            if face != OUT
        }
        if not seeds:
            seeds = {OUT}
        source_seed_faces[source] = tuple(sorted(seeds))

    outer_boundary, outer_occurrence_resources, resource_outer_occurrences = (
        _outer_boundary_occurrences(
            n, tree, frozenset(cotree), support, component_of
        )
    )

    return FullPrunedModel(
        n=n,
        axis=axis,
        tree=tuple(sorted(tree)),
        contour=contour,
        reached_exit_ports=tuple(sorted(("port", stop) for stop in groups)),
        tokens=tokens,
        collisions=collisions,
        residual_resources=residual,
        reserved_owner=reserved_owner,
        source_seed_faces=source_seed_faces,
        face_parent=face_parent,
        face_resources={face: frozenset(items) for face, items in face_resources.items()},
        components=components,
        component_contacts=component_contacts,
        cotree=tuple(sorted(cotree)),
        fundamental_exchanges=fundamental_exchanges,
        marked_slots=marked,
        collision_merger_slots={
            token: merger_slot_by_owner[token.demand] for token in collisions
        },
        outer_boundary=outer_boundary,
        outer_occurrence_resources=outer_occurrence_resources,
        resource_outer_occurrences=resource_outer_occurrences,
    )


def _boundary_index(n: int, vertex: Vertex) -> int:
    row, column = divmod(vertex, n)
    if row == 0:
        return column
    if column + 1 == n:
        return n + row - 1
    if row + 1 == n:
        return 3 * n - 3 - column
    return 4 * n - 4 - row


def _spatial_key(n: int, source: Source) -> int:
    # NORTH/EAST/SOUTH/WEST are Lean's top/right/bottom/left tie order.
    return 4 * _boundary_index(n, source.demand.vertex) + source.demand.side


def _spatial_gap_transition(model: FullPrunedModel, previous: Source, current: Source) -> Edge:
    """Execute the ordinary-gap or duplicated-corner transition from Lean."""
    n = model.n
    pr, pc = divmod(previous.demand.vertex, n)
    cr, cc = divmod(current.demand.vertex, n)
    if (pr, pc) != (cr, cc):
        if pr == cr:
            column = min(pc, cc)
            edge_row = n - 2 if pr + 1 == n else pr + 1
            transition = _edge(edge_row * n + column, edge_row * n + column + 1)
        elif pc == cc:
            row = min(pr, cr)
            edge_column = n - 2 if pc + 1 == n else pc + 1
            transition = _edge(row * n + edge_column, (row + 1) * n + edge_column)
        else:
            raise AssertionError("consecutive contacts do not lie in one straight component")
    elif model.axis == "rows":
        # Southwest duplicated corner: top side, otherwise right side.
        top = _edge((n - 2) * n, (n - 2) * n + 1)
        right = _edge((n - 2) * n + 1, (n - 1) * n + 1)
        transition = top if top in model.cotree else right
    else:
        # Northeast duplicated corner: bottom side, otherwise left side.
        bottom = _edge(n + n - 2, n + n - 1)
        left = _edge(n - 2, 2 * n - 2)
        transition = bottom if bottom in model.cotree else left
    if transition not in model.cotree:
        raise AssertionError("selected spatial gap did not produce a cotree transition")
    return transition


def spatial_gaps(model: FullPrunedModel) -> dict[int, tuple[SpatialGap, ...]]:
    result: dict[int, tuple[SpatialGap, ...]] = {}
    for component in sorted({source.component for source in model.tokens}):
        contacts = sorted(
            (source for source in model.tokens if source.component == component),
            key=lambda source: _spatial_key(model.n, source),
        )
        result[component] = tuple(
            SpatialGap(component, previous, current,
                _spatial_gap_transition(model, previous, current))
            for previous, current in zip(contacts, contacts[1:])
        )
    return result


def occurrence_gap_bijections(model: FullPrunedModel) -> Iterable[dict[Source, SpatialGap]]:
    """Enumerate Lean's noncomputable componentwise ``equivOfCardEq`` choice."""
    gaps = spatial_gaps(model)
    components = sorted(gaps)
    local_choices = []
    for component in components:
        occurrences = tuple(source for source in model.collisions if source.component == component)
        if len(occurrences) != len(gaps[component]):
            raise AssertionError("contour-collision/spatial-gap cardinality mismatch")
        local_choices.append(tuple(
            dict(zip(occurrences, ordering)) for ordering in permutations(gaps[component])
        ))
    for choices in product(*local_choices):
        yield {source: gap for choice in choices for source, gap in choice.items()}


def occurrence_gap_bijection_count(model: FullPrunedModel) -> int:
    """Return the size of the componentwise bijection space without expanding it."""
    return math.prod(math.factorial(len(gaps)) for gaps in spatial_gaps(model).values())


def sampled_occurrence_gap_bijections(
    model: FullPrunedModel, count: int, rng: random.Random
) -> Iterable[dict[Source, SpatialGap]]:
    """Sample distinct componentwise bijections, uniformly from the product space."""
    gaps = spatial_gaps(model)
    components = sorted(gaps)
    occurrences = {
        component: tuple(source for source in model.collisions if source.component == component)
        for component in components
    }
    seen: set[tuple[tuple[SpatialGap, ...], ...]] = set()
    while len(seen) < count:
        orderings = tuple(
            tuple(rng.sample(gaps[component], len(gaps[component])))
            for component in components
        )
        if orderings in seen:
            continue
        seen.add(orderings)
        yield {
            source: gap
            for component, ordering in zip(components, orderings, strict=True)
            for source, gap in zip(occurrences[component], ordering, strict=True)
        }


def _boundary_port(n: int, edge: Edge) -> Resource:
    a, b = edge
    ar, ac = divmod(a, n)
    br, bc = divmod(b, n)
    if ar == br:
        side = NORTH if ar == 0 else SOUTH
    else:
        side = WEST if ac == 0 else EAST
    return "port", (a, side)


def _shared_core_parent(
    model: FullPrunedModel, inward: Sequence[Source], choice: dict[Source, SpatialGap]
) -> tuple[dict[Node, Node | None], dict[Source, Node]]:
    occurrences: list[tuple[Node, Edge]] = [
        (("edge", edge), edge) for edge in model.cotree
    ]
    selected: dict[Source, Node] = {}
    for source in inward:
        edge = choice[source].transition
        endpoints = _edge_dual_endpoints(model.n, edge)
        if OUT in endpoints:
            selected[source] = ("edge", edge)
        else:
            node = ("gap", source)
            selected[source] = node
            occurrences.append((node, edge))

    adjacency: dict[Node, set[Node]] = {}
    boundary_nodes: set[Node] = set()
    for occurrence, edge in occurrences:
        adjacency.setdefault(occurrence, set())
        for endpoint_index, face in enumerate(_edge_dual_endpoints(model.n, edge)):
            if face == OUT:
                other = ("boundary", (edge, endpoint_index))
                boundary_nodes.add(other)
            else:
                other = ("face", face)
            adjacency.setdefault(other, set())
            adjacency[occurrence].add(other)
            adjacency[other].add(occurrence)

    distance = {node: 0 for node in boundary_nodes}
    queue = sorted(boundary_nodes, key=repr)
    for node in queue:
        for other in sorted(adjacency[node], key=repr):
            if other not in distance:
                distance[other] = distance[node] + 1
                queue.append(other)
    if len(distance) != len(adjacency):
        raise AssertionError("shared cotree-dual core did not reach its split boundary")
    parent: dict[Node, Node | None] = {}
    for node in adjacency:
        if node in boundary_nodes:
            parent[node] = None
        else:
            candidates = [other for other in adjacency[node] if distance[other] < distance[node]]
            parent[node] = min(candidates, key=repr)
    return parent, selected


def build_grouped_hull(
    model: FullPrunedModel, occurrence_to_gap: dict[Source, SpatialGap]
) -> GroupedHullModel:
    outer = tuple(
        source for source in model.collisions
        if model.collision_merger_slots[source] in model.marked_slots
    )
    inward = tuple(source for source in model.collisions if source not in outer)
    # Outer collisions are not hull leaves, but their independently routed
    # selected-gap occurrence lives over the same one-copy continuation core.
    parent, selected = _shared_core_parent(model, model.collisions, occurrence_to_gap)
    hull: set[Node] = set()
    start_parent: dict[Node, Node] = {}
    for source in inward:
        start = ("start", source)
        start_parent[start] = selected[source]
        hull.add(start)
        node: Node | None = selected[source]
        while node is not None:
            hull.add(node)
            node = parent[node]

    children = {node: [] for node in hull}
    for node in hull:
        next_node = start_parent.get(node, parent.get(node))
        if next_node in children:
            children[next_node].append(node)

    sources: list[GroupedSource] = []
    seeds: dict[GroupedSource, Node] = {}
    root_reverse_seeds: dict[GroupedSource, Node] = {}
    roots = sorted((node for node in hull if node[0] != "start" and parent[node] is None), key=repr)
    for index, node in enumerate(roots):
        edge, _endpoint_index = node[1]  # type: ignore[misc]
        source = GroupedSource("root", index, _boundary_port(model.n, edge))
        sources.append(source)
        seeds[source] = ("resource", source.label)
        root_reverse_seeds[source] = node
    branch_index = 0
    for node in sorted(hull, key=repr):
        physical_children = sorted(
            (child for child in children[node] if child[0] != "start"), key=repr
        )
        excess = len(children[node]) - 1
        for slot in range(max(0, excess)):
            source = GroupedSource("branch", branch_index, (node, slot))
            branch_index += 1
            sources.append(source)
            seeds[source] = physical_children[min(slot, len(physical_children) - 1)] \
                if physical_children else node
    for index, collision in enumerate(outer):
        source = GroupedSource("outer", index, collision)
        sources.append(source)
        seeds[source] = selected[collision]
    if len(sources) != len(model.collisions):
        raise AssertionError("one-copy roots-plus-branch-excess identity failed")
    return GroupedHullModel(
        model, occurrence_to_gap, tuple(sorted(sources)), seeds, parent,
        frozenset(hull), root_reverse_seeds
    )


def grouped_hulls(model: FullPrunedModel) -> Iterable[GroupedHullModel]:
    for choice in occurrence_gap_bijections(model):
        yield build_grouped_hull(model, choice)


def alternating_closure(
    model: FullPrunedModel, sources: Iterable[Source], *, displace: bool = True
) -> tuple[frozenset[Resource], frozenset[Owner]]:
    """Close first-separator walks under canonical reserved-resource owners."""
    face_queue = [face for source in sources for face in model.source_seed_faces[source]]
    seen_faces: set[Face] = set()
    seen_owners: set[Owner] = set()
    neighborhood: set[Resource] = set()
    while face_queue:
        face = face_queue.pop(0)
        if face in seen_faces:
            continue
        seen_faces.add(face)
        candidates = model.face_resources[face]
        if not candidates:
            parent = model.face_parent[face]
            if parent is not None:
                face_queue.append(parent)
            continue
        for resource in candidates:
            if resource in model.residual_resources:
                neighborhood.add(resource)
            elif displace:
                owner = model.reserved_owner[resource]
                if owner not in seen_owners:
                    seen_owners.add(owner)
                    face_queue.extend(owner.seed_faces)
    return frozenset(neighborhood), frozenset(seen_owners)


def historical_collision_hall_balance(
    model: FullPrunedModel, *, displace: bool = True
) -> HallFailure | None:
    """Test Hall by unioning independently computed singleton neighborhoods."""
    sources = model.collisions
    singleton = {
        source: alternating_closure(model, (source,), displace=displace)
        for source in sources
    }
    for size in range(1, len(sources) + 1):
        for indices in combinations(range(len(sources)), size):
            selected = tuple(sources[index] for index in indices)
            neighborhood = frozenset().union(*(singleton[source][0] for source in selected))
            owners = frozenset().union(*(singleton[source][1] for source in selected))
            if len(neighborhood) < size:
                return HallFailure(indices, selected, tuple(sorted(neighborhood)), tuple(sorted(owners, key=repr)))
    return None


def historical_closed_region_balance(model: FullPrunedModel) -> HallFailure | None:
    """Jointly close every subset and test its candidate-region boundary balance."""
    sources = model.collisions
    for size in range(1, len(sources) + 1):
        for indices in combinations(range(len(sources)), size):
            selected = tuple(sources[index] for index in indices)
            neighborhood, owners = alternating_closure(model, selected)
            if len(neighborhood) < size:
                return HallFailure(indices, selected, tuple(sorted(neighborhood)), tuple(sorted(owners, key=repr)))
    return None


def grouped_alternating_closure(
    model: GroupedHullModel, sources: Iterable[GroupedSource], *, displace: bool = True
) -> tuple[frozenset[Resource], frozenset[Owner]]:
    """Walk through raw resources, owner displacement, and basis exchanges."""
    base = model.base
    selected_sources = tuple(sources)
    queue = [(model.source_seeds[source], source) for source in selected_sources]
    queue.extend(
        (("reverse-root", node), source)
        for source, node in model.root_reverse_seeds.items()
        if source in selected_sources
    )
    seen_states: set[tuple[Node, GroupedSource]] = set()
    seen_owner_states: set[tuple[Owner, GroupedSource]] = set()
    displaced_owners: set[Owner] = set()
    neighborhood: set[Resource] = set()
    reverse_children: dict[Node, tuple[Node, ...]] = {
        node: tuple(sorted((child for child in model.hull_nodes
            if child[0] != "start" and model.parent.get(child) == node), key=repr))
        for node in model.hull_nodes
    }

    def continue_outer(index: int, direction: int, source: GroupedSource) -> None:
        next_index = (index + direction) % len(base.outer_boundary)
        queue.append((("outer-walk", (next_index, direction)), source))

    def displace_owner(resource: Resource, source: GroupedSource) -> bool:
        if not displace or resource not in base.reserved_owner:
            return False
        owner = base.reserved_owner[resource]
        owner_state = (owner, source)
        if owner_state not in seen_owner_states:
            seen_owner_states.add(owner_state)
            displaced_owners.add(owner)
            # OUT is not a single candidate region. Exterior continuation is
            # launched from the concrete occurrence that caused displacement.
            queue.extend(
                (("owner-face", face), source)
                for face in owner.seed_faces if face != OUT
            )
        return True

    def offer(
        resource: Resource, source: GroupedSource, entry_face: Face | None = None
    ) -> None:
        if resource in base.residual_resources:
            neighborhood.add(resource)
        elif displace_owner(resource, source) and resource[0] == "port":
            for index in base.resource_outer_occurrences[resource]:
                continue_outer(index, 1, source)
                continue_outer(index, -1, source)
        if displace and resource[0] == "internal":
            edge = resource[1]
            queue.append((("internal-pass", (edge, entry_face)), source))
            queue.extend((("edge", omitted), source)
                for omitted in base.fundamental_exchanges[edge])  # type: ignore[index]
        if displace and resource[0] == "component":
            component = resource[1]
            queue.extend((
                ("component-contact", (component, contact.edge, endpoint_index, face)), source
            ) for contact in base.component_contacts[component]  # type: ignore[index]
              for endpoint_index, face in enumerate(contact.faces))
            for index in base.resource_outer_occurrences.get(resource, ()):
                continue_outer(index, 1, source)
                continue_outer(index, -1, source)

    while queue:
        node, source = queue.pop(0)
        state = (node, source)
        if state in seen_states:
            continue
        seen_states.add(state)
        kind, label = node
        if kind == "reverse-root":
            hull_node = label  # type: ignore[assignment]
            if hull_node[0] == "face":  # type: ignore[index]
                for resource in base.face_resources[hull_node[1]]:  # type: ignore[index]
                    offer(resource, source, hull_node[1])  # type: ignore[arg-type]
            queue.extend(
                (("reverse-root", child), source)
                for child in reverse_children.get(hull_node, ())  # type: ignore[arg-type]
            )
            continue
        if kind == "outer-walk":
            index, direction = label  # type: ignore[misc]
            occurrence = base.outer_boundary[index]
            resource = base.outer_occurrence_resources.get(index)
            if resource is None:
                edge = occurrence[1]
                # The exterior occurrence of a boundary cotree edge continues
                # through that contact into its bounded incident face. The
                # shared core's parent points the opposite way, back to OUT.
                queue.extend(
                    (("face", face), source)
                    for face in _edge_dual_endpoints(base.n, edge)  # type: ignore[arg-type]
                    if face != OUT
                )
            elif resource[0] == "port" and resource in base.reserved_owner:
                displace_owner(resource, source)
                continue_outer(index, direction, source)
            else:
                offer(resource, source, OUT)
            continue
        if kind == "resource":
            offer(label, source)  # type: ignore[arg-type]
            continue
        if kind == "internal-pass":
            edge, entry_face = label  # type: ignore[misc]
            endpoints = _edge_dual_endpoints(base.n, edge)
            if entry_face is not None and entry_face not in endpoints:
                raise AssertionError("internal edge reached from a nonincident face")
            for face in endpoints:
                if face == entry_face:
                    continue
                if face == OUT:
                    index = base.outer_boundary.index(("outer-edge", edge))
                    continue_outer(index, 1, source)
                    continue_outer(index, -1, source)
                else:
                    queue.append((("face", face), source))
            continue
        if kind == "boundary":
            edge, _endpoint_index = label  # type: ignore[misc]
            offer(_boundary_port(base.n, edge), source)
            continue
        if kind == "edge" and OUT in _edge_dual_endpoints(base.n, label):  # type: ignore[arg-type]
            index = base.outer_boundary.index(("outer-edge", label))
            continue_outer(index, 1, source)
            continue_outer(index, -1, source)
            continue
        if kind in ("face", "owner-face", "component-contact"):
            if kind == "component-contact" and displace:
                _component, edge, _endpoint_index, _face = label  # type: ignore[misc]
                queue.extend(
                    (("edge", omitted), source)
                    for omitted in base.fundamental_exchanges[edge]
                )
            face = label[-1] if kind == "component-contact" else label  # type: ignore[index]
            if face == OUT:
                if kind == "component-contact":
                    _component, edge, _endpoint_index, _face = label  # type: ignore[misc]
                    occurrence = ("outer-edge", edge)
                    index = base.outer_boundary.index(occurrence)
                    continue_outer(index, 1, source)
                    continue_outer(index, -1, source)
                continue
            candidates = base.face_resources[face]  # type: ignore[index]
            if candidates:
                for resource in candidates:
                    offer(resource, source, face)  # type: ignore[arg-type]
                continue
            if kind == "owner-face":
                parent_face = base.face_parent[face]  # type: ignore[index]
                if parent_face is not None:
                    queue.append((("owner-face", parent_face), source))
                continue
        parent = model.parent.get(node)
        if parent is not None:
            queue.append((parent, source))
    return frozenset(neighborhood), frozenset(displaced_owners)


def _subset_hall_balance(
    model: GroupedHullModel, *, displace: bool = True
) -> HallFailure | None:
    sources = model.sources
    singleton = {
        source: grouped_alternating_closure(model, (source,), displace=displace)
        for source in sources
    }
    for size in range(1, len(sources) + 1):
        for indices in combinations(range(len(sources)), size):
            selected = tuple(sources[index] for index in indices)
            neighborhood = frozenset().union(*(singleton[source][0] for source in selected))
            owners = frozenset().union(*(singleton[source][1] for source in selected))
            if len(neighborhood) < size:
                return HallFailure(indices, selected, tuple(sorted(neighborhood)),
                    tuple(sorted(owners, key=repr)))
    return None


def _matching_hall_balance(
    model: GroupedHullModel, *, displace: bool = True
) -> HallFailure | None:
    """Test Hall by exact bipartite matching and recover an alternating witness."""
    sources = model.sources
    singleton = tuple(
        grouped_alternating_closure(model, (source,), displace=displace)
        for source in sources
    )
    resource_owner: dict[Resource, int] = {}

    def augment(index: int, seen: set[Resource]) -> bool:
        for resource in sorted(singleton[index][0], key=repr):
            if resource in seen:
                continue
            seen.add(resource)
            previous = resource_owner.get(resource)
            if previous is None or augment(previous, seen):
                resource_owner[resource] = index
                return True
        return False

    for index in range(len(sources)):
        augment(index, set())
    source_resource = {index: resource for resource, index in resource_owner.items()}
    if len(source_resource) == len(sources):
        return None

    # Alternating reachability from all unmatched left vertices gives S with
    # N(S) equal to the reached right side and |N(S)| < |S|.
    reached_sources = {index for index in range(len(sources)) if index not in source_resource}
    reached_resources: set[Resource] = set()
    queue = list(sorted(reached_sources))
    for index in queue:
        for resource in sorted(singleton[index][0], key=repr):
            if source_resource.get(index) == resource or resource in reached_resources:
                continue
            reached_resources.add(resource)
            owner = resource_owner.get(resource)
            if owner is not None and owner not in reached_sources:
                reached_sources.add(owner)
                queue.append(owner)
    indices = tuple(sorted(reached_sources))
    neighborhood = frozenset().union(*(singleton[index][0] for index in indices))
    if len(neighborhood) >= len(indices):
        raise AssertionError("matching failure did not yield a Hall witness")
    owners = frozenset().union(*(singleton[index][1] for index in indices))
    return HallFailure(
        indices,
        tuple(sources[index] for index in indices),
        tuple(sorted(neighborhood)),
        tuple(sorted(owners, key=repr)),
    )


def exact_hall_balance(
    model: GroupedHullModel,
    *,
    displace: bool = True,
    method: str = "auto",
    subset_limit: int = 12,
) -> HallFailure | None:
    """Test Hall exactly, enumerating small source sets and matching larger ones."""
    if method not in ("auto", "subsets", "matching"):
        raise ValueError(f"unknown Hall method: {method}")
    if method == "auto":
        method = "subsets" if len(model.sources) <= subset_limit else "matching"
    if method == "subsets":
        return _subset_hall_balance(model, displace=displace)
    return _matching_hall_balance(model, displace=displace)


def exact_closed_region_balance(model: GroupedHullModel) -> HallFailure | None:
    for size in range(1, len(model.sources) + 1):
        for indices in combinations(range(len(model.sources)), size):
            selected = tuple(model.sources[index] for index in indices)
            neighborhood, owners = grouped_alternating_closure(model, selected)
            if len(neighborhood) < size:
                return HallFailure(indices, selected, tuple(sorted(neighborhood)),
                    tuple(sorted(owners, key=repr)))
    return None


def exact_subset_balance(model: GroupedHullModel, *, displace: bool = True) -> HallFailure | None:
    return exact_hall_balance(model, displace=displace)


def audit_tree(
    n: int,
    tree: Iterable[Edge],
    axis: str,
    *,
    all_gap_limit: int | None = None,
    sampled_gap_count: int = 64,
    rng: random.Random | None = None,
    subset_limit: int = 12,
) -> TreeAudit:
    model = build_model(n, tree, axis)
    gap_choice_total = occurrence_gap_bijection_count(model)
    audit_all = all_gap_limit is None or gap_choice_total <= all_gap_limit
    if audit_all:
        choices = occurrence_gap_bijections(model)
    else:
        choices = sampled_occurrence_gap_bijections(
            model, min(sampled_gap_count, gap_choice_total), rng or random.Random(0)
        )
    hulls = tuple(build_grouped_hull(model, choice) for choice in choices)
    failures = tuple(
        exact_hall_balance(hull, subset_limit=subset_limit) for hull in hulls
    )
    failing_index = next((index for index, failure in enumerate(failures) if failure is not None), None)
    first_failure = failures[failing_index] if failing_index is not None else None
    gap_choice_failure = None if failing_index is None else GapChoiceFailure(
        tuple(sorted(hulls[failing_index].occurrence_to_gap.items())), first_failure
    )
    default_hull = hulls[0]
    enumerate_closed_regions = len(default_hull.sources) <= subset_limit
    return TreeAudit(
        n=n,
        axis=axis,
        source_count=len(model.collisions),
        residual_count=len(model.residual_resources),
        hall_failure=first_failure,
        closed_region_failure=(
            next(
                (failure for hull in hulls
                 if (failure := exact_closed_region_balance(hull)) is not None), None
            )
            if enumerate_closed_regions else first_failure
        ),
        direct_hall_failure=exact_hall_balance(
            default_hull, displace=False, subset_limit=subset_limit
        ),
        gap_choice_count=len(hulls),
        hall_holds_for_all_gap_choices=all(failure is None for failure in failures),
        hall_holds_for_some_gap_choices=any(failure is None for failure in failures),
        first_failing_gap_choice=gap_choice_failure,
        gap_choice_total=gap_choice_total,
        gap_choice_mode="all" if audit_all else "sampled",
        hall_method=(
            "subsets" if max((len(hull.sources) for hull in hulls), default=0) <= subset_limit
            else "matching"
        ),
    )


def _jsonable(value: object) -> object:
    if hasattr(value, "__dataclass_fields__"):
        return {key: _jsonable(item) for key, item in asdict(value).items()}
    if isinstance(value, dict):
        return {str(key): _jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list, set, frozenset)):
        return [_jsonable(item) for item in value]
    return value


def exhaustive_census(n: int) -> dict[str, object]:
    tree_count = 0
    axis_audits = 0
    trees_with_collisions = 0
    maximum_sources = 0
    gap_choices = 0
    audits_holding_for_all_choices = 0
    audits_holding_for_some_choices = 0
    trees_with_no_axis_failures = 0
    trees_with_one_axis_failure = 0
    trees_with_both_axis_failures = 0
    first_failure: dict[str, object] | None = None
    hall_counterexamples: list[dict[str, object]] = []
    first_closed_region_failure: dict[str, object] | None = None
    first_direct_failure: dict[str, object] | None = None
    for tree in spanning_trees(n):
        tree_count += 1
        tree_has_collision = False
        axis_failures = 0
        for axis in AXES:
            audit = audit_tree(n, tree, axis)
            axis_audits += 1
            tree_has_collision |= audit.source_count > 0
            maximum_sources = max(maximum_sources, audit.source_count)
            gap_choices += audit.gap_choice_count
            audits_holding_for_all_choices += audit.hall_holds_for_all_gap_choices
            audits_holding_for_some_choices += audit.hall_holds_for_some_gap_choices
            axis_failures += not audit.hall_holds_for_some_gap_choices
            if audit.hall_failure is not None and first_failure is None:
                first_failure = {
                    "tree": list(tree), "axis": axis,
                    "gap_choice_failure": _jsonable(audit.first_failing_gap_choice),
                }
            if audit.hall_failure is not None:
                hall_counterexamples.append({
                    "tree": list(tree), "axis": axis,
                    "fails_every_gap_choice": not audit.hall_holds_for_some_gap_choices,
                    "gap_choice_failure": _jsonable(audit.first_failing_gap_choice),
                })
            if audit.closed_region_failure is not None and first_closed_region_failure is None:
                first_closed_region_failure = {
                    "tree": list(tree), "axis": axis,
                    "gap_choice_failure": _jsonable(audit.first_failing_gap_choice),
                }
            if audit.direct_hall_failure is not None and first_direct_failure is None:
                first_direct_failure = {"tree": list(tree), "axis": axis, "failure": _jsonable(audit.direct_hall_failure)}
        trees_with_collisions += tree_has_collision
        if axis_failures == 0:
            trees_with_no_axis_failures += 1
        elif axis_failures == 1:
            trees_with_one_axis_failure += 1
        else:
            trees_with_both_axis_failures += 1
    return {
        "n": n,
        "tree_count": tree_count,
        "axis_audits": axis_audits,
        "trees_with_collisions": trees_with_collisions,
        "maximum_collision_sources": maximum_sources,
        "hall_counterexample": first_failure,
        "hall_counterexamples": hall_counterexamples,
        "candidate_closed_region_counterexample": first_closed_region_failure,
        "alternating_closure_counterexample": first_failure,
        "direct_neighborhood_counterexample": first_direct_failure,
        "all_source_subsets_tested": True,
        "gap_choice_count": gap_choices,
        "axis_audits_holding_for_all_gap_choices": audits_holding_for_all_choices,
        "axis_audits_holding_for_some_gap_choices": audits_holding_for_some_choices,
        "axis_audits_failing_for_at_least_one_gap_choice": axis_audits - audits_holding_for_all_choices,
        "axis_audits_failing_for_every_gap_choice": axis_audits - audits_holding_for_some_choices,
        "trees_with_no_axis_failing_for_every_gap_choice": trees_with_no_axis_failures,
        "trees_with_exactly_one_axis_failing_for_every_gap_choice": trees_with_one_axis_failure,
        "trees_with_both_axes_failing_for_every_gap_choice": trees_with_both_axis_failures,
        "trees_with_adaptive_axis_holding_for_all_gap_choices": tree_count - trees_with_both_axis_failures,
        "axis_failure_semantics": "an axis fails when Hall fails for every occurrence-to-spatial-gap bijection; adaptive success chooses an axis whose Hall audit holds for all such bijections",
        "source_semantics": "one-copy shared-hull used roots plus branch excess and outer collisions",
        "reverse_root_semantics": "one grouped root occurrence also traverses inward along every unique active descendant chain belonging to its selected collision leaves, exposing face-incident raw resources without copying the root source",
        "launch_semantics": "all occurrence-to-spatial-gap bijections; exact ordinary/corner transitions",
        "internal_edge_semantics": "a reached raw support-support tree edge remains one resource and continues, occurrence-labelled, to its opposite incident dual face without receiving a second unit of credit",
        "exchange_semantics": "a reached internal tree edge or raw-component contact edge also continues through every cotree insertion whose fundamental cycle contains it",
        "component_semantics": "a reached raw component remains one resource and continues, occurrence-labelled, through every distinct tree-edge contact with cotree support to both adjacent dual faces",
        "outer_boundary_semantics": "clockwise and counterclockwise occurrence walks displace reserved ports in order and stop at the first free port or contact-local cotree/component/internal continuation",
    }


def _comb_tree(n: int, axis: str, connector: int) -> tuple[Edge, ...]:
    if axis == "rows":
        edges = [edge for edge in grid_edges(n) if edge[1] == edge[0] + 1]
        edges.extend((row * n + connector, (row + 1) * n + connector) for row in range(n - 1))
    else:
        edges = [edge for edge in grid_edges(n) if edge[1] == edge[0] + n]
        edges.extend((connector * n + column, connector * n + column + 1) for column in range(n - 1))
    result = tuple(sorted(edges))
    if not is_tree(n * n, result):
        raise AssertionError("targeted comb construction is not a tree")
    return result


def targeted_spanning_trees(
    n: int, count: int, rng: random.Random
) -> tuple[tuple[str, tuple[Edge, ...]], ...]:
    """Return structured combs plus exchange-climbed high-collision trees."""
    candidates: dict[tuple[Edge, ...], str] = {}
    for axis in AXES:
        for connector in sorted({0, n // 2, n - 1}):
            tree = _comb_tree(n, axis, connector)
            candidates.setdefault(tree, f"{axis}-comb-{connector}")
    pressure_cache: dict[tuple[tuple[Edge, ...], str], tuple[int, int]] = {}

    def pressure(tree: tuple[Edge, ...], preferred_axis: str) -> tuple[int, int]:
        key = tree, preferred_axis
        if key in pressure_cache:
            return pressure_cache[key]
        counts = tuple(len(build_model(n, tree, axis).collisions) for axis in AXES)
        result = counts[AXES.index(preferred_axis)], sum(counts)
        pressure_cache[key] = result
        return result

    def exchange_neighbor(tree: tuple[Edge, ...]) -> tuple[Edge, ...]:
        tree_set = set(tree)
        added = rng.choice(tuple(edge for edge in grid_edges(n) if edge not in tree_set))
        adjacency = [[] for _ in range(n * n)]
        for left, right in tree:
            adjacency[left].append(right)
            adjacency[right].append(left)
        parent = {added[0]: -1}
        queue = [added[0]]
        for vertex in queue:
            if vertex == added[1]:
                break
            for other in adjacency[vertex]:
                if other not in parent:
                    parent[other] = vertex
                    queue.append(other)
        path = []
        vertex = added[1]
        while parent[vertex] != -1:
            path.append(_edge(vertex, parent[vertex]))
            vertex = parent[vertex]
        removed = rng.choice(path)
        return tuple(sorted((tree_set | {added}) - {removed}))

    climb_count = max(0, count - len(candidates))
    for index in range(climb_count):
        preferred_axis = AXES[index % len(AXES)]
        current = random_spanning_tree(n, rng)
        best = current
        for _step in range(20 * n):
            proposal = exchange_neighbor(current)
            if pressure(proposal, preferred_axis) >= pressure(current, preferred_axis) or rng.random() < 0.02:
                current = proposal
            if pressure(current, preferred_axis) > pressure(best, preferred_axis):
                best = current
        candidates.setdefault(
            best,
            f"{preferred_axis}-collision-climb-{index}-{pressure(best, preferred_axis)[0]}",
        )
    return tuple((name, tree) for tree, name in list(candidates.items())[:count])


def sampled_tree_census(
    n: int,
    *,
    random_count: int = 32,
    targeted_count: int = 16,
    seed: int = 20260816,
    all_gap_limit: int = 720,
    sampled_gap_count: int = 64,
    subset_limit: int = 12,
) -> dict[str, object]:
    """Search structured and random trees with exact Hall and bounded gap choices."""
    started = time.perf_counter()
    rng = random.Random(seed + n)
    trees = list(targeted_spanning_trees(n, targeted_count, rng))
    trees.extend(
        (f"wilson-{index}", random_spanning_tree(n, rng))
        for index in range(random_count)
    )
    seen_trees: set[tuple[Edge, ...]] = set()
    unique_trees = []
    for kind, tree in trees:
        if tree not in seen_trees:
            seen_trees.add(tree)
            unique_trees.append((kind, tree))

    axis_audits = gap_choices_tested = gap_choice_space = 0
    all_gap_audits = sampled_gap_audits = matching_audits = subset_audits = 0
    maximum_sources = 0
    failures: list[dict[str, object]] = []
    trees_with_a_failure = 0
    trees_with_both_axis_failures = 0
    for kind, tree in unique_trees:
        failed_axes = 0
        for axis in AXES:
            audit = audit_tree(
                n,
                tree,
                axis,
                all_gap_limit=all_gap_limit,
                sampled_gap_count=sampled_gap_count,
                rng=rng,
                subset_limit=subset_limit,
            )
            axis_audits += 1
            gap_choices_tested += audit.gap_choice_count
            gap_choice_space += audit.gap_choice_total
            maximum_sources = max(maximum_sources, audit.source_count)
            all_gap_audits += audit.gap_choice_mode == "all"
            sampled_gap_audits += audit.gap_choice_mode == "sampled"
            matching_audits += audit.hall_method == "matching"
            subset_audits += audit.hall_method == "subsets"
            if audit.hall_failure is not None:
                failed_axes += 1
                failures.append({
                    "tree_kind": kind,
                    "tree": list(tree),
                    "axis": axis,
                    "gap_choice_mode": audit.gap_choice_mode,
                    "gap_choices_tested": audit.gap_choice_count,
                    "gap_choice_total": audit.gap_choice_total,
                    "hall_method": audit.hall_method,
                    "gap_choice_failure": _jsonable(audit.first_failing_gap_choice),
                })
        trees_with_a_failure += failed_axes > 0
        trees_with_both_axis_failures += failed_axes == len(AXES)
    elapsed = time.perf_counter() - started
    return {
        "n": n,
        "seed": seed,
        "tree_count": len(unique_trees),
        "targeted_tree_count": sum(not kind.startswith("wilson-") for kind, _tree in unique_trees),
        "random_tree_count": sum(kind.startswith("wilson-") for kind, _tree in unique_trees),
        "axis_audits": axis_audits,
        "all_gap_bijection_audits": all_gap_audits,
        "sampled_gap_bijection_audits": sampled_gap_audits,
        "gap_bijections_tested": gap_choices_tested,
        "gap_bijection_space": gap_choice_space,
        "gap_sampling_cap": sampled_gap_count,
        "all_gap_bijection_limit": all_gap_limit,
        "all_source_subsets_limit": subset_limit,
        "subset_enumeration_audits": subset_audits,
        "exact_matching_audits": matching_audits,
        "maximum_collision_sources": maximum_sources,
        "hall_failure_count": len(failures),
        "trees_with_a_hall_failure": trees_with_a_failure,
        "trees_with_both_axes_hall_failures": trees_with_both_axis_failures,
        "hall_failures": failures,
        "elapsed_seconds": round(elapsed, 6),
        "trees_per_second": round(len(unique_trees) / elapsed, 3) if elapsed else None,
        "gap_choice_semantics": "all bijections when the exact product is at most the limit; otherwise distinct reproducible uniform samples",
        "hall_semantics": "all source subsets through the limit; otherwise exact bipartite maximum matching with an alternating Hall witness on failure",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, action="append", choices=range(3, 9), dest="widths")
    parser.add_argument("--output")
    parser.add_argument("--random-count", type=int, default=32)
    parser.add_argument("--targeted-count", type=int, default=16)
    parser.add_argument("--seed", type=int, default=20260816)
    parser.add_argument("--all-gap-limit", type=int, default=720)
    parser.add_argument("--sampled-gap-count", type=int, default=64)
    parser.add_argument("--subset-limit", type=int, default=12)
    args = parser.parse_args()
    widths = args.widths or [3, 4]
    result = {
        "censuses": [exhaustive_census(n) for n in widths if n <= 4],
        "sampled_searches": [
            sampled_tree_census(
                n,
                random_count=args.random_count,
                targeted_count=args.targeted_count,
                seed=args.seed,
                all_gap_limit=args.all_gap_limit,
                sampled_gap_count=args.sampled_gap_count,
                subset_limit=args.subset_limit,
            )
            for n in widths if n >= 5
        ],
    }
    rendered = json.dumps(result, indent=2, sort_keys=True)
    if args.output:
        with open(args.output, "w", encoding="ascii") as output:
            output.write(rendered + "\n")
    else:
        print(rendered)


if __name__ == "__main__":
    main()
