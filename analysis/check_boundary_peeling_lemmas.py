from __future__ import annotations

import unittest
from dataclasses import dataclass


Vertex = tuple[int, int]
Edge = tuple[Vertex, Vertex]


def grid_edges(n: int) -> list[Edge]:
    return [
        ((r, c), (r + 1, c)) for r in range(n - 1) for c in range(n)
    ] + [((r, c), (r, c + 1)) for r in range(n) for c in range(n - 1)]


def components(vertices: set[Vertex], edges: list[Edge]) -> list[set[Vertex]]:
    adjacency = {vertex: set() for vertex in vertices}
    for left, right in edges:
        if left in adjacency and right in adjacency:
            adjacency[left].add(right)
            adjacency[right].add(left)

    result: list[set[Vertex]] = []
    while adjacency:
        stack = [next(iter(adjacency))]
        component: set[Vertex] = set()
        while stack:
            vertex = stack.pop()
            if vertex in component:
                continue
            component.add(vertex)
            stack.extend(adjacency[vertex] - component)
        for vertex in component:
            del adjacency[vertex]
        result.append(component)
    return result


def is_forest(vertices: set[Vertex], edges: list[Edge]) -> bool:
    return len(edges) == len(vertices) - len(components(vertices, edges))


@dataclass(frozen=True)
class CombData:
    boundary_components: int
    inner_components: int
    teeth: int
    unattached_backbones: int
    mergers: int


@dataclass(frozen=True)
class PatternData:
    n: int
    mask: int
    u_count: int
    q_u: int
    c_f: int
    c_h: int
    inner_q_u: int | None
    f_comb: CombData | None
    h_comb: CombData | None

    @property
    def ledger(self) -> int:
        return self.q_u + self.c_f + self.c_h


def comb_data(
    vertices: set[Vertex],
    edges: list[Edge],
    boundary: set[Vertex],
) -> CombData:
    inner = vertices - boundary
    boundary_components = components(
        vertices & boundary,
        [edge for edge in edges if edge[0] in boundary and edge[1] in boundary],
    )
    inner_components = components(
        inner,
        [edge for edge in edges if edge[0] in inner and edge[1] in inner],
    )
    boundary_owner = {
        vertex: index
        for index, component in enumerate(boundary_components)
        for vertex in component
    }
    inner_owner = {
        vertex: index
        for index, component in enumerate(inner_components)
        for vertex in component
    }
    teeth: list[tuple[int, int]] = []
    for left, right in edges:
        if left in boundary and right in inner:
            teeth.append((boundary_owner[left], inner_owner[right]))
        elif right in boundary and left in inner:
            teeth.append((boundary_owner[right], inner_owner[left]))

    # Parallel owner pairs would be a two-cycle after contraction.
    if len(teeth) != len(set(teeth)):
        raise AssertionError("two teeth join the same pair of components")

    incidence_vertices = {("b", backbone) for backbone, _ in teeth} | {
        ("i", target) for _, target in teeth
    }
    incidence_edges = [(("b", backbone), ("i", target)) for backbone, target in teeth]
    incidence_components = components(incidence_vertices, incidence_edges)  # type: ignore[arg-type]
    if not is_forest(incidence_vertices, incidence_edges):  # type: ignore[arg-type]
        raise AssertionError("contracted comb incidence graph has a cycle")

    attached_backbones = len({backbone for backbone, _ in teeth})
    touched_inner = len({target for _, target in teeth})
    mergers = touched_inner - len(incidence_components)
    return CombData(
        boundary_components=len(boundary_components),
        inner_components=len(inner_components),
        teeth=len(teeth),
        unattached_backbones=len(boundary_components) - attached_backbones,
        mergers=mergers,
    )


def analyze(n: int, mask: int) -> PatternData | None:
    vertices = {(row, column) for row in range(n) for column in range(n)}
    ordered = sorted(vertices)
    u = {vertex for index, vertex in enumerate(ordered) if mask & (1 << index)}
    f = vertices - u
    edges = grid_edges(n)
    h_edges = [edge for edge in edges if not ({edge[0], edge[1]} <= u)]
    if not is_forest(vertices, h_edges):
        return None

    f_edges = [edge for edge in edges if edge[0] in f and edge[1] in f]
    q_u = sum(
        (row in (0, n - 1)) + (column in (0, n - 1)) for row, column in u
    )
    c_f = len(components(f, f_edges))
    c_h = len(components(vertices, h_edges))
    if n < 3:
        return PatternData(n, mask, len(u), q_u, c_f, c_h, None, None, None)

    boundary = {
        vertex
        for vertex in vertices
        if vertex[0] in (0, n - 1) or vertex[1] in (0, n - 1)
    }
    inner = vertices - boundary
    radial = [edge for edge in edges if bool(edge[0] in boundary) != bool(edge[1] in boundary)]
    inner_q_u = sum(
        1
        for left, right in radial
        if (left in inner and left in u) or (right in inner and right in u)
    )
    return PatternData(
        n,
        mask,
        len(u),
        q_u,
        c_f,
        c_h,
        inner_q_u,
        comb_data(f, f_edges, boundary),
        comb_data(vertices, h_edges, boundary),
    )


def rows(data: PatternData) -> tuple[str, ...]:
    return tuple(
        "".join(
            "U" if data.mask & (1 << (row * data.n + column)) else "."
            for column in range(data.n)
        )
        for row in range(data.n)
    )


def exhaustive(n: int) -> list[PatternData]:
    return [
        data
        for mask in range(1 << (n * n))
        if (data := analyze(n, mask)) is not None
    ]


class BoundaryPeelingLemmaTests(unittest.TestCase):
    def test_all_forest_valid_patterns_through_n4(self) -> None:
        expected_counts = {2: 9, 3: 100, 4: 2_278}
        expected_minimum_ledgers = {2: 6, 3: 9, 4: 8}
        for n in range(2, 5):
            patterns = exhaustive(n)
            self.assertEqual(len(patterns), expected_counts[n])
            self.assertEqual(min(data.ledger for data in patterns), expected_minimum_ledgers[n])
            for data in patterns:
                # This is the global component identity, not an assumed bound.
                self.assertEqual(
                    data.ledger,
                    3 * data.u_count - 2 * (n - 1) ** 2 + 2,
                )
                self.assertGreaterEqual(data.ledger, n + 4)

    def test_exact_peeling_and_comb_merger_identities(self) -> None:
        for n in range(3, 5):
            for data in exhaustive(n):
                assert data.f_comb is not None and data.h_comb is not None
                for total_components, comb in (
                    (data.c_f, data.f_comb),
                    (data.c_h, data.h_comb),
                ):
                    self.assertEqual(
                        total_components,
                        comb.inner_components + comb.boundary_components - comb.teeth,
                    )
                    self.assertEqual(
                        total_components,
                        comb.inner_components + comb.unattached_backbones - comb.mergers,
                    )

    def test_scalar_plus_two_annular_bound_has_n4_counterexample(self) -> None:
        outer = analyze(4, 3942)
        inner = analyze(2, 15)
        assert outer is not None and inner is not None
        self.assertEqual(rows(outer), (".UU.", ".UU.", "UUUU", "...."))
        self.assertEqual((outer.ledger, inner.ledger), (8, 12))
        self.assertEqual(outer.ledger - inner.ledger, -4)
        assert outer.f_comb is not None and outer.h_comb is not None
        self.assertEqual(
            (
                outer.q_u,
                outer.inner_q_u,
                outer.f_comb.unattached_backbones + outer.h_comb.unattached_backbones,
                outer.f_comb.mergers + outer.h_comb.mergers,
            ),
            (4, 8, 3, 3),
        )

    def test_unproved_merger_bound_small_grid_evidence(self) -> None:
        # This deliberately tests evidence for, rather than claims a proof of,
        # mu_F + mu_H <= the number of U-ended radial edges.
        minimum_margins = {}
        for n in range(3, 5):
            margins = []
            for data in exhaustive(n):
                assert data.f_comb is not None and data.h_comb is not None
                assert data.inner_q_u is not None
                margins.append(
                    data.inner_q_u - data.f_comb.mergers - data.h_comb.mergers
                )
            minimum_margins[n] = min(margins)
        self.assertEqual(minimum_margins, {3: 0, 4: 4})


if __name__ == "__main__":
    unittest.main()
