from __future__ import annotations

import unittest


Vertex = tuple[int, int]


def vertices(n: int) -> list[Vertex]:
    return [(r, c) for r in range(n) for c in range(n)]


def neighbors(n: int, vertex: Vertex) -> list[Vertex]:
    r, c = vertex
    return [
        (rr, cc)
        for rr, cc in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1))
        if 0 <= rr < n and 0 <= cc < n
    ]


def forced_edges(n: int, u_set: set[Vertex]) -> list[tuple[Vertex, Vertex]]:
    return [
        (v, w)
        for v in vertices(n)
        for w in neighbors(n, v)
        if v < w and not (v in u_set and w in u_set)
    ]


def component_labels(
    n: int, edges: list[tuple[Vertex, Vertex]]
) -> dict[Vertex, int] | None:
    parent = {v: v for v in vertices(n)}

    def root(v: Vertex) -> Vertex:
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for v, w in edges:
        rv, rw = root(v), root(w)
        if rv == rw:
            return None
        parent[rv] = rw
    roots: dict[Vertex, int] = {}
    return {v: roots.setdefault(root(v), len(roots)) for v in vertices(n)}


def valid(n: int, u_set: set[Vertex]) -> bool:
    return component_labels(n, forced_edges(n, u_set)) is not None


def exchange_is_valid_from_labels(
    n: int, u_set: set[Vertex], u: Vertex, labels: dict[Vertex, int]
) -> bool:
    # Changing u to F adds exactly its formerly omitted U-U edges. Those
    # edges form a star, so they are acyclic after contracting old H-components
    # exactly when all component labels at the star's ends are distinct.
    star_labels = [labels[u]] + [
        labels[v] for v in neighbors(n, u) if v in u_set
    ]
    return len(star_labels) == len(set(star_labels))


def parse(*rows: str) -> set[Vertex]:
    return {
        (r, c)
        for r, row in enumerate(rows)
        for c, value in enumerate(row)
        if value == "U"
    }


def side_f_counts(n: int, u_set: set[Vertex]) -> tuple[int, int, int, int]:
    is_f = lambda v: v not in u_set
    return (
        sum(is_f((0, c)) for c in range(n)),
        sum(is_f((n - 1, c)) for c in range(n)),
        sum(is_f((r, 0)) for r in range(n)),
        sum(is_f((r, n - 1)) for r in range(n)),
    )


class ForestExtremalInductionTests(unittest.TestCase):
    def test_exchange_criterion_exhaustively_through_n4(self) -> None:
        for n in range(2, 5):
            ordered = vertices(n)
            for mask in range(1 << (n * n)):
                u_set = {v for i, v in enumerate(ordered) if mask & (1 << i)}
                labels = component_labels(n, forced_edges(n, u_set))
                if labels is None:
                    continue
                for u in u_set:
                    predicted = exchange_is_valid_from_labels(n, u_set, u, labels)
                    actual = valid(n, u_set - {u})
                    self.assertEqual(predicted, actual)

    def test_maximal_n5_configuration_has_no_cheap_side(self) -> None:
        u_set = parse(
            "....U",
            "UUUUU",
            ".UUU.",
            ".UUU.",
            ".U.U.",
        )
        n = 5
        self.assertTrue(valid(n, u_set))
        self.assertTrue(all(not valid(n, u_set - {u}) for u in u_set))
        self.assertEqual(side_f_counts(n, u_set), (4, 3, 4, 3))
        self.assertGreater(min(side_f_counts(n, u_set)), (n + 2) / 3)

    def test_maximality_does_not_force_two_u_neighbors(self) -> None:
        u_set = parse("UU.", "UUU", "...")
        n = 3
        self.assertTrue(valid(n, u_set))
        self.assertTrue(all(not valid(n, u_set - {u}) for u in u_set))
        self.assertEqual(
            sum(v in u_set for v in neighbors(n, (1, 2))),
            1,
        )

    def test_no_boundary_f_corner_is_needed(self) -> None:
        u_set = parse("U.U", "U.U", "U.U")
        n = 3
        self.assertTrue(valid(n, u_set))
        self.assertTrue(all((r, c) in u_set for r in (0, 2) for c in (0, 2)))

    def test_four_boundary_segments_defeat_side_density_rule(self) -> None:
        # This is the scalable family from INCIDENCE_WASTE_EXCHANGE.md.
        for n in range(8, 20):
            f_set = (
                {(r, c) for r in range(1, n - 1) for c in (0, n - 1)}
                | {(r, c) for r in (0, n - 1) for c in range(2, n - 2)}
            )
            u_set = set(vertices(n)) - f_set
            self.assertTrue(valid(n, u_set))
            self.assertGreater(min(side_f_counts(n, u_set)), (n + 2) / 3)


if __name__ == "__main__":
    unittest.main()
