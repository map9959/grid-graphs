from __future__ import annotations

import argparse
import random
import unittest
from dataclasses import dataclass


@dataclass(frozen=True)
class AnnularData:
    n: int
    mask: int
    q_u: int
    ledger: int
    inner_ledger: int
    mu_f: int
    mu_h: int
    a_f: int
    a_h: int
    s_f: int
    s_h: int
    r_uu: int
    r_uf: int
    r_fu: int
    r_ff: int

    @property
    def rho_u(self) -> int:
        return self.r_uu + self.r_fu

    @property
    def merger_margin(self) -> int:
        return self.rho_u - self.mu_f - self.mu_h

    @property
    def radial_margin(self) -> int:
        return self.a_h + self.a_f + self.r_uu - self.r_uf - 2 * self.r_ff

    @property
    def inherited_surplus(self) -> int:
        return self.inner_ledger - (self.n + 2)

    @property
    def annular_debt(self) -> int:
        return 2 - (self.ledger - self.inner_ledger)


class DSU:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.count = size

    def find(self, value: int) -> int:
        while self.parent[value] != value:
            self.parent[value] = self.parent[self.parent[value]]
            value = self.parent[value]
        return value

    def union(self, left: int, right: int) -> bool:
        left = self.find(left)
        right = self.find(right)
        if left == right:
            return False
        self.parent[right] = left
        self.count -= 1
        return True


def edges(n: int) -> list[tuple[int, int]]:
    return [
        (r * n + c, (r + 1) * n + c)
        for r in range(n - 1)
        for c in range(n)
    ] + [
        (r * n + c, r * n + c + 1)
        for r in range(n)
        for c in range(n - 1)
    ]


def boundary_order(n: int) -> list[int]:
    return (
        [c for c in range(n)]
        + [r * n + n - 1 for r in range(1, n)]
        + [(n - 1) * n + c for c in range(n - 2, -1, -1)]
        + [r * n for r in range(n - 2, 0, -1)]
    )


def analyze(n: int, mask: int) -> AnnularData | None:
    all_edges = edges(n)
    h = DSU(n * n)
    for left, right in all_edges:
        if mask >> left & 1 and mask >> right & 1:
            continue
        if not h.union(left, right):
            return None

    f_vertices = {vertex for vertex in range(n * n) if not (mask >> vertex & 1)}
    f = DSU(n * n)
    for left, right in all_edges:
        if left in f_vertices and right in f_vertices:
            f.union(left, right)
    c_f = len({f.find(vertex) for vertex in f_vertices})
    q_u = sum(
        ((vertex // n) in (0, n - 1)) + ((vertex % n) in (0, n - 1))
        for vertex in range(n * n)
        if mask >> vertex & 1
    )
    ledger = q_u + c_f + h.count

    inner_vertices = [
        r * n + c for r in range(1, n - 1) for c in range(1, n - 1)
    ]
    inner_mask = 0
    for index, vertex in enumerate(inner_vertices):
        inner_mask |= ((mask >> vertex) & 1) << index
    inner_n = n - 2
    inner = base_ledger(inner_n, inner_mask)

    boundary = boundary_order(n)
    boundary_set = set(boundary)
    inner_set = set(inner_vertices)
    radial = [
        (left, right) if left in boundary_set else (right, left)
        for left, right in all_edges
        if (left in boundary_set) != (right in boundary_set)
    ]
    radial_types = [0, 0, 0, 0]  # UU, UF, FU, FF
    for outer, inward in radial:
        outer_u = mask >> outer & 1
        inner_u = mask >> inward & 1
        radial_types[(not outer_u) * 2 + (not inner_u)] += 1

    # Components are represented by their DSU roots.  The incidence graph is
    # itself a forest, so mu = teeth - attached boundary components.
    h_boundary = DSU(n * n)
    f_boundary = DSU(n * n)
    for index, left in enumerate(boundary):
        right = boundary[(index + 1) % len(boundary)]
        if not (mask >> left & 1 and mask >> right & 1):
            h_boundary.union(left, right)
        if not (mask >> left & 1) and not (mask >> right & 1):
            f_boundary.union(left, right)

    h_teeth = [(outer, inward) for outer, inward in radial if not (mask >> outer & 1 and mask >> inward & 1)]
    f_teeth = [(outer, inward) for outer, inward in radial if not (mask >> outer & 1) and not (mask >> inward & 1)]
    a_h = len({h_boundary.find(outer) for outer, _ in h_teeth})
    a_f = len({f_boundary.find(outer) for outer, _ in f_teeth})
    p_h = len({h_boundary.find(vertex) for vertex in boundary})
    boundary_f = [vertex for vertex in boundary if not (mask >> vertex & 1)]
    p_f = len({f_boundary.find(vertex) for vertex in boundary_f})

    return AnnularData(
        n=n,
        mask=mask,
        q_u=q_u,
        ledger=ledger,
        inner_ledger=inner,
        mu_f=len(f_teeth) - a_f,
        mu_h=len(h_teeth) - a_h,
        a_f=a_f,
        a_h=a_h,
        s_f=p_f - a_f,
        s_h=p_h - a_h,
        r_uu=radial_types[0],
        r_uf=radial_types[1],
        r_fu=radial_types[2],
        r_ff=radial_types[3],
    )


def base_ledger(n: int, mask: int) -> int:
    if n == 0:
        return 0
    all_edges = edges(n)
    h = DSU(n * n)
    f = DSU(n * n)
    for left, right in all_edges:
        if not (mask >> left & 1 and mask >> right & 1):
            h.union(left, right)
        if not (mask >> left & 1) and not (mask >> right & 1):
            f.union(left, right)
    f_vertices = [vertex for vertex in range(n * n) if not (mask >> vertex & 1)]
    c_f = len({f.find(vertex) for vertex in f_vertices})
    q_u = sum(
        ((vertex // n) in (0, n - 1)) + ((vertex % n) in (0, n - 1))
        for vertex in range(n * n)
        if mask >> vertex & 1
    )
    return q_u + c_f + h.count


def format_rows(n: int, mask: int) -> tuple[str, ...]:
    return tuple(
        "".join("U" if mask >> (r * n + c) & 1 else "." for c in range(n))
        for r in range(n)
    )


def centered_mask(n: int, mask: int, inset: int) -> int:
    side = n - 2 * inset
    result = 0
    for row in range(side):
        for column in range(side):
            vertex = (row + inset) * n + column + inset
            result |= ((mask >> vertex) & 1) << (row * side + column)
    return result


def randomized_search(n: int, trials: int, seed: int) -> tuple[AnnularData, int]:
    rng = random.Random(seed)
    best: AnnularData | None = None
    valid = 0
    for _ in range(trials):
        density = rng.uniform(0.45, 0.95)
        mask = sum(
            (rng.random() < density) << vertex for vertex in range(n * n)
        )
        data = analyze(n, mask)
        if data is None:
            continue
        valid += 1
        if best is None or data.merger_margin < best.merger_margin:
            best = data
    if best is None:
        raise RuntimeError("random search found no forest-valid pattern")
    return best, valid


class AnnularMergerTests(unittest.TestCase):
    def test_exact_through_n4(self) -> None:
        expected_valid = {3: 100, 4: 2_278}
        expected_margin = {3: 0, 4: 4}
        for n in (3, 4):
            data = [
                result
                for mask in range(1 << (n * n))
                if (result := analyze(n, mask)) is not None
            ]
            self.assertEqual(len(data), expected_valid[n])
            self.assertEqual(min(item.merger_margin for item in data), expected_margin[n])
            for item in data:
                self.assertEqual(item.merger_margin, item.radial_margin)
                self.assertGreaterEqual(item.inherited_surplus, item.annular_debt)

    def test_known_negative_annular_increment(self) -> None:
        data = analyze(4, 3942)
        assert data is not None
        self.assertEqual(format_rows(4, data.mask), (".UU.", ".UU.", "UUUU", "...."))
        self.assertEqual((data.inherited_surplus, data.annular_debt), (6, 6))

    def test_two_annulus_scalar_pooling_has_n6_counterexample(self) -> None:
        data = analyze(6, 30_458_370_000)
        assert data is not None
        self.assertEqual(
            format_rows(6, data.mask),
            ("....U.", "UUUUU.", "U.UUU.", "U.UUU.", "UUU.U.", "..UUU."),
        )
        central_ledger = base_ledger(2, centered_mask(6, data.mask, 2))
        self.assertEqual((data.ledger, central_ledger), (15, 12))
        self.assertEqual(data.ledger - central_ledger, 3)

    def test_boundary_deficiency_linear_potential_is_infeasible(self) -> None:
        # Monotonicity of P-alpha*Q across an annulus would require
        # (1-alpha)(Q-Q_inner)+s_F+s_H-mu_F-mu_H >= 2.
        lower = analyze(4, 3942)
        upper = analyze(4, 4026)
        assert lower is not None and upper is not None
        self.assertEqual(
            (lower.q_u - lower.rho_u, lower.s_f + lower.s_h - lower.mu_f - lower.mu_h),
            (-4, 0),
        )
        self.assertEqual(
            (upper.q_u - upper.rho_u, upper.s_f + upper.s_h - upper.mu_f - upper.mu_h),
            (1, 1),
        )
        # The first transition forces alpha >= 3/2; the second forces alpha <= 0.


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--random-n", type=int)
    parser.add_argument("--trials", type=int, default=100_000)
    parser.add_argument("--seed", type=int, default=20260806)
    args, unittest_args = parser.parse_known_args()
    if args.random_n is None:
        unittest.main(argv=[__file__, *unittest_args])
    else:
        result, valid_count = randomized_search(args.random_n, args.trials, args.seed)
        print(f"valid={valid_count} minimum_margin={result.merger_margin}")
        print("\n".join(format_rows(result.n, result.mask)))
        print(result)
