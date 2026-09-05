#!/usr/bin/env python3
"""Exact finite census for the forced-forest boundary-charge reduction.

For a forced set F, U is its complement and H contains every grid edge with at
least one endpoint in F.  All computations here are finite checks, not proofs
for uncomputed widths.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path

from diagonal_patterns import (
    residue_one_pattern,
    residue_two_pattern,
    residue_zero_explicit_pattern,
)
from forced_forest_row_grammar import (
    State,
    _DisjointSet,
    first_row_state,
    is_forced_forest,
    transition,
)
from max_fr_checker import TARGETED_MAXIMUM_WITNESSES, maximum_witnesses


@dataclass(frozen=True)
class Charges:
    n: int
    forced_count: int
    boundary_charge: int
    isolated_u: int
    branching_credit: int
    nonisolated_h_components: int
    f_components: int
    charged_expression: int
    target: int


def boundary_charges(n: int, rows: tuple[int, ...]) -> Charges:
    """Compute B_F, d_F-derived credits, and H/G[F] component counts directly."""
    if len(rows) != n or not is_forced_forest(n, list(rows)):
        raise ValueError("rows must describe an acyclic forced set")

    forced = {r * n + c for r in range(n) for c in range(n) if rows[r] >> c & 1}
    h_dsu = _DisjointSet(n * n)
    f_dsu = _DisjointSet(n * n)
    d_f = [0] * (n * n)
    h_edges = 0
    f_edges = 0
    boundary_charge = 0

    for r in range(n):
        for c in range(n):
            vertex = r * n + c
            degree = (r > 0) + (r + 1 < n) + (c > 0) + (c + 1 < n)
            if vertex in forced:
                boundary_charge += 4 - degree
            for dr, dc in ((0, 1), (1, 0)):
                rr, cc = r + dr, c + dc
                if rr >= n or cc >= n:
                    continue
                other = rr * n + cc
                left_forced = vertex in forced
                right_forced = other in forced
                if left_forced or right_forced:
                    if not h_dsu.union_edge(vertex, other):
                        raise AssertionError("direct H construction found a cycle")
                    h_edges += 1
                if left_forced and right_forced:
                    if not f_dsu.union_edge(vertex, other):
                        raise AssertionError("G[F] cycled inside H")
                    f_edges += 1
                if left_forced != right_forced:
                    d_f[other if left_forced else vertex] += 1

    u = set(range(n * n)) - forced
    isolated_u = sum(d_f[vertex] == 0 for vertex in u)
    branching_credit = sum(max(0, d_f[vertex] - 1) for vertex in u)
    # Remove precisely the isolated U vertices.  The remaining H components
    # normally contain edges; this formulation also handles the one-vertex grid.
    nonisolated_h_components = (
        len({h_dsu.find(vertex) for vertex in range(n * n)}) - isolated_u
    )
    f_components = len(forced) - f_edges
    charged_expression = (
        boundary_charge
        - isolated_u
        - branching_credit
        - 2 * nonisolated_h_components
    )

    # Independent edge/component and quotient-forest replays of both identities.
    assert h_edges == n * n - isolated_u - nonisolated_h_components
    assert f_components == nonisolated_h_components + branching_credit
    assert 3 * len(forced) == n * n + charged_expression
    return Charges(
        n=n,
        forced_count=len(forced),
        boundary_charge=boundary_charge,
        isolated_u=isolated_u,
        branching_credit=branching_credit,
        nonisolated_h_components=nonisolated_h_components,
        f_components=f_components,
        charged_expression=charged_expression,
        target=3 * n - 4,
    )


def _render(rows: tuple[int, ...]) -> list[str]:
    n = len(rows)
    return ["".join("F" if mask >> c & 1 else "U" for c in range(n)) for mask in rows]


def exhaustive_sets(n: int):
    row_mask = (1 << n) - 1
    for flat in range(1 << (n * n)):
        rows = tuple((flat >> (r * n)) & row_mask for r in range(n))
        if is_forced_forest(n, list(rows)):
            yield rows


def maximum_forced_plus_isolated(n: int) -> tuple[int, int, tuple[int, ...]]:
    """Exactly maximize 3|F|+U0 over every forced forest using the row grammar."""
    limit = 1 << n

    def pending(mask: int, forced_above: int) -> int:
        horizontal_forced = ((mask << 1) | (mask >> 1)) & (limit - 1)
        return (limit - 1) & ~mask & ~horizontal_forced & ~forced_above

    costs: dict[tuple[State, int], tuple[int, tuple[int, ...]]] = {}
    for mask in range(limit):
        state = first_row_state(n, mask)
        if state is not None:
            costs[(state, pending(mask, 0))] = (3 * mask.bit_count(), (mask,))
    peak = len(costs)
    for _row in range(1, n):
        next_costs: dict[tuple[State, int], tuple[int, tuple[int, ...]]] = {}
        for (state, pending_above), (cost, rows) in costs.items():
            for mask in range(limit):
                next_state = transition(n, state, mask)
                if next_state is None:
                    continue
                value = (
                    cost
                    + 3 * mask.bit_count()
                    + (pending_above & ~mask).bit_count()
                )
                key = (next_state, pending(mask, state.forced_mask))
                if value > next_costs.get(key, (-1, ()))[0]:
                    next_costs[key] = (value, rows + (mask,))
        costs = next_costs
        peak = max(peak, len(costs))
    maximum, rows = max(
        (cost + pending_mask.bit_count(), rows)
        for (_state, pending_mask), (cost, rows) in costs.items()
    )
    return maximum, peak, rows


def canonical_rows(n: int) -> tuple[int, ...]:
    if n % 3 == 0:
        pattern = residue_zero_explicit_pattern(n)
    elif n % 3 == 1:
        pattern = residue_one_pattern(n)
    else:
        pattern = residue_two_pattern(n)
    return tuple(sum((ch == ".") << c for c, ch in enumerate(row)) for row in pattern)


def exact_maxima() -> dict[int, int]:
    path = Path(__file__).parents[1] / "data" / "diagonal.csv"
    result = {}
    with path.open(newline="") as source:
        for row in csv.reader(source):
            if not row or not row[0].isdigit() or "lower bound" in row[-1]:
                continue
            result[int(row[0])] = int(row[1])
    return result


def candidate_reductions(samples: list[tuple[Charges, tuple[int, ...]]]) -> list[dict]:
    """Test small nonnegative integer credits; lower coefficients are stronger."""
    records = []
    for isolated_coefficient in range(2):
        for branching_coefficient in range(2):
            for component_coefficient in range(3):
                margins = [
                    item.target
                    - (
                        item.boundary_charge
                        - isolated_coefficient * item.isolated_u
                        - branching_coefficient * item.branching_credit
                        - component_coefficient * item.nonisolated_h_components
                    )
                    for item, _rows in samples
                ]
                worst = min(range(len(samples)), key=margins.__getitem__)
                worst_item, worst_rows = samples[worst]
                records.append(
                    {
                        "coefficients": [
                            isolated_coefficient,
                            branching_coefficient,
                            component_coefficient,
                        ],
                        "holds_on_samples": min(margins) >= 0,
                        "minimum_margin": min(margins),
                        "worst_example": {
                            "rows": _render(worst_rows),
                            **asdict(worst_item),
                        },
                    }
                )
    passing = [record for record in records if record["holds_on_samples"]]
    for record in records:
        a, b, c = record["coefficients"]
        record["pareto_strongest"] = record in passing and not any(
            other["coefficients"] != record["coefficients"]
            and all(x <= y for x, y in zip(other["coefficients"], (a, b, c)))
            for other in passing
        )
    return records


def build_report(
    brute_max_n: int = 4,
    exhaustive_maximum_n: int = 6,
    augmented_max_n: int = 7,
) -> dict:
    all_samples: list[tuple[Charges, tuple[int, ...]]] = []
    exhaustive = []
    equality_examples = []
    for n in range(3, brute_max_n + 1):
        valid = 0
        violations = 0
        equalities = 0
        max_forced = -1
        for rows in exhaustive_sets(n):
            item = boundary_charges(n, rows)
            all_samples.append((item, rows))
            valid += 1
            max_forced = max(max_forced, item.forced_count)
            violations += item.charged_expression > item.target
            if item.charged_expression == item.target:
                equalities += 1
                if len(equality_examples) < 8:
                    equality_examples.append({"n": n, "rows": _render(rows), **asdict(item)})
        exhaustive.append(
            {
                "n": n,
                "acyclic_forced_sets": valid,
                "maximum_forced_count": max_forced,
                "target_violations": violations,
                "target_equalities": equalities,
            }
        )

    maximum_records = []
    for n in range(3, exhaustive_maximum_n + 1):
        witnesses = list(maximum_witnesses(n))
        items = [boundary_charges(n, rows) for rows in witnesses]
        all_samples.extend(zip(items, witnesses))
        maximum_records.append(
            {
                "n": n,
                "coverage": "all maximum witnesses",
                "checked": len(items),
                "forced_count": items[0].forced_count,
                "charge_distribution": dict(Counter(item.charged_expression for item in items)),
                "equality_count": sum(item.charged_expression == item.target for item in items),
            }
        )

    certified = exact_maxima()
    for n in range(exhaustive_maximum_n + 1, 16):
        rows = canonical_rows(n)
        candidates = {rows, *TARGETED_MAXIMUM_WITNESSES.get(n, ())}
        items = [boundary_charges(n, candidate) for candidate in sorted(candidates)]
        all_samples.extend(zip(items, sorted(candidates)))
        expected = certified.get(n)
        maximum_records.append(
            {
                "n": n,
                "coverage": "cached/canonical maximum witnesses" if expected is not None else "target-count witness; maximum not certified in diagonal.csv",
                "checked": len(items),
                "forced_count_distribution": dict(Counter(item.forced_count for item in items)),
                "recorded_exact_maximum": expected,
                "all_match_recorded_maximum": expected is not None and all(item.forced_count == expected for item in items),
                "charge_distribution": dict(Counter(item.charged_expression for item in items)),
                "equality_count": sum(item.charged_expression == item.target for item in items),
            }
        )

    augmented = []
    for n in range(3, augmented_max_n + 1):
        maximum, peak, rows = maximum_forced_plus_isolated(n)
        bound = n * n + 3 * n - 4
        item = boundary_charges(n, rows)
        assert maximum == 3 * item.forced_count + item.isolated_u
        all_samples.append((item, rows))
        augmented.append(
            {
                "n": n,
                "maximum_3F_plus_U0": maximum,
                "bound": bound,
                "margin": bound - maximum,
                "peak_product_states": peak,
                "maximizing_rows": _render(rows),
            }
        )

    return {
        "definitions": {
            "B_F": "sum over v in F of (4-deg_G(v))",
            "d_F(u)": "number of grid neighbors of u in F, for u in U",
            "U0": "number of u in U with d_F(u)=0; equivalently isolated vertices of H",
            "branching_credit": "sum over u in U with d_F(u)>=2 of d_F(u)-1",
            "c_nonisolated": "number of H components other than the isolated U vertices U0",
        },
        "identities_checked": [
            "c(G[F]) = c_nonisolated + branching_credit",
            "3|F| = n^2 + B_F - U0 - branching_credit - 2*c_nonisolated",
        ],
        "exhaustive_all_sets": exhaustive,
        "exact_augmented_row_grammar": augmented,
        "maximum_witnesses": maximum_records,
        "equality_examples": equality_examples,
        "candidate_coefficient_order": "[U0, branching_credit, c_nonisolated]; smaller is a stronger inequality",
        "candidate_reductions": candidate_reductions(all_samples),
        "scope": "finite exact checks only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brute-max-n", type=int, default=4)
    parser.add_argument("--exhaustive-maximum-n", type=int, default=6)
    parser.add_argument("--augmented-max-n", type=int, default=7)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = build_report(
        args.brute_max_n,
        args.exhaustive_maximum_n,
        args.augmented_max_n,
    )
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
