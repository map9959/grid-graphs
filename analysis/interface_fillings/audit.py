"""Re-enumerate saved cases using adjacency traversal, without Rust/union-find.

Run: python3 -m analysis.interface_fillings.audit INPUT.json OUTPUT.json
"""

import argparse
import hashlib
import json
from pathlib import Path


def rank(labels, edges):
    adjacency = [[] for _ in labels]
    edge_count = 0
    for v, w in edges:
        if labels[v] or labels[w]:
            adjacency[v].append(w)
            adjacency[w].append(v)
            edge_count += 1
    seen = set()
    components = 0
    for v in range(len(labels)):
        if v in seen:
            continue
        components += 1
        seen.add(v)
        stack = [v]
        while stack:
            for w in adjacency[stack.pop()]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
    return edge_count - len(labels) + components


def audit_case(case):
    n = len(case["baseline"])
    baseline = [ch == "." for row in case["baseline"] for ch in row]
    region = set(case["region"])
    optional = [v for v in case["region"] if not baseline[v]]
    edges = [(y * n + x, yy * n + xx)
             for y in range(n) for x in range(n)
             for xx, yy in [(x + 1, y), (x, y + 1)]
             if xx < n and yy < n]
    local = [(v, w) for v, w in edges if v in region or w in region]
    legal_count = relaxed_count = 0
    optimum = relaxed_optimum = penalty_optimum = 0
    unit_price_failure = None
    for mask in range(1 << len(optional)):
        labels = baseline.copy()
        for i, v in enumerate(optional):
            labels[v] = bool(mask & (1 << i))
        actual_rank = rank(labels, edges)
        relaxed_rank = rank(labels, local)
        gain = mask.bit_count()
        if actual_rank == 0:
            legal_count += 1
            optimum = max(optimum, gain)
        if relaxed_rank == 0:
            relaxed_count += 1
            relaxed_optimum = max(relaxed_optimum, gain)
            penalty_optimum = max(penalty_optimum, gain - 2 * actual_rank)
            if gain - actual_rank > case["result"]["optimum"] and unit_price_failure is None:
                unit_price_failure = {
                    "case": case["name"], "baseline": case["baseline"],
                    "region": case["region"], "ports": case["ports"],
                    "candidate_rows": ["".join("." if f else "U" for f in labels[y*n:(y+1)*n]) for y in range(n)],
                    "gain": gain, "cycle_rank": actual_rank,
                    "actual_optimum": case["result"]["optimum"],
                }
    result = case["result"]
    assert (legal_count, relaxed_count, optimum, relaxed_optimum) == (
        result["feasible"], result["relaxed_feasible"],
        result["optimum"], result["relaxed_optimum"]), case["name"]
    assert result["tested"] == 1 << len(optional)
    assert penalty_optimum == optimum
    best = [ch == "." for row in result["best_rows"] for ch in row]
    assert rank(best, edges) == 0
    for v in range(n * n):
        if v not in region or baseline[v]:
            assert best[v] == baseline[v]
    assert sum(best[v] for v in optional) == optimum
    return unit_price_failure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    summary = {"input_sha256": hashlib.sha256(raw).hexdigest(), "families": {}}
    for family in ("four_square", "moving_seams"):
        cases = data[family]
        failures = [failure for case in cases if (failure := audit_case(case)) is not None]
        worst = max(cases, key=lambda c: c["result"]["relaxed_optimum"] - c["result"]["optimum"])
        result = {
            "cases": len(cases),
            "fillings": sum(c["result"]["tested"] for c in cases),
            "legal": sum(c["result"]["feasible"] for c in cases),
            "positive_price": sum(c["result"]["relaxed_optimum"] > c["result"]["optimum"] for c in cases),
            "max_price": worst["result"]["relaxed_optimum"] - worst["result"]["optimum"],
            "first_max_price_case": worst,
            "cases_with_unit_rank_penalty_failure": len(failures),
            "first_unit_rank_penalty_failure": failures[0] if failures else None,
        }
        summary["families"][family] = result
        print(f"{family}: audited {result['cases']} cases, {result['fillings']} fillings; "
              f"max price {result['max_price']} at {worst['name']}; "
              f"actual/relaxed optimum {worst['result']['optimum']}/{worst['result']['relaxed_optimum']}")
        if failures:
            print("First unit-rank penalty failure:", json.dumps(failures[0]))
    with args.output.open("x") as output:
        json.dump(summary, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
