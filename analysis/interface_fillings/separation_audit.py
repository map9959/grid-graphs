"""Independent exhaustive terminal-separation audit using full adjacency traversal.

python3 -m analysis.interface_fillings.separation_audit INPUT.json OUTPUT.json
"""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from .replacements_audit import labels


def components(state, edges):
    adjacency = [[] for _ in state]
    for v, w in edges:
        if state[v] or state[w]:
            adjacency[v].append(w)
            adjacency[w].append(v)
    roots = [-1] * len(state)
    count = 0
    forest = True
    for start in range(len(state)):
        if roots[start] >= 0:
            continue
        roots[start] = count
        stack = [start]
        size = degree = 0
        while stack:
            v = stack.pop()
            size += 1
            degree += len(adjacency[v])
            for w in adjacency[v]:
                if roots[w] < 0:
                    roots[w] = count
                    stack.append(w)
        forest &= degree == 2 * (size - 1)
        count += 1
    return roots, count, forest


def filled(baseline, region, mask):
    state = baseline.copy()
    for i, v in enumerate(region):
        state[v] = bool(mask & (1 << i))
    return state


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    summary = {"input_sha256": hashlib.sha256(raw).hexdigest(),
               "scope": "independent exhaustive enumeration and monotonic path exclusions",
               "boards": []}
    for board in data["boards"]:
        original = labels(board["original"]["rows"])
        n = len(board["original"]["rows"])
        edges = [(y*n+x, yy*n+xx) for y in range(n) for x in range(n)
                 for xx, yy in [(x+1, y), (x, y+1)] if xx < n and yy < n]
        original_roots, original_c, forest = components(original, edges)
        assert forest
        neighbors = [[] for _ in original]
        for v, w in edges:
            neighbors[v].append(w)
            neighbors[w].append(v)
        expected_terminals = []
        for v, is_f in enumerate(original):
            holes = [w for w in neighbors[v] if not original[w]]
            if not is_f and len(holes) == 1 and original_roots[v] == original_roots[holes[0]]:
                expected_terminals.append({"v": v, "w": holes[0]})
        assert expected_terminals == board["terminals"]
        expected_regions = [[yy*n+xx for yy in range(y, y+h) for xx in range(x, x+w)]
                            for w, h in [(3, 4), (4, 3)]
                            for y in range(1, n-h) for x in range(1, n-w)]
        assert expected_regions == [c["region"] for c in board["cases"]]
        histogram = Counter()
        pairs = monotonic = tested = successes = 0
        first_counterexample = None
        successful = []
        for case in board["cases"]:
            region = case["region"]
            baseline = original.copy()
            for v in region:
                baseline[v] = False
            base_roots, _, forest = components(baseline, edges)
            assert forest
            old = sum(original[v] for v in region)
            assert old == case["original_score"]
            assert case["original_components"] == original_c
            expected_pairs = [t for t in expected_terminals if t["v"] not in region
                              and all(w not in region for w in neighbors[t["v"]])]
            assert expected_pairs == [t["terminal"] for t in case["terminals"]]
            best = [None] * len(expected_pairs)
            neutral = [False] * len(expected_pairs)
            severable = []
            for t in case["terminals"]:
                v, w = t["terminal"]["v"], t["terminal"]["w"]
                split = base_roots[v] != base_roots[w]
                assert split == t["clearing_separates"]
                severable.append(split)
                monotonic += not split
                pairs += 1
            if any(severable):
                count = 0
                for mask in range(1 << len(region)):
                    state = filled(baseline, region, mask)
                    roots, _, forest = components(state, edges)
                    if not forest:
                        continue
                    count += 1
                    score = mask.bit_count()
                    for i, t in enumerate(expected_pairs):
                        if roots[t["v"]] != roots[t["w"]]:
                            best[i] = max(best[i] or 0, score)
                            neutral[i] |= score == old
                assert case["fillings_tested"] == 1 << len(region)
                assert case["feasible_fillings"] == count
                tested += case["fillings_tested"]
            else:
                assert case["fillings_tested"] == case["feasible_fillings"] == 0
            for i, t in enumerate(case["terminals"]):
                assert best[i] == t["best_separated"]
                assert neutral[i] == (t["neutral_mask"] is not None)
                v, w = t["terminal"]["v"], t["terminal"]["w"]
                if best[i] is not None:
                    witness = filled(baseline, region, t["best_mask"])
                    roots, _, forest = components(witness, edges)
                    assert forest and roots[v] != roots[w]
                    assert sum(witness[u] for u in region) == best[i]
                    deficit = old - best[i]
                    histogram[deficit] += 1
                    if deficit > 0 and first_counterexample is None:
                        first_counterexample = {"region": region, "terminal": t["terminal"],
                            "old_score": old, "best_separated": best[i],
                            "original_rows": board["original"]["rows"],
                            "best_rows": ["".join("." if f else "U" for f in witness[y*n:(y+1)*n]) for y in range(n)]}
                if neutral[i]:
                    state = filled(baseline, region, t["neutral_mask"])
                    roots, count, forest = components(state, edges)
                    assert forest and roots[v] != roots[w]
                    assert sum(state) == sum(original)
                    assert count == t["neutral_components"]
                    assert t["neutral_deleted"] == [u for u in region if original[u] and not state[u]]
                    assert t["neutral_added"] == [u for u in region if state[u] and not original[u]]
                    state[v] = True
                    assert components(state, edges)[2]
                    assert state == labels(t["promoted_rows"])
                    successes += 1
                    successful.append({"region": region, **t})
        record = {"name": board["name"], "terminals": len(expected_terminals),
                  "compatible_pairs": pairs, "monotonic_obstructions": monotonic,
                  "separator_deficit_histogram": dict(sorted(histogram.items())),
                  "neutral_separators": successes, "fillings_audited": tested,
                  "first_counterexample": first_counterexample, "successes": successful}
        summary["boards"].append(record)
        print(board["name"], "pairs", pairs, "monotonic", monotonic,
              "deficits", dict(histogram), "neutral", successes, "fillings", tested)
    with args.output.open("x") as out:
        json.dump(summary, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
