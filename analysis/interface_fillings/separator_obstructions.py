"""Extract actual path-edge deletion certificates and sharp score-loss examples.

python3 -m analysis.interface_fillings.separator_obstructions INPUT.json OUTPUT.json
"""

import argparse
import hashlib
import json
from pathlib import Path

from .replacements_audit import labels
from .separation_audit import components, filled
from .terminal_cut import path_between


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    certificates = []
    examples = {}
    whole_interior_obstructions = []
    for board in data["boards"]:
        original = labels(board["original"]["rows"])
        n = len(board["original"]["rows"])
        edges = [(y*n+x, yy*n+xx) for y in range(n) for x in range(n)
                 for xx, yy in [(x+1, y), (x, y+1)] if xx < n and yy < n]
        for terminal in board["terminals"]:
            v, w = terminal["v"], terminal["w"]
            protected = {v}
            for a, b in edges:
                if a == v:
                    protected.add(b)
                if b == v:
                    protected.add(a)
            cleared = original.copy()
            for y in range(1, n-1):
                for x in range(1, n-1):
                    u = y*n+x
                    if u not in protected:
                        cleared[u] = False
            remaining_path = path_between(cleared, edges, v, w)
            whole_interior_obstructions.append({"board": board["name"],
                "terminal": terminal, "fixed_closed_neighborhood": sorted(protected),
                "path_after_clearing_all_free_interior": remaining_path})
        for case in board["cases"]:
            region = case["region"]
            for t in case["terminals"]:
                if not t["clearing_separates"]:
                    continue
                v, w = t["terminal"]["v"], t["terminal"]["w"]
                path = path_between(original, edges, v, w)
                assert path is not None
                choices = []
                for a, b in zip(path, path[1:]):
                    endpoints = [u for u in (a, b) if original[u]]
                    if endpoints and all(u in region for u in endpoints):
                        choices.append(endpoints)
                assert choices
                deletion = min(choices, key=lambda x: (len(x), x))
                candidate = original.copy()
                for u in deletion:
                    candidate[u] = False
                roots, _, forest = components(candidate, edges)
                assert forest and roots[v] != roots[w]
                deficit = case["original_score"] - t["best_separated"]
                assert deficit <= len(deletion) <= 2
                certificates.append({"board": board["name"], "region": region,
                    "terminal": t["terminal"], "path": path,
                    "deletion_separator": deletion, "optimal_deficit": deficit})
                if str(deficit) not in examples:
                    baseline = original.copy()
                    for u in region:
                        baseline[u] = False
                    best = filled(baseline, region, t["best_mask"])
                    examples[str(deficit)] = {**certificates[-1],
                        "original_core_score": case["original_score"],
                        "optimal_separated_core_score": t["best_separated"],
                        "original_rows": board["original"]["rows"],
                        "best_rows": ["".join("." if f else "U" for f in best[y*n:(y+1)*n]) for y in range(n)]}
    output = {"input_sha256": hashlib.sha256(raw).hexdigest(),
              "scope": "constructive path deletion audit; optimum values independently exhaustively audited separately",
              "certificates": certificates, "examples_by_deficit": examples,
              "whole_interior_obstructions": whole_interior_obstructions}
    print("Path deletion certificates:", len(certificates))
    print("Whole-interior immutable-path obstructions:",
          sum(o["path_after_clearing_all_free_interior"] is not None for o in whole_interior_obstructions),
          "of", len(whole_interior_obstructions), "terminals")
    for deficit, example in examples.items():
        print("Deficit", deficit, "board", example["board"], "region", example["region"],
              "terminal", example["terminal"], "old/best", example["original_core_score"],
              example["optimal_separated_core_score"], "delete-only separator", example["deletion_separator"])
    with args.output.open("x") as out:
        json.dump(output, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
