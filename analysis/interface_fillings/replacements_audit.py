"""Audit every saved rank-profile witness and summarize replacement experiments.

This checks witnesses, not exhaustiveness of the Rust enumerations.
Run as python3 -m analysis.interface_fillings.replacements_audit INPUT OUTPUT.
"""

import argparse
import hashlib
import json
from pathlib import Path

from .audit import audit_case, rank


def labels(rows):
    return [ch == "." for row in rows for ch in row]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--exhaustive", action="store_true",
                        help="also independently enumerate every filling in every saved case")
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    summary = {"input_sha256": hashlib.sha256(raw).hexdigest(),
               "scope": ("independent exhaustive enumeration plus all saved frontier witnesses" if args.exhaustive
                         else "independent traversal of all saved frontier witnesses, not independent exhaustive search"),
               "boards": []}
    for board in data["boards"]:
        original = labels(board["original"]["rows"])
        n = len(board["original"]["rows"])
        edges = [(y * n + x, yy * n + xx)
                 for y in range(n) for x in range(n)
                 for xx, yy in [(x + 1, y), (x, y + 1)] if xx < n and yy < n]
        assert rank(original, edges) == 0
        families = {}
        controls = []
        improvements = []
        audited = 0
        for case in board["cases"]:
            if args.exhaustive:
                audit_case(case)
            family = case["name"].split("_")[0]
            stats = families.setdefault(family, {"regions": 0, "fillings": 0,
                "actual_improvements": 0, "relaxed_improvements": 0,
                "max_relaxed_gain": 0, "best_positive_rank_margin": -999})
            baseline = labels(case["baseline"])
            region = set(case["region"])
            optional = [v for v in case["region"] if not baseline[v]]
            old = case["original_optional"]
            assert old == sum(original[v] for v in region)
            assert all(baseline[v] == (original[v] and v not in region) for v in range(n*n))
            local = [(v, w) for v, w in edges if v in region or w in region]
            result = case["result"]
            assert result["tested"] == 1 << len(optional)
            assert sum(p["count"] for p in case["rank_profile"]) == result["relaxed_feasible"]
            for point in case["rank_profile"]:
                candidate = baseline.copy()
                for i, v in enumerate(optional):
                    candidate[v] = bool(point["mask"] & (1 << i))
                assert rank(candidate, edges) == point["rank"]
                assert rank(candidate, local) == 0
                assert sum(candidate[v] for v in optional) == point["best_optional"]
                assert point["best_optional"] - 2*point["rank"] <= result["optimum"]
                if point["rank"] > 0:
                    stats["best_positive_rank_margin"] = max(stats["best_positive_rank_margin"],
                        point["best_optional"] - old - 2*point["rank"])
                audited += 1
            best = labels(result["best_rows"])
            assert rank(best, edges) == 0
            assert all(best[v] == original[v] for v in range(n*n) if v not in region)
            assert sum(best[v] for v in region) == result["optimum"]
            stats["regions"] += 1
            stats["fillings"] += result["tested"]
            stats["actual_improvements"] += result["optimum"] > old
            stats["relaxed_improvements"] += result["relaxed_optimum"] > old
            stats["max_relaxed_gain"] = max(stats["max_relaxed_gain"], result["relaxed_optimum"] - old)
            if result["optimum"] > old:
                improvements.append({"region": case["name"],
                    "deleted": [v for v in range(n*n) if original[v] and not best[v]],
                    "added": [v for v in range(n*n) if best[v] and not original[v]],
                    "rows": result["best_rows"]})
            if family == "control":
                controls.append({"region": case["name"], "old": old,
                                 "actual": result["optimum"], "relaxed": result["relaxed_optimum"],
                                 "rank_profile": case["rank_profile"]})
        record = {"name": board["name"], "families": families, "controls": controls,
                  "audited_rank_witnesses": audited, "improvements": improvements}
        summary["boards"].append(record)
        print(board["name"], json.dumps(families))
        for improvement in improvements:
            print("Gain witness:", improvement["region"], "delete", improvement["deleted"], "add", improvement["added"])
        for control in controls:
            print("Control:", control["region"], "old/actual/relaxed", control["old"], control["actual"], control["relaxed"])
    with args.output.open("x") as out:
        json.dump(summary, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
