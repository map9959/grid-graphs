"""Batch003 cycle3: exhaustive, core-compatible supersets of direct Q_2/Q_4.

Scheduled entry point (no work on import):
    python3 -B -m analysis.research_program.nested_renewal --output data/NEW.json

Only n=8 and n=14 are materialized. Every decision uses full primal graph
traversal, retaining ambient isolates; no solver or build is invoked. The 703
n8 pairs are checked independently of singleton filtering. A cyclic singleton
cannot occur in any feasible superset, since adding F only adds forced edges.
Thus exhausting every subset of the eligible pool proves the restricted
superset optimum. Pools above 20 receive an explicit inconclusive cutoff.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from .renewal_annulus import geometry as source_geometry


ROOT = Path(__file__).resolve().parents[2]
MAX_ELIGIBLE = 20
SOURCES = {
    8: "data/renewal_annulus_n8_batch002.json",
    14: "data/renewal_annulus_n14_gap1_batch002.json",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def size_k(n):
    require(type(n) is int and n in (8, 14), "only n=8 and n=14 are authorized")
    return (n-2)//3


def depth(n, v):
    r, c = divmod(v, n)
    return min(r, c, n-1-r, n-1-c)


def coordinates(n, centers):
    return [list(divmod(v, n)) for v in sorted(centers)]


def direct_q(n):
    """Q_k in old-board coordinates; never construct I_(k+2)."""
    k = size_k(n)
    points = {(r, 3*j+1) for j in range(k+1) for r in range(3*j+1)}
    points |= {(r, 3*j+3) for j in range(-1, k-1)
               for r in range(3*j+5, 3*k+2)}
    points |= {(3*j+2, 3*j+2) for j in range(k)}
    require(all(0 <= r < n and 0 <= c < n for r, c in points), "Q out of range")
    return {r*n+c for r, c in points}


def source_i(n):
    """The smaller source I_k, including its non-deep centers."""
    k = size_k(n)
    points = {(r, 3*i+1) for i in range(1, k) for r in range(2, 3*i+1)}
    points |= {(r, 3*i+3) for i in range(k-1) for r in range(3*i+5, 3*k)}
    points |= {(3*a+2, 3*a+2) for a in range(k)}
    return {r*n+c for r, c in points}


def traverse(adjacency, vertices):
    """Count components and detect cycles by undirected full graph traversal."""
    seen = set()
    components = 0
    cyclic = False
    for start in vertices:
        if start in seen:
            continue
        components += 1
        seen.add(start)
        stack = [(start, -1)]
        while stack:
            v, parent = stack.pop()
            for w in adjacency[v]:
                if w == parent:
                    continue
                if w in seen:
                    cyclic = True
                else:
                    seen.add(w)
                    stack.append((w, v))
    return components, not cyclic


def ledger(n, centers):
    """Independent forced-graph and FF-graph traversal, not a square-only test."""
    size_k(n)
    values = list(centers)
    require(all(type(v) is int and 0 <= v < n*n for v in values), "invalid center")
    chosen = set(values)
    require(len(chosen) == len(values), "duplicate centers")
    adjacency = [[] for _ in range(n*n)]
    ff_adjacency = [[] for _ in range(n*n)]
    ambient_degree = [0]*(n*n)
    edges = ff_edges = 0
    for r in range(n):
        for c in range(n):
            u = r*n+c
            for rr, cc in ((r+1, c), (r, c+1)):
                if rr >= n or cc >= n:
                    continue
                v = rr*n+cc
                ambient_degree[u] += 1
                ambient_degree[v] += 1
                if u in chosen or v in chosen:
                    adjacency[u].append(v)
                    adjacency[v].append(u)
                    edges += 1
                if u in chosen and v in chosen:
                    ff_adjacency[u].append(v)
                    ff_adjacency[v].append(u)
                    ff_edges += 1
    c, forest = traverse(adjacency, range(n*n))
    r, ff_forest = traverse(ff_adjacency, sorted(chosen))
    f = len(chosen)
    beta = edges-n*n+c
    ff_beta = ff_edges-f+r
    require(forest == (beta == 0) and ff_forest == (ff_beta == 0),
            "traversal/rank disagreement")
    b = sum(4-ambient_degree[v] for v in range(n*n) if v not in chosen)
    residual = 3*f+r+b+c-(n*n+4*n)
    if forest:
        require(residual == 0, "forest ledger disagreement")
    return {"f": f, "r": r, "b": b, "c": c,
            "z": sum(not neighbors for neighbors in adjacency),
            "edges": edges, "ff_edges": ff_edges, "cycle_rank": beta,
            "ff_cycle_rank": ff_beta, "forest": forest,
            "forest_ledger_residual": residual}


def board(n, centers):
    chosen = set(centers)
    return {"n": n, "center_ids": sorted(chosen), "centers": coordinates(n, chosen),
            "rows": ["".join("F" if r*n+c in chosen else "U" for c in range(n))
                     for r in range(n)], "ledger": ledger(n, chosen)}


def geometry_report(n):
    k = size_k(n)
    q = direct_q(n)
    deep = {v for v in range(n*n) if depth(n, v) >= 3}
    core = source_i(n) & deep
    source_core, source_free = source_geometry(n)
    band = set(range(n*n))-deep
    require(core == set(source_core) and band == set(source_free), "source mismatch")
    require(q & deep == core, "Q changes old deep labels")
    expected = {"q_f": 3*k*k+5*k+1, "deep_f": 3*k*k-7*k+3,
                "old_band_f": 12*k-2}
    observed = {"q_f": len(q), "deep_f": len(core), "old_band_f": len(q & band)}
    require(observed == expected, "symbolic count mismatch")
    require(ledger(n, q)["forest"], "Q is not a forest")
    holes = sorted(band-q)
    if n == 8:
        require(len(holes) == 38 and len(deep-q) == 3, "n8 hole partition mismatch")
    return {"n": n, "k": k, "q": board(n, q), "expected_counts": expected,
            "observed_counts": observed, "source_deep_labels_agree": True,
            "target": 3*k*k+7*k, "crop_deficit": 2*k-1,
            "immutable_deep_f_ids": sorted(core), "immutable_deep_u_ids": sorted(deep-q),
            "allowed_hole_ids": holes, "allowed_holes": coordinates(n, holes)}


def singleton_report(n, q, holes):
    trials = []
    eligible = []
    for v in holes:
        stats = ledger(n, q | {v})
        trials.append({"id": v, "coordinate": list(divmod(v, n)), "ledger": stats})
        if stats["forest"]:
            eligible.append(v)
    return {"tested": len(trials), "trials": trials, "eligible_ids": eligible,
            "eligible": coordinates(n, eligible),
            "ineligible_ids": sorted(set(holes)-set(eligible)),
            "monotonicity": "An ineligible singleton forces a cycle retained by every superset."}


def pair_report(q, holes):
    require(len(holes) == 38 and len(set(holes)) == 38, "expected 38 distinct n8 holes")
    require(set(holes) <= {v for v in range(64) if depth(8, v) <= 2}-q,
            "pair includes a deep label or existing center")
    feasible = []
    rejected = []
    tested = 0
    for pair in itertools.combinations(holes, 2):
        stats = ledger(8, q | set(pair))
        tested += 1
        entry = {"extra_ids": list(pair), "extras": coordinates(8, pair), "ledger": stats}
        (feasible if stats["forest"] else rejected).append(entry)
    require(tested == 703, "pair enumeration incomplete")
    return {"status": "exhaustive", "tested": tested, "feasible_count": len(feasible),
            "feasible_25_pairs": feasible, "rejected_pairs": rejected,
            "decision": "sat" if feasible else "none_exhaustive"}


def enumerate_supersets(n, q, eligible):
    """Mask bit i promotes eligible_ids[i]; include the empty mask explicitly."""
    eligible = sorted(eligible)
    total = 1 << len(eligible)
    result = {"eligible_ids": eligible, "mask_encoding": "bit i selects eligible_ids[i]",
              "pool_limit": MAX_ELIGIBLE, "total_supermasks": total,
              "tested_supermasks": 0, "feasible_supermask_count": 0,
              "feasible_masks": [], "maximum_f": None, "best_masks": [], "best_boards": []}
    if len(eligible) > MAX_ELIGIBLE:
        result.update(status="cutoff_inconclusive", exhaustive=False,
                      reason="eligible pool exceeds 20; no subset enumeration performed",
                      feasible_lower_bound_f=len(q)+1,
                      lower_bound_board=board(n, q | {eligible[0]}))
        return result
    best = -1
    for mask in range(total):
        centers = q | {v for i, v in enumerate(eligible) if mask & (1 << i)}
        stats = ledger(n, centers)
        result["tested_supermasks"] += 1
        if not stats["forest"]:
            continue
        result["feasible_masks"].append(mask)
        if len(centers) > best:
            best = len(centers)
            result["best_masks"] = []
        if len(centers) == best:
            result["best_masks"].append(mask)
    result.update(status="exact_core_compatible_superset_optimum", exhaustive=True,
                  maximum_f=best, feasible_supermask_count=len(result["feasible_masks"]))
    result["best_boards"] = [
        board(n, q | {v for i, v in enumerate(eligible) if mask & (1 << i)})
        for mask in result["best_masks"]]
    return result


def recorded_report(n):
    path = ROOT / SOURCES[n]
    raw = path.read_bytes()
    record = json.loads(raw)
    require(record["n"] == n and record["status"] == "sat_verified", "invalid recorded status")
    values = record["witness"]["center_ids"]
    stats = ledger(n, values)
    centers = set(values)
    require(stats["forest"] and stats["f"] == {8: 26, 14: 75}[n], "invalid recorded seed")
    require(stats == record["witness"]["ledger"], "recorded ledger mismatch")
    require(coordinates(n, centers) == record["witness"]["centers"], "recorded coordinates mismatch")
    require([row.replace("F", ".") for row in board(n, centers)["rows"]]
            == record["witness"]["rows"], "recorded rows mismatch")
    q = direct_q(n)
    deleted, added = centers-q, q-centers
    require(all(depth(n, v) <= 2 for v in deleted | added), "recorded seed changes deep core")
    k = size_k(n)
    gap = 3*k*k+7*k-len(centers)
    require(len(deleted)-len(added) == 2*k-1-gap, "rewrite count mismatch")
    return {"source": SOURCES[n], "source_sha256": hashlib.sha256(raw).hexdigest(),
            "board": board(n, centers), "C": gap, "delete_ids": sorted(deleted),
            "delete": coordinates(n, deleted), "add_ids": sorted(added),
            "add": coordinates(n, added), "delete_count": len(deleted),
            "add_count": len(added), "mandatory_flips": len(deleted)+len(added),
            "net_deleted": len(deleted)-len(added), "all_changes_in_old_band": True}


def compose(pair, final):
    q = direct_q(8)
    extras = set(pair)
    require(len(extras) == 2 and not extras & q
            and all(depth(8, v) <= 2 for v in extras), "invalid composition extras")
    current = q | extras
    stages = [{"operation": "seed", "board": board(8, current)}]
    for v in sorted(extras):
        current.remove(v)
        stages.append({"operation": "delete_old_extra", "id": v,
                       "coordinate": list(divmod(v, 8)), "board": board(8, current)})
    require(current == q, "deletion did not yield Q2")
    current = {(v//8+3)*14+v % 8+3 for v in current}
    crop = {v for v in final if depth(14, v) >= 3}
    require(current == crop, "embedded Q2 differs from recorded central crop")
    stages.append({"operation": "embed_plus_3_plus_3", "board": board(14, current)})
    outer = sorted(final-current)
    require(len(outer) == 52 and all(depth(14, v) <= 2 for v in outer), "invalid outer frame")
    for v in outer:
        current.add(v)
        stages.append({"operation": "add_recorded_outer_F", "id": v,
                       "coordinate": list(divmod(v, 14)), "board": board(14, current)})
    require(current == final, "composition differs from recorded witness")
    require(all(stage["board"]["ledger"]["forest"] for stage in stages), "cyclic composition stage")
    gain = len(current)-stages[0]["board"]["ledger"]["f"]
    require(gain == 50, "wrong composition gain")
    return {"extra_ids": sorted(extras), "extras": coordinates(8, extras),
            "central_crop_equals_embedded_q2": True, "deleted": 2, "added": len(outer),
            "net_gain": gain, "all_stages_forest": True, "stages": stages}


def diagnostic():
    records = {n: recorded_report(n) for n in (8, 14)}
    cases = []
    for n in (8, 14):
        case = geometry_report(n)
        q = set(case["q"]["center_ids"])
        holes = case["allowed_hole_ids"]
        singles = singleton_report(n, q, holes)
        case["single_promotions"] = singles
        if n == 8:
            case["pairs"] = pair_report(q, holes)
        case["supersets"] = enumerate_supersets(n, q, singles["eligible_ids"])
        case["recorded_seed_rewrite"] = records[n]
        cases.append(case)
    first = cases[0]
    if first["supersets"]["exhaustive"]:
        pool = first["supersets"]["eligible_ids"]
        mask_pairs = {tuple(v for i, v in enumerate(pool) if mask & (1 << i))
                      for mask in first["supersets"]["feasible_masks"] if mask.bit_count() == 2}
        require(mask_pairs == {tuple(p["extra_ids"]) for p in first["pairs"]["feasible_25_pairs"]},
                "independent pair/subset enumeration mismatch")
    final = set(records[14]["board"]["center_ids"])
    embedded_q = {(v//8+3)*14+v % 8+3 for v in direct_q(8)}
    require(embedded_q == {v for v in final if depth(14, v) >= 3}, "recorded crop mismatch")
    compositions = [compose(p["extra_ids"], final) for p in first["pairs"]["feasible_25_pairs"]]
    return {"schema": "nested_renewal_cycle3_v1", "status": "completed",
            "all_superset_optima_exact": all(c["supersets"]["exhaustive"] for c in cases),
            "scope": "Only forest supersets of Q2/Q4 preserving every old deep F/U label; not global optima.",
            "source_coordinate_scope": {
                "coordinates": "zero-based row,column; inclusive intervals; id=row*n+column; F=center",
                "source_geometry": "docs/PAPER_CONSTANT_GAP_LOWER.md:372-401; renewal_annulus.py:geometry",
                "source_results": "docs/PAPER_RENEWAL_ANNULUS_TEST.md; recorded solver UNSAT has no independent proof trace",
                "q_formula": "union_j=0..k [0,3j]x{3j+1}; union_j=-1..k-2 [3j+5,3k+1]x{3j+3}; {(3j+2,3j+2):j=0..k-1}",
                "materialized_sizes": [8, 14], "larger_board_materialized": False,
                "old_immutable": "depth>=3 (both F and U); maps to new depth>=6",
                "old_rewrite_band": "depth<=2; maps to new depth 3..5",
                "new_free_frame": "new depth<=2",
                "symbolic_counts": {"Q": "3k^2+5k+1", "deep": "3k^2-7k+3",
                                    "old_band_F": "12k-2", "crop_deficit": "2k-1",
                                    "net_deletions_from_T_minus_C": "2k-1-C"}},
            "cases": cases, "recorded_central_crop_equals_embedded_q2": True,
            "composition_status": "verified" if compositions else "not_applicable_no_feasible_25_pair",
            "compositions": compositions}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    require(output.is_relative_to(ROOT), "output must be inside the repository")
    require(output.parent.is_dir(), "output parent must already exist")
    # Reserve exclusively before computation; an exception leaves an incomplete
    # artifact, never a completed/exact result and never overwrites prior evidence.
    with output.open("x") as handle:
        result = diagnostic()
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps({"output": str(output), "status": result["status"],
                      "all_superset_optima_exact": result["all_superset_optima_exact"],
                      "composition_status": result["composition_status"]}))


if __name__ == "__main__":
    main()
