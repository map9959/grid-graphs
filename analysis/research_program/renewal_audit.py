"""Repository-only replay of annulus SAT journals and rank-changing edits.

This validates models/cuts/witnesses, NOT the solver's internal UNSAT proof.
python3 -m analysis.research_program.renewal_audit OUTPUT.json
"""

import argparse
import hashlib
import json
from pathlib import Path

from analysis.interface_fillings.separation_audit import components
from .guarded_fronts import exchange, rooted14, rows
from .renewal_annulus import build_model, geometry, grid_edges


def graph_stats(n, state):
    edges = grid_edges(n)
    _, c, forest = components(state, edges)
    forced = {(u,v) for u,v in edges if state[u] or state[v]}
    return {"f":sum(state), "c":c, "edges":len(forced),
            "beta":len(forced)-n*n+c, "forest":forest}


def check_cycle(n, centers, indices):
    edges = grid_edges(n)
    assert len(indices) == len(set(indices)) >= 4
    adjacency = {}
    for i in indices:
        assert 0 <= i < len(edges)
        u,v = edges[i]
        assert u in centers or v in centers
        adjacency.setdefault(u,[]).append(v)
        adjacency.setdefault(v,[]).append(u)
    assert all(len(v)==2 for v in adjacency.values())
    seen = {next(iter(adjacency))}
    stack = list(seen)
    while stack:
        for w in adjacency[stack.pop()]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    assert len(seen) == len(adjacency)


def audit_file(path):
    result = json.loads(path.read_text())
    n = result["n"]
    core, free = geometry(n)
    assert core == result["core_ids"] and free == result["free_ids"]
    model = build_model(n, result["max_rounds"], result["C"])
    digest = hashlib.sha256(json.dumps(model,sort_keys=True).encode()).hexdigest()
    assert digest == result["model_sha256"]
    assert model["threshold"] == result["threshold"]
    cuts = 0
    cycle_lengths = {}
    terminal = None
    for line in Path(result["journal"]).read_text().splitlines():
        event = json.loads(line)
        if event.get("event") not in ("cut","sat","unsat","round_limit"):
            continue
        if "centers" in event:
            centers = set(event["centers"])
            assert len(centers)==len(event["centers"])
            assert set(core)<=centers<=set(core+free)
            assert len(centers)>=model["threshold"]
        if event["event"] == "cut":
            assert event["round"] == cuts
            check_cycle(n,centers,event["cycle_edge_indices"])
            length = len(event["cycle_edge_indices"])
            cycle_lengths[length] = cycle_lengths.get(length,0)+1
            cuts += 1
        else:
            terminal = event
    assert cuts == result["completed_cuts"]
    assert terminal is not None and terminal["round"] == cuts
    if terminal["event"] == "sat":
        state = [v in set(terminal["centers"]) for v in range(n*n)]
        stats = graph_stats(n,state)
        assert stats["forest"] and stats["beta"]==0
        assert rows(state,n)==result["witness"]["rows"]
        assert stats["f"]==result["witness"]["ledger"]["f"]
    else:
        assert terminal["event"] == "unsat" and result["status"] == "unsat_restricted"
        assert result["returncode"]==0 and not result["timed_out"]
        stats = None
    return {"input":str(path), "input_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "n":n,"threshold":model["threshold"],"status":result["status"],
            "cuts_checked":cuts,"cycle_length_histogram":cycle_lengths,
            "witness_stats":stats,"unsat_proof_independently_certified":False}


def original_candidate(n):
    k = (n-2)//3
    f = {(r,3*i+1) for i in range(1,k) for r in range(2,3*i+1)}
    f |= {(r,3*i+3) for i in range(k-1) for r in range(3*i+5,3*k)}
    f |= {(3*a+2,3*a+2) for a in range(k)}
    boundary_holes = {(0,1),(0,2),(1,3*k+1),(3*k+1,1),(3*k+1,3*k)}
    f |= {(r,c) for r in range(n) for c in range(n)
          if min(r,c,n-1-r,n-1-c)==0 and (r,c) not in boundary_holes}
    return [(r,c) in f for r in range(n) for c in range(n)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output",type=Path)
    args = parser.parse_args()
    files = [Path("data/renewal_annulus_n8_batch002.json"),
             Path("data/renewal_annulus_n14_batch002.json"),
             Path("data/renewal_annulus_n14_gap1_batch002.json")]
    audits = [audit_file(path) for path in files]
    final_data = json.loads(files[-1].read_text())
    final = [v in set(final_data["witness"]["center_ids"]) for v in range(196)]
    original = original_candidate(14)
    assert graph_stats(14,original)["f"]==78 and graph_stats(14,original)["beta"]==5
    deleted = [v for v in range(196) if original[v] and not final[v]]
    added = [v for v in range(196) if final[v] and not original[v]]
    current = original.copy()
    deletion_trace = []
    for v in deleted:
        before = graph_stats(14,current)
        current[v] = False
        after = graph_stats(14,current)
        assert after["beta"] <= before["beta"]
        deletion_trace.append({"vertex":v,"before_beta":before["beta"],"after_beta":after["beta"]})
    assert graph_stats(14,current)["beta"]==0
    for v in added:
        current[v] = True
        assert graph_stats(14,current)["beta"]==0
    assert current==final
    # Deliberately cyclic full-grid input with a remote, still-valid guarded move.
    cyclic = rooted14()
    cyclic[1*14+5] = True
    changed = exchange(cyclic,14,[7])
    before, after = graph_stats(14,cyclic), graph_stats(14,changed)
    assert before["beta"]>0 and before["beta"]==after["beta"]
    assert after["edges"]-before["edges"]==2 and after["c"]-before["c"]==-2
    old_edges = {(u,v) for u,v in grid_edges(14) if cyclic[u] or cyclic[v]}
    new_edges = {(u,v) for u,v in grid_edges(14) if changed[u] or changed[v]}
    assert old_edges-new_edges == {(110,111)}
    assert new_edges-old_edges == {(95,109),(109,110),(109,123)}
    output = {"scope":"independent adjacency replay of all cuts/witnesses; no internal UNSAT proof certification",
              "runs":audits,"cap_repair":{"original":graph_stats(14,original),"final":graph_stats(14,final),
                    "deleted":deleted,"added":added,"deletion_rank_trace":deletion_trace},
              "cyclic_guarded_control":{"before":before,"after":after,
                    "before_rows":rows(cyclic,14),"after_rows":rows(changed,14)}}
    with args.output.open("x") as out:
        json.dump(output,out,indent=2)
        out.write("\n")
    print("Annulus journals audited:", [(r["n"],r["threshold"],r["status"],r["cuts_checked"]) for r in audits])
    print("Cap repair delete/add:",len(deleted),len(added),"rank-changing deletions:",
          [t for t in deletion_trace if t["before_beta"]!=t["after_beta"]])
    print("Cyclic guarded control:",before,"->",after)


if __name__ == "__main__":
    main()
