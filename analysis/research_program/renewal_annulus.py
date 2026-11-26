"""Batch002: exact threshold SAT in the three-layer moving-phase annulus.

Coordinates are zero-based (row, column), flattened as row*n+column.
Only n=8,14 are executable instances. No solver runs on import.

Uniform observation: guarded pendant surgery removes one leaf edge and
then attaches three isolated vertices, per level. Thus Delta E=2, Delta c=-2,
and Delta beta=0, even on a cyclic graph IF its full-graph pendant/isolate
hypotheses are independently checked. Resource conversion is not rank repair.
Moving leaf terminals need not retain their old component identities.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time


PROVENANCE = {
    "source": "docs/PAPER_CONSTANT_GAP_LOWER.md:372-401",
    "core_rule": "(union A_i, B_i, x_a) intersect depth>=3",
    "A_i": "[2,3i] x {3i+1}, 1<=i<=k-1",
    "B_i": "[3i+5,3k-1] x {3i+3}, 0<=i<=k-2",
    "x_a": "(3a+2,3a+2), 0<=a<=k-1",
    "scope": "all depth<=2 labels free; every other noncore label fixed U",
    "n8_note": "k=2 diagnostic extension; source uniform statement uses k>=3",
    "coordinates": "zero-based row,column; inclusive intervals; id=row*n+column",
}


def geometry(n):
    if n not in (8, 14):
        raise ValueError("only n=8 and n=14 are authorized")
    k = (n-2)//3
    moving = {(r, 3*i+1) for i in range(1, k) for r in range(2, 3*i+1)}
    moving |= {(r, 3*i+3) for i in range(k-1) for r in range(3*i+5, 3*k)}
    moving |= {(3*a+2, 3*a+2) for a in range(k)}
    depth = lambda r, c: min(r, c, n-1-r, n-1-c)
    core = sorted(r*n+c for r, c in moving if depth(r, c) >= 3)
    free = [r*n+c for r in range(n) for c in range(n) if depth(r, c) <= 2]
    return core, free


def grid_edges(n):
    return [(r*n+c, rr*n+cc) for r in range(n) for c in range(n)
            for rr, cc in ((r+1, c), (r, c+1)) if rr < n and cc < n]


class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def new(self):
        self.variables += 1
        return self.variables

    def add(self, *clause):
        self.clauses.append(list(clause))

    def at_least(self, literals, target):
        """Exact unary threshold recurrence, no one-sided auxiliary shortcut.

        s[i,j] <=> s[i-1,j] OR (x_i AND s[i-1,j-1]).
        Only columns through target are needed. Four clauses encode each cell.
        """
        if target <= 0:
            return
        if target > len(literals):
            self.add()
            return
        truth = self.new()
        self.add(truth)
        prev = [truth] + [-truth]*target
        for i, x in enumerate(literals, 1):
            row = [truth]
            for j in range(1, target+1):
                if j > i:
                    row.append(-truth)
                    continue
                a, b, z = prev[j], prev[j-1], self.new()
                self.add(-a, z)
                self.add(-x, -b, z)
                self.add(-z, a, x)
                self.add(-z, a, b)
                row.append(z)
            prev = row
        self.add(prev[target])


def build_model(n, max_rounds=10000, gap=0):
    if not 1 <= max_rounds <= 10000:
        raise ValueError("max_rounds must be in 1..10000")
    if type(gap) is not int or not 0 <= gap <= 3:
        raise ValueError("gap must be in 0..3")
    core, free = geometry(n)
    k = (n-2)//3
    threshold = 3*k*k+7*k-gap
    formula = CNF()
    centers = [formula.new() for _ in range(n*n)]
    core_set, free_set = set(core), set(free)
    for v, x in enumerate(centers):
        if v not in free_set:
            formula.add(x if v in core_set else -x)
    edges = grid_edges(n)
    edge_vars = []
    for u, v in edges:
        e, x, y = formula.new(), centers[u], centers[v]
        edge_vars.append(e)
        # e <=> F[u] OR F[v]. Both directions are essential for cycle cuts.
        formula.add(-x, e)
        formula.add(-y, e)
        formula.add(-e, x, y)
    formula.at_least([centers[v] for v in free], threshold-len(core))
    lookup = {tuple(sorted(edge)): e for edge, e in zip(edges, edge_vars)}
    # Sound static cuts only: every unit square must have an unforced edge.
    for r in range(n-1):
        for c in range(n-1):
            a = r*n+c
            square = [a, a+1, a+n+1, a+n, a]
            formula.add(*[-lookup[tuple(sorted((u, v)))]
                          for u, v in zip(square, square[1:])])
    return {"n": n, "variables": formula.variables, "clauses": formula.clauses,
            "center_vars": centers, "edges": edges, "edge_vars": edge_vars,
            "max_rounds": max_rounds, "threshold": threshold}


def audit(n, centers):
    """Independent full primal reconstruction, including every ambient isolate."""
    geometry(n)  # Enforce the size guard even for direct API calls.
    if len(set(centers)) != len(centers) or any(type(v) is not int or not 0 <= v < n*n
                                             for v in centers):
        raise ValueError("invalid center list")
    chosen = set(centers)
    parent = list(range(n*n))
    ff_parent = list(range(n*n))

    def root(p, x):
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    degree, forced_degree = [0]*(n*n), [0]*(n*n)
    e = ff = 0
    for u, v in grid_edges(n):
        degree[u] += 1
        degree[v] += 1
        if u in chosen or v in chosen:
            e += 1
            forced_degree[u] += 1
            forced_degree[v] += 1
            parent[root(parent, u)] = root(parent, v)
        if u in chosen and v in chosen:
            ff += 1
            ff_parent[root(ff_parent, u)] = root(ff_parent, v)
    c = len({root(parent, v) for v in range(n*n)})
    r = len({root(ff_parent, v) for v in chosen})
    f = len(chosen)
    b = sum(4-degree[v] for v in range(n*n) if v not in chosen)
    beta = e-n*n+c
    result = {"f": f, "r": r, "b": b, "c": c, "z": forced_degree.count(0),
              "edges": e, "ff_edges": ff, "cycle_rank": beta,
              "ff_cycle_rank": ff-f+r, "forest": beta == 0,
              "forest_ledger_residual": 3*f+r+b+c-(n*n+4*n)}
    if beta == 0 and result["forest_ledger_residual"] != 0:
        raise ValueError("forest ledger inconsistency")
    return result


def verify_witness(n, centers, threshold):
    core, free = geometry(n)
    chosen = set(centers)
    if not set(core) <= chosen or not chosen <= set(core+free):
        raise ValueError("witness violates frozen geometry")
    ledger = audit(n, centers)
    if not ledger["forest"] or ledger["f"] < threshold:
        raise ValueError("witness fails forest/threshold check")
    return ledger


def run(n, binary, output, seconds=60.0, max_rounds=10000, gap=0):
    """One single-threaded child, killed externally even while SAT is solving.

    Flush a JSONL journal throughout. A timeout never means UNSAT. A complete
    witness event remains verifiable if the process is killed before exiting.
    The journal is evidence/progress preservation, not a resumable SAT state.
    """
    if not math.isfinite(seconds) or not 0 < seconds <= 60:
        raise ValueError("external cap must be in (0,60] seconds")
    model = build_model(n, max_rounds, gap)
    encoded_model = json.dumps(model, sort_keys=True)
    core, free = geometry(n)
    output = Path(output)
    journal = output.with_suffix(output.suffix + ".progress.jsonl")
    if not output.parent.is_dir():
        raise ValueError("output parent directory must already exist")
    # Exclusive creation protects prior evidence, including an interrupted run.
    metadata = {"event": "metadata", "schema": "renewal_annulus_v1", "n": n,
                "provenance": PROVENANCE, "core": [divmod(v, n) for v in core],
                "core_ids": core, "free_ids": free,
                "fixed_u_ids": sorted(set(range(n*n))-set(core)-set(free)),
                "core_ledger": audit(n, core),
                "threshold": model["threshold"], "C": gap,
                "required_annulus_centers": model["threshold"]-len(core),
                "model_sha256": hashlib.sha256(encoded_model.encode()).hexdigest(),
                "external_seconds": seconds, "max_rounds": max_rounds,
                "workers": 1, "variables": model["variables"],
                "initial_clauses": len(model["clauses"])}
    with output.open("x") as final, journal.open("x") as progress:
        progress.write(json.dumps(metadata) + "\n")
        progress.flush()
        with tempfile.TemporaryFile(mode="w+", dir=output.parent) as request, \
                tempfile.TemporaryFile(mode="w+", dir=output.parent) as errors:
            request.write(encoded_model)
            request.seek(0)
            start = time.monotonic()
            timed_out = False
            try:
                child = subprocess.Popen([str(Path(binary).resolve())], stdin=request,
                                         stdout=progress, stderr=errors, start_new_session=True)
                try:
                    child.wait(timeout=seconds)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
                returncode = child.returncode
            except OSError as exc:
                returncode = None
                errors.write(str(exc))
            elapsed = time.monotonic()-start
            errors.seek(0)
            stderr = errors.read()
        progress.flush()
        result = dict(metadata, status="cutoff" if timed_out else "engine_error",
                      timed_out=timed_out, returncode=returncode, elapsed_seconds=elapsed,
                      stderr=stderr, journal=str(journal), exhaustive=False,
                      witness=None, last_candidate=None, completed_cuts=0,
                      scope="this n, this frozen core, this threshold only; no global claim")
        terminal = None
        with journal.open() as saved:
            for line in saved:
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    # A SIGKILL may leave the final line incomplete.
                    result["incomplete_journal_line"] = True
                    continue
                if event.get("event") == "cut":
                    result["completed_cuts"] += 1
                    result["last_candidate"] = event
                if event.get("event") in ("sat", "unsat", "round_limit"):
                    terminal = event
        if result["last_candidate"]:
            candidate = result["last_candidate"]
            candidate["ledger"] = audit(n, candidate["centers"])
        if terminal and terminal["event"] == "sat":
            try:
                ledger = verify_witness(n, terminal["centers"], model["threshold"])
                result.update(status="sat_verified", witness={
                    "centers": [divmod(v, n) for v in terminal["centers"]],
                    "center_ids": terminal["centers"], "ledger": ledger,
                    "rows": ["".join("." if r*n+c in set(terminal["centers"]) else "U"
                                     for c in range(n)) for r in range(n)]})
            except ValueError as exc:
                result.update(status="verification_error", verification_error=str(exc))
        elif terminal and terminal["event"] == "unsat" and returncode == 0:
            result.update(status="unsat_restricted", exhaustive=True,
                          proof_scope="exact SAT decision with sound cycle cuts; no proof trace emitted")
        elif terminal and terminal["event"] == "round_limit" and returncode == 0:
            result["status"] = "round_limit"
        json.dump(result, final, indent=2)
        final.write("\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, choices=(8, 14), required=True)
    parser.add_argument("--binary", default="target/release/renewal_annulus")
    parser.add_argument("--output", required=True)
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--max-rounds", type=int, default=10000)
    parser.add_argument("--gap", type=int, choices=range(4), default=0)
    args = parser.parse_args()
    result = run(args.n, args.binary, args.output, args.seconds, args.max_rounds, args.gap)
    print(json.dumps({k: result[k] for k in ("n", "status", "exhaustive", "elapsed_seconds",
                                            "completed_cuts", "witness")}))


if __name__ == "__main__":
    main()
