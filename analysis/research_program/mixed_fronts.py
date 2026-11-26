"""Complete rooted three-column frontier graph and integer potential search.

python3 -m analysis.research_program.mixed_fronts OUTPUT.json
"""

import argparse
import json
from collections import deque
from pathlib import Path


class DSU:
    def __init__(self, n):
        self.parent = list(range(n))

    def root(self, v):
        while self.parent[v] != v:
            v = self.parent[v]
        return v

    def join(self, v, w):
        v, w = self.root(v), self.root(w)
        if v == w:
            return False
        self.parent[w] = v
        return True


def bit(mask, i):
    return (mask >> i) & 1


def canonical(dsu, vertices):
    names = {}
    return tuple(names.setdefault(dsu.root(v), len(names)) for v in vertices)


def initial(mask, suppliers=False):
    dsu = DSU(4)
    for i in (0, 1):
        if bit(mask, i) or bit(mask, i+1):
            assert dsu.join(i, i+1)
    assert dsu.join(0, 3)  # Actual back-q root to marked p, even if p is U.
    # Virtual preceding S=F suppresses an unsupported first-row singleton.
    state = (0, 2 if suppliers else 0, mask, *canonical(dsu, range(4)))
    return (*state, 0) if suppliers else state


def transition(state, next_mask, suppliers=False):
    phase, previous, current = state[:3]
    partition = state[3:7]
    flags = state[7] if suppliers else 0
    next_phase = (phase+1) % 3
    if next_phase and bit(next_mask, 0):
        return None  # Off-level depth-two vertex is forced U by back FF.
    dsu = DSU(7)
    for i in range(4):
        for j in range(i):
            if partition[i] == partition[j]:
                dsu.join(i, j)
    for i in range(3):
        if bit(current, i) or bit(next_mask, i):
            if not dsu.join(i, i+4):
                return None
    for i in (0, 1):
        if bit(next_mask, i) or bit(next_mask, i+1):
            if not dsu.join(i+4, i+5):
                return None
    if next_phase == 0 and not dsu.join(4, 3):
        return None
    # Finalize the current row using its actual two neighbouring row masks.
    hole = 1-bit(current, 2)
    pure_start = int(bit(current, 2) and not bit(previous, 2) and not bit(current, 1))
    deep = near = demand = 0
    if phase:
        demand = 1
        deep = int(not bit(previous, 0) and not bit(next_mask, 0) and not bit(current, 1))
        near = int(not bit(current, 1) and not bit(current, 2)
                   and not bit(previous, 1) and not bit(next_mask, 1))
    cost = hole+pure_start+deep+near-demand
    target = (next_phase, current, next_mask, *canonical(dsu, [4,5,6,3]))
    terms = [hole,pure_start,deep,near,demand]
    if suppliers:
        singleton = int(bit(current,1) and not bit(current,0) and not bit(current,2)
                        and not bit(previous,1) and not bit(next_mask,1))
        dimer_start = 0
        if phase:
            dimer = int(bit(current,1) and bit(current,2))
            position = 1 << (phase-1)
            dimer_start = int(dimer and not (flags & position))
            flags = (flags | position) if dimer else (flags & ~position)
        cost += singleton+dimer_start
        terms.extend([singleton,dimer_start])
        target = (*target, flags)
    return target, cost, terms


def graph(suppliers=False):
    states = []
    index = {}
    queue = deque()
    def add(state):
        if state not in index:
            index[state] = len(states)
            states.append(state)
            queue.append(index[state])
        return index[state]
    initials = [add(initial(mask, suppliers)) for mask in range(8)]
    edges = []
    while queue:
        u = queue.popleft()
        for mask in range(8):
            step = transition(states[u], mask, suppliers)
            if step is not None:
                target, cost, terms = step
                edges.append([u,add(target),cost,mask,terms])
    return states, initials, edges


def potential(states, edges):
    distance = [0] * len(states)
    parent = [None] * len(states)
    for _ in range(len(states)):
        changed = None
        for i, (u,v,cost,_,_) in enumerate(edges):
            if distance[v] > distance[u]+cost:
                distance[v] = distance[u]+cost
                parent[v] = i
                changed = v
        if changed is None:
            return distance, None
    v = changed
    for _ in states:
        v = edges[parent[v]][0]
    start = v
    cycle = []
    while True:
        i = parent[v]
        cycle.append(i)
        v = edges[i][0]
        if v == start:
            break
    cycle.reverse()
    assert sum(edges[i][2] for i in cycle) < 0
    return None, cycle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--suppliers", action="store_true")
    args = parser.parse_args()
    with args.output.open("x") as output:
        states, initials, edges = graph(args.suppliers)
        phi, cycle = potential(states, edges)
        result = {"schema": 1, "scope": "complete reachable three-column single-root relaxation; requires geometric soundness and nonreuse proof",
                  "state_fields": ["phase","previous_mask","current_mask","p_component","s_component","boundary_component","root_component"],
                  "edge_fields": ["source","target","weight","next_mask","hole_pure_deep_near_demand"],
                  "suppliers": args.suppliers,
                  "states": states, "initials": initials, "edges": edges,
                  "potential": phi, "negative_cycle_edges": cycle}
        if args.suppliers:
            result["state_fields"].append("last_dimer_bits_by_offphase")
            result["edge_fields"][-1] = "hole_pure_deep_near_demand_singleton_dimerbankstart"
        if phi is not None:
            assert all(cost >= phi[v]-phi[u] for u,v,cost,_,_ in edges)
            def final_cost(state):
                _, prev, cur, *_ = state
                return 1-bit(cur,2)+int(bit(cur,2) and not bit(prev,2) and not bit(cur,1))
            initial_max = max(phi[i] for i in initials)
            terminal_min = min(phi[i]+final_cost(s) for i,s in enumerate(states) if s[0] == 0)
            result["endpoint_error"] = max(0, initial_max-terminal_min)
            print("states",len(states),"edges",len(edges),"potential range",min(phi),max(phi),
                  "endpoint error",result["endpoint_error"])
        else:
            print("states",len(states),"edges",len(edges),"negative cycle weight",sum(edges[i][2] for i in cycle))
        json.dump(result, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
