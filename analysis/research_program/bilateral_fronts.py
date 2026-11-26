"""Complete six-column bilateral frontier, with no fictitious common root.

python3 -m analysis.research_program.bilateral_fronts OUTPUT.json
"""

import argparse
import json
import time
from collections import deque
from pathlib import Path

from .mixed_fronts import DSU, bit, canonical


def initial(mask):
    dsu = DSU(6)
    for base in (0,3):
        for i in (base,base+1):
            if bit(mask,i) or bit(mask,i+1):
                assert dsu.join(i,i+1)
    assert dsu.join(0,3)  # Suppressed actual central rail path.
    return (0,18,mask,*canonical(dsu,range(6)),0)


def transition(state, next_mask):
    phase, previous, current = state[:3]
    partition, flags = state[3:9], state[9]
    next_phase = (phase+1)%3
    if next_phase and next_mask & 9:
        return None
    dsu = DSU(12)
    for i in range(6):
        for j in range(i):
            if partition[i] == partition[j]:
                dsu.join(i,j)
    for i in range(6):
        if bit(current,i) or bit(next_mask,i):
            if not dsu.join(i,i+6):
                return None
    for base in (6,9):
        for i in (base,base+1):
            if bit(next_mask,i-6) or bit(next_mask,i-5):
                if not dsu.join(i,i+1):
                    return None
    if next_phase == 0 and not dsu.join(6,9):
        return None
    terms = []
    for side, base in enumerate((0,3)):
        p,s,b = base,base+1,base+2
        hole = 1-bit(current,b)
        pure = int(bit(current,b) and not bit(previous,b) and not bit(current,s))
        deep = near = start = 0
        if phase:
            deep = int(not bit(previous,p) and not bit(next_mask,p) and not bit(current,s))
            near = int(not bit(current,s) and not bit(current,b)
                       and not bit(previous,s) and not bit(next_mask,s))
            dimer = int(bit(current,s) and bit(current,b))
            position = 1 << (2*side+phase-1)
            start = int(dimer and not(flags & position))
            flags = (flags | position) if dimer else (flags & ~position)
        singleton = int(bit(current,s) and not bit(current,p) and not bit(current,b)
                        and not bit(previous,s) and not bit(next_mask,s))
        terms.extend([hole,pure,deep,near,singleton,start])
    demand = int(phase != 0)
    weight = sum(terms)-demand
    terms.append(demand)
    target = (next_phase,current,next_mask,*canonical(dsu,range(6,12)),flags)
    return target,weight,terms


def graph():
    states, index, edges = [], {}, []
    queue = deque()
    def add(state):
        if state not in index:
            if len(states) >= 20000:
                raise OverflowError("state_limit_20000")
            index[state] = len(states)
            states.append(state)
            queue.append(index[state])
        return index[state]
    initials = [add(initial(mask)) for mask in range(64)]
    while queue:
        u = queue.popleft()
        for mask in range(64):
            step = transition(states[u],mask)
            if step is None:
                continue
            target,cost,terms = step
            edges.append([u,add(target),cost,mask,terms])
            if len(edges)>1000000:
                raise OverflowError("edge_limit_1000000")
    return states,initials,edges


def negative_parent_cycle(parent,edges,last):
    positions, backward = {}, []
    v = last
    while v not in positions:
        positions[v] = len(backward)
        i = parent[v]
        if i is None:
            return None
        backward.append(i)
        v = edges[i][0]
    cycle = backward[positions[v]:][::-1]
    if sum(edges[i][2] for i in cycle)<0:
        assert all(edges[cycle[i]][1]==edges[cycle[(i+1)%len(cycle)]][0] for i in range(len(cycle)))
        return cycle
    return None


def potential(states,edges):
    start = time.monotonic()
    distance, parent = [0]*len(states), [None]*len(states)
    for _ in states:
        changed = None
        for i,(u,v,cost,_,_) in enumerate(edges):
            if distance[v]>distance[u]+cost:
                distance[v]=distance[u]+cost
                parent[v]=i
                changed=v
        if changed is None:
            return distance,None,"potential"
        cycle = negative_parent_cycle(parent,edges,changed)
        if cycle is not None:
            return None,cycle,"negative_cycle"
        if time.monotonic()-start>180:
            return None,None,"potential_time_limit"
    raise AssertionError("Bellman-Ford exhausted without extracting its negative cycle")


def final_cost(state):
    _,previous,current,*_ = state
    return sum(1-bit(current,b)+int(bit(current,b) and not bit(previous,b) and not bit(current,s))
               for s,b in ((1,2),(4,5)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output",type=Path)
    args = parser.parse_args()
    with args.output.open("x") as output:
        try:
            states,initials,edges = graph()
        except OverflowError as error:
            json.dump({"schema":1,"status":str(error),"exhaustive":False},output,indent=2)
            print(error)
            return
        print("complete graph:",len(states),"states",len(edges),"edges",flush=True)
        phi,cycle,status = potential(states,edges)
        result = {"schema":1,"status":status,"exhaustive_graph":True,
            "scope":"complete bilateral six-column necessary-condition graph; no persistent common root; requires geometric ownership proof",
            "state_fields":["phase","previous_mask","current_mask","PL","SL","BL","PR","SR","BR","dimer_history"],
            "row_bit_order":["PL","SL","BL","PR","SR","BR"],
            "charge_order":["hL","pureL","deepL","nearL","singletonL","dimer_startL",
                            "hR","pureR","deepR","nearR","singletonR","dimer_startR","demand"],
            "states":states,"initials":initials,"edges":edges,"potential":phi,"negative_cycle_edges":cycle}
        if phi is not None:
            assert all(cost>=phi[v]-phi[u] for u,v,cost,_,_ in edges)
            initial_max = max(phi[i] for i in initials)
            terminal_min = min(phi[i]+final_cost(state) for i,state in enumerate(states) if state[0]==0)
            result["endpoint_error"]=max(0,initial_max-terminal_min)
            print("potential range",min(phi),max(phi),"endpoint error",result["endpoint_error"])
        elif cycle is not None:
            print("negative cycle length",len(cycle),"weight",sum(edges[i][2] for i in cycle))
        else:
            print(status)
        json.dump(result,output,indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
