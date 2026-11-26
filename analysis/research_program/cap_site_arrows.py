"""Necessary strip test using only site outdegrees, no component partition."""
from functools import lru_cache
from itertools import product
from .finite_cap_language import extend


def moves(state, v, drop, last=False):
    m, above, used, first = state
    if v & ((m << 1) | (m >> 1)):
        return
    old = (m >> 1) & 7
    vert = ((v | m) >> 1) & 7
    lat = (m << 1) | (m >> 1)
    bare = 14 & ~m
    iso = bare & ~(v | above | lat)
    double = bare & 10 & (((m << 1) & (m >> 1)) | (v & above))
    cost = iso.bit_count() + int(bool(iso & 4)) + double.bit_count()
    cost += 2*int(bool(v & 4 & ~(m | (v << 1) | (v >> 1))))
    cost += int(bool(v & 4 & ((v << 1) ^ (v >> 1))))
    for down in range(8):
        if down & ~vert or down & used or (last and down):
            continue
        if first and down != 2*drop:
            continue
        unsent = 7 & ~(down | used)
        if not first and unsent & ~old & ~(iso >> 1):
            continue
        sinks = 0 if first else (unsent & old).bit_count()
        for dirs in product(*[(0,1) if (v >> i) & 3 else (-1,) for i in range(4)]):
            busy = vert ^ down
            for i,d in enumerate(dirs):
                if d == -1:
                    continue
                who = i-1 if d else i
                if 0 <= who < 3:
                    if busy & (1 << who):
                        break
                    busy |= 1 << who
            else:
                yield ((v & 3)+4*(dirs[0]==1), (v >> 3)+4*(dirs[3]==1),
                       (v,m & 14,busy,False), cost+2*sinks)


@lru_cache(None)
def build(edge, drop):
    states = [(4,0,5,True)]
    ids = {states[0]: 0}
    arcs, ends = [], {}
    for i,s in enumerate(states):
        row = set()
        for v in range(32):
            if (edge=='L' and v & 3) or (edge=='R' and v & 24):
                continue
            for l,r,t,z in moves(s,v,drop):
                if t not in ids:
                    ids[t] = len(states)
                    states.append(t)
                row.add((l,r,ids[t],z))
        arcs.append(sorted(row))
        for _,_,_,z in moves(s,0,drop,last=True):
            cost = z+(14 & ~s[0]).bit_count()+int(not (s[0] & 4))
            ends[i] = min(ends.get(i,cost),cost)
    return states,arcs,ends


def transfer(edge,drop):
    return build(edge,drop)[1:]


def extend_sites(options,edge,limit):
    return extend(options,edge,limit,local=transfer)
