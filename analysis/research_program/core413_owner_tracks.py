"""Free-length interface relations retaining marks, arrows and acyclicity."""
from array import array
from itertools import product
from functools import lru_cache
from .joint_rim_pump import kernel
from .core413_seams import D

@lru_cache(None)
def ports(H,phase,positive,stationary):
    cols,arcs,extend=kernel(H,star_dir=0)
    initial=tuple(range(H))*2;dp={};entries=[]
    for a,b in product(cols,repeat=2):
        if a&((b<<1)|(b>>1)):continue
        for w in range(1<<H):
            if w&~(a|b) or not arcs(12+phase,a,b,w):continue
            dp[a,b,w,initial]=1<<len(entries);entries.append((a,b,w))
    keep=None;old=None
    for length in range(150):
        if length%42==2 and (not positive or length>=44):
            if dp==old:break
            old=dp
            dest={}
            for (a,b,w,_),bits in dp.items():
                e=(a,b,w);dest[e]=dest.get(e,0)|bits
            if keep is None:keep=dest
            elif stationary:keep={e:z&dest.get(e,0) for e,z in keep.items() if z&dest.get(e,0)}
            else:
                for e,z in dest.items():keep[e]=keep.get(e,0)|z
        nd={}
        for (a,b,w,p),bits in dp.items():
            for c,nw,q in arcs(12+(phase+length)%3,a,b,w):
                if q:continue
                v=extend(b,c,p)
                if v is not None:
                    key=b,c,nw,v;nd[key]=nd.get(key,0)|bits
        dp=nd
    else:raise AssertionError('no 42-step stabilization')
    print('owner track',H,phase,'repeat through length',length,'pairs',sum(z.bit_count() for z in keep.values()),flush=True)
    return entries,keep

def install(n,cuts,positive,stationary,H,marks,fresh,add):
    dirs=array('I');dirs.frombytes((D/'arcs.bin').read_bytes())
    for vert,cut in ((False,cuts[1]),(False,cuts[2]),(True,cuts[0])):
        for far in (False,True):
            rev=not far if vert else far or cut==cuts[2]
            entry=cut if rev else cut-1;sign=-1 if rev else 1
            ls,relation=ports(H,(n-1-entry if rev else entry)%3,positive or vert,stationary)
            def endpoint(cur,states):
                words={}
                for key in states:
                    z=fresh();words[key]=z
                    for g,m in enumerate(key):
                        j=cur-sign if g==0 else cur
                        for r in range(H):
                            i=n-1-r if far else r
                            p=n*j+i if vert else n*i+j
                            # DIR order east, south, west, north.
                            v=dirs[4*p+((1 if rev else 3) if vert else (0 if rev else 2))] if g==2 else marks[p]
                            assert v>0;add([-z,v if m>>r&1 else -v])
                add(list(words.values()));return words
            left=endpoint(entry,ls);right=endpoint(entry+2*sign,relation)
            for e,z in right.items():add([-z,*[left[s] for i,s in enumerate(ls) if relation[e]>>i&1]])
