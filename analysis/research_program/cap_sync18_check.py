"""Replay the surviving row words with a single physical cylinder partition."""
from subprocess import run
from functools import lru_cache

def transfer(rows,w):
    full=(1<<w)-1;rails=sum(1<<i for i in range(0,w,3))
    dp={(rails,(0,)*(w+1),1):0}
    @lru_cache(maxsize=100000)
    def add(st,v):
        old,part,cycles=st
        if v&((old<<1)|(old>>1)|(old>>(w-1))|((old&1)<<(w-1))):return
        par=[*part,*range(w+1,2*w+1)];cyc={i for i in range(w+1) if cycles>>i&1}
        def root(i):
            while par[i]!=i:i=par[i]
            return i
        def edge(a,b):
            a,b=root(a),root(b)
            if a==b:
                if a in cyc:return False
                cyc.add(a)
            else:
                if a in cyc and b in cyc:return False
                par[a]=b
                if a in cyc:cyc.remove(a);cyc.add(b)
            return True
        for i in range(w):
            j=(i+1)%w
            if ((old|v)>>i)&1 and not edge(1+i,w+1+i):return
            if v&((1<<i)|(1<<j)) and not edge(w+1+i,w+1+j):return
        reps=[root(0),*[root(w+1+i) for i in range(w)]]
        z=tuple(reps.index(a) for a in reps)
        return v,z,sum(1<<i for i,a in enumerate(reps) if i==z[i] and a in cyc)
    peak=0
    for masks in rows:
        nd={}
        for st,score in dp.items():
            for v in masks:
                u=add(st,v)
                if u is not None:nd[u]=max(nd.get(u,-10**6),score+v.bit_count()-w//3)
        dp=nd;peak=max(peak,len(dp))
    return max(dp.values(),default=None),peak

def audit():
    for name in ('cap_event_band','cap_sync18'):
        run(['rustc','--edition=2021','-O',f'src/bin/{name}.rs','-o',f'target/{name}'],check=True)
    for p in range(3):
        assert run(['target/cap_event_band','9',str(p),'3'],capture_output=True,text=True,check=True).stdout.startswith('EMPTY')
    h=22
    s=run(['target/cap_sync18',str(h),'--emit'],capture_output=True,text=True,check=True).stdout
    rows=[list(map(int,line.split()[1:])) for line in s.splitlines() if line.startswith('ROW ')]
    assert len(rows)==h
    value,peak=transfer(rows,18)
    print('18-column synchronized row domains',list(map(len,rows)))
    print('full pseudoforest maximum on survivors',value,'peak',peak)
    assert value is None or value<2
if __name__=='__main__':audit()
