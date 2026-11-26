"""An exact physical rim glued to the necessary two-tile bulk relations."""
from itertools import product
from pathlib import Path
import sys
from .saturated_tile_phase import relation,ROW,COL
from .defect_window import window,table
from .depth_two_far_quarter import run

def graph(tables,di,dj):
    x=40;g=[];rows=range(34+min(0,3*di),49+max(0,3*di));cols=range(34+min(0,3*dj),49+max(0,3*dj))
    def emit(f,bit,flags):
        g.append(relation(f,[[bit(x+a+3*di*h,x+b+3*dj*h) for a,b in product(range(3),repeat=2)] for h in (0,1)]))
    window(119,'rim',1,tables,domain=set(product(rows,cols)),want=False,emit=emit,turn_domain=set())
    return g[0]

def test(n,W,lo,hi,seconds):
    tab=table(119);rules={(di,dj):graph(tab,di,dj) for di,dj in ((0,1),(1,0),(1,1),(1,-1))}
    ds=range(14,n-14,3);dom={(i,j) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<W}
    def extra(f,bit,flags):
        # Pre-existing rim variables are allocated before any new tile ID.
        top=f.nv;states=sorted(rules[0,1]);assert len(states)==31
        def new():
            nonlocal top
            top+=1;return top
        words={};axis=new();rows={i:new() for i in ds};cols={j:new() for j in ds}
        for z in rows.values():f.append([-z,axis])
        for z in cols.values():f.append([-z,-axis])
        for i,j in product(ds,repeat=2):
            vs=[bit(i+a,j+b) if (i+a,j+b) in dom else None for a,b in product((-1,0,1),repeat=2)]
            assert max((z for z in vs if z is not None),default=0)<=base_nv
            word=words[i,j]={m:new() for m in states};f.append(list(word.values()))
            # Against a five-bit private code, two distinct words cannot
            # both be selected. Visible tiles instead use their own marks.
            binary=[] if all(vs) else [new() for _ in range(5)]
            for k,(m,z) in enumerate(word.items()):
                for h,v in enumerate(binary):f.append([-z,v if k>>h&1 else -v])
                for h,v in enumerate(vs):
                    if v:f.append([-z,v if m>>h&1 else -v])
                if m&16 and m&130:f.append([-z,rows[i]])
                if m&16 and m&40:f.append([-z,cols[j]])
                if m not in ROW:f.append([-rows[i],-z])
                if m not in COL:f.append([-cols[j],-z])
        for (di,dj),g in rules.items():
            back={m:{u for u in g if m in g[u]} for m in states}
            for (i,j),a in words.items():
                b=words.get((i+3*di,j+3*dj))
                if b is None:continue
                for m in states:
                    f.append([-a[m],*(b[k] for k in sorted(g[m]))])
                    f.append([-b[m],*(a[k] for k in sorted(back[m]))])
        print('tile alphabet',len(states),'pair rules',[sum(map(len,g.values())) for g in rules.values()],'bulk tiles',len(words),flush=True)
    def install(f,bit,flags):
        nonlocal base_nv
        base_nv=f.nv;extra(f,bit,flags)
    base_nv=0
    def replay(w,site,X,out):
        print('rim/tiles SAT; frame',w,'star',site,'not a full-board witness')
    run(n,lo,hi,seconds,domain=dom,output=f'target/tile_rim_{n}_{W}_{lo}_{hi}',extra=install,replay=replay)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
