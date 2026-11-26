"""Search for a small height-14 schedule. Only Lean checks the resulting certificate."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import ast


def initial(h):
    p = Path("lean/GridGraphs/ResidueTwoUpper/OneGap")
    extra = next(ast.literal_eval(a.value) for a in ast.parse((p/"SouthCapCatalogue.py").read_text()).body
                 if isinstance(a, ast.Assign) and a.targets[0].id == "EXTRA")
    bank = {}
    for t,s in zip(product(range(6,13),repeat=2),(p/"SouthCapBank.txt").read_text().splitlines()):
        words = bank[t] = set(extra.get(t, ()))
        for j in range(0,len(s),6):
            m = sum((ord(ch)-48) << (6*i) for i,ch in enumerate(s[j:j+6]))
            words.add(tuple((m >> (9*i)) & 511 for i in range(4)))
    w = 3*h//4+3
    return {(r,c): {v for v in bank[max(6,14+r-h),max(6,14+c-w)]
                    if r or v[0]==v[1]==73} for r,c in product(range(h-1),range(w-1))}


def seams(d):
    dirs = [(-1,0,0,1,2,3),(1,0,2,3,0,1),(0,-1,0,2,1,3),(0,1,1,3,0,2)]
    n = 0
    while True:
        out = {}
        for (r,c),words in d.items():
            for dr,dc,a,b,i,j in dirs:
                other = d.get((r+dr,c+dc))
                if other is not None:
                    pairs = {(x[i],x[j]) for x in other}
                    words = {x for x in words if (x[a],x[b]) in pairs}
            out[r,c] = words
        if d==out: return d,n
        d,n = out,n+1
        if not all(out.values()): return out,n


@lru_cache(maxsize=100000)
def row(state,old,m,tooth,opened):
    lab,mark,op = state
    p = list(lab)+list(range(7,13))
    marks = [mark>>i&1 for i in range(7)]+[m>>i&1 for i in range(6)]
    opens = [op>>i&1 for i in range(7)]+[opened>>i&1 for i in range(6)]
    def root(i):
        while p[i]!=i: i=p[i]
        return i
    def edge(i,j):
        i,j=root(i),root(j)
        if i==j:return False
        p[i]=j; marks[j]|=marks[i];opens[j]|=opens[i]
        return True
    for i in range(6):
        if old>=0 and (old|m)>>i&1 and not edge(i,i+7):return
        if i and m>>(i-1)&3 and not edge(i+6,i+7):return
        if m&tooth&(1<<i) and not edge(i+7,6):return
    keep=[root(i) for i in [7,8,9,10,11,12,6]]
    if any(marks[k] and not opens[k] and k not in keep for k in map(root,range(6))):return
    return tuple(keep.index(k) for k in keep),sum(marks[k]<<i for i,k in enumerate(keep)),sum(opens[k]<<i for i,k in enumerate(keep))


@lru_cache(maxsize=None)
def mask(horizontal,line,phase):
    return sum((line[i//3]>>((3*(i%3)+phase) if horizontal else (3*phase+i%3))&1)<<i for i in range(6))


def strip(d,h,w,hor,x):
    length,extent=(w,h) if hor else (h,w)
    def point(j):return (x,j) if hor else (j,x)
    def advance(j,a,b,state):
        old=mask(hor,a,2) if a else -1
        for phase in range(3):
            m=mask(hor,b,phase)
            teeth=(63 if 3*j+phase+2==3*length else 0)|(16 if x+2==extent else 0)
            if hor and x==0 and 3*j+phase+3==3*w:teeth|=2
            if not hor and j==0 and phase==1 and x+2==w:teeth|=8
            exits=63 if j==0 and phase==0 else 1|(32 if x+2!=extent else 0)
            state=row(state,old,m,teeth,exits)
            if state is None:return
            old=m
        return state
    history=[]
    for j in range(length-1):
        edges={}
        for v in d[point(j)]:
            a,b=((v[0],v[2]),(v[1],v[3])) if hor else (v[:2],v[2:])
            edges.setdefault(a,[]).append((b,v))
        if j==0:
            front={(a,s) for a in edges if (s:=advance(0,None,a,(tuple(range(7)),0,64))) is not None}
        arcs=[]
        for a,s in front:
            for b,v in edges.get(a,()):
                t=advance(j+1,a,b,s)
                if t is not None:arcs.append(((a,s),(b,t),v))
        front={e[1] for e in arcs}
        history.append(arcs)
    live={(b,t) for b,t in front if not t[1]&~t[2]}
    out=dict(d)
    for j in reversed(range(length-1)):
        arcs=[e for e in history[j] if e[1] in live]
        out[point(j)]={e[2] for e in arcs}
        live={e[0] for e in arcs}
    return out


if __name__=="__main__":
    h,w=14,13
    d,n=seams(initial(h))
    print("initial seams",n,flush=True)
    # Prefer narrow-state strips; score candidates by seam propagation.
    while all(d.values()):
        best=None
        for hor,ext in [(True,h),(False,w)]:
            for x in range(ext-1):
                out=strip(d,h,w,hor,x)
                if out==d:continue
                out,n=seams(out)
                size=sum(map(len,out.values())) if all(out.values()) else 0
                if best is None or size<best[0]:best=size,hor,x,n,out
                if size==0:break
            if best and best[0]==0:break
        if best is None:raise RuntimeError("open")
        size,hor,x,n,d=best
        print("H" if hor else "V",x,"seams",n,"size",size,flush=True)
