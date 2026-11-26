"""Search for a height-independent local flux for the grounded rod transition."""
from itertools import product
from fractions import Fraction as Q
from collections import Counter
import subprocess

DIR=((0,1),(1,0),(0,-1),(-1,0))
STATES=((0,0,0),(0,1,-1),(0,1,1),(1,0,-1),(1,0,1),(1,1,-1),(1,1,1))
# Currents in integer units (five times the LP variables). Order E,S.
TABLE=(
    ((1,1,-5,7,-2,4,-2),(6,6,0,12,6,12,0)),
    ((2,2,-4,5,-1,2,-4),(0,0,-6,6,0,6,0)),
    ((0,0,-3,6,0,6,0),(0,0,-3,3,0,3,-3)),
)


def audit():
    def current(c,axis,e):
        return TABLE[c%3][axis][STATES.index(e)]
    slacks=Counter()
    for c in range(3):
        for f,e in atoms(c):
            div=current(c,0,e[0])+current(c,1,e[1])-current(c-1,0,e[2])-current(c,1,e[3])
            slack=div-5*(3*f-1)
            assert slack>=0
            slacks[slack]+=1
    print("integer local checks",sum(slacks.values()),"minimum slack",min(slacks))
    def flux(phase,out):
        total=0
        for c in range(3):
            f=int(c==phase)
            arrow=out if f else (0 if (c+1)%3==phase else 2)
            total+=current(c,1,letters(f,1,f,arrow))-current(c,0,letters(f,0,int((c+1)%3==phase),arrow))
        return total
    for a,b in product((1,3),repeat=2):
        m=int(a==1)+int(b==3)
        coeff=flux(1,a)-flux(0,b)+15*m
        assert coeff>=18
        print("upper/lower rail directions","S" if a==1 else "N","S" if b==1 else "N",
              "upper flux",flux(1,a),"lower flux",flux(0,b),"paid",m,"margin",coeff)


def check_witness(p):
    """Independent physical cut calculation; do not use the quotient's Euler count."""
    from .triple_pocket import run
    result,sites=run(-3,5,p,8*p-1)
    core={(r,c) for i,(s,r,c) in enumerate(sites) if i in result['selected'] and s=='C'}
    delta=len(core)-9*p
    W=3*p
    def selected(v):
        z,c=v;r=z+c%3
        return ((r,c) in core if -3<=r<=5 else c%3==int(r< -3))
    def nb(v,i):
        z,c=v;dr,dc=DIR[i]
        return z+dr-dc,(c+dc)%W
    vertices={(z,c) for z in range(-15,16) for c in range(W)}
    edges=set()
    for u in vertices:
        for i in (0,1):
            v=nb(u,i)
            if v in vertices and (selected(u) or selected(v)):edges.add(tuple(sorted((u,v))))
    # M=0 on the verified witnesses. Prescribe all far-background arrows
    # there to be out along the rail, or from a U leaf into its rail.
    arrows={}
    for u in vertices:
        z,c=u
        if -10<=z<=10:continue
        phase=1 if z<0 else 0
        i=(3 if z<0 else 1) if selected(u) else (0 if (c+1)%3==phase else 2)
        arrows[u]=i
    rest={e for e in edges if not any(u in arrows and nb(u,arrows[u])==v for u,v in (e,e[::-1]))}
    adjacency={u:[] for u in vertices}
    for u,v in rest:adjacency[u].append(v);adjacency[v].append(u)
    # Propagate from prescribed sinks. Then peel remaining components: trees
    # accept a sink; a unicyclic component accepts a consistent cycle.
    stack=list(arrows)
    def point(u,v):
        arrows[u]=next(i for i in range(4) if nb(u,i)==v)
    while stack:
        u=stack.pop()
        for v in adjacency[u]:
            e=tuple(sorted((u,v)))
            if e not in rest:continue
            assert v not in arrows;point(v,u);rest.remove(e);stack.append(v)
    degree={u:0 for u in vertices}
    for u,v in rest:degree[u]+=1;degree[v]+=1
    stack=[u for u in vertices if degree[u]==1]
    while stack:
        u=stack.pop()
        for v in adjacency[u]:
            e=tuple(sorted((u,v)))
            if e not in rest:continue
            point(u,v);rest.remove(e);degree[v]-=1
            if degree[v]==1:stack.append(v)
    while rest:
        u=min(min(rest))
        while u not in arrows:
            v=next(v for v in adjacency[u] if tuple(sorted((u,v))) in rest)
            point(u,v);rest.remove(tuple(sorted((u,v))));u=v
    assert all(sum(int(a in arrows and nb(a,arrows[a])==b) for a,b in (e,e[::-1]))==1 for e in edges)
    def edge(u,i):
        c=u[1];v=nb(u,i)
        if i in (2,3):u,v=v,u;c=u[1];i-=2
        f=int(selected(u));h=int(selected(v));a=arrows.get(u,-1)
        return TABLE[c%3][i][STATES.index((f,h,(1 if a==i else -1) if f or h else 0))]
    total=0;slack=0
    for u in vertices:
        if abs(u[0])>11:continue
        div=edge(u,0)+edge(u,1)-edge(u,2)-edge(u,3)
        s=div-5*(3*int(selected(u))-1);assert s>=0
        slack+=s;total+=div
    assert slack==total-15*(delta-p)
    assert total==-18*p
    print("uncontracted witness",p,"net core",delta,"total divergence",total,"summed local slack",slack)


def letters(f,d,nb,out):
    # Canonical orientation of an edge is east or south. The sign is
    # +1 for a forced arrow in that orientation, -1 for the reverse.
    a,b=(f,nb) if d<2 else (nb,f)
    s=(1 if out==d else -1)*(1 if d<2 else -1) if a or b else 0
    return a,b,s


def atoms(c):
    ans=[]
    for f in (0,1):
        for nb in product(range(2),repeat=4):
            if any(nb[i] and nb[(i+1)%4] for i in range(4)):continue
            for out in range(-1,4):
                if out!=-1 and not (f or nb[out]):continue
                e=tuple(letters(f,d,nb[d],out) for d in range(4))
                ans.append((f,e))
    return ans


def lpstr(terms):
    return " ".join(f"{v:+d} {n}" for n,v in sorted(terms.items()) if v) or "0"


def bound(pair=False):
    names={}
    def var(c,d,e):
        return names.setdefault((c%3,d,e),"v"+str(len(names)))
    def terms(c,e):
        z=Counter()
        for d in range(4):
            z[var(c-int(d==2),d%2,e[d])]+=1 if d<2 else -1
        return z
    constraints=set()
    states=atoms(0)
    for c in range(3):
        for f,e in states:
            if not pair:
                constraints.add(lpstr(terms(c,e))+f" >= {3*f-1}")
            else:
                for h,u in states:
                    if e[0]!=u[2]:continue
                    if (f and (u[1][1] or u[3][0])) or (h and (e[1][1] or e[3][0])):continue
                    a=terms(c,e);a.update(terms(c+1,u))
                    constraints.add(lpstr(a)+f" >= {3*(f+h)-2}")
    def rail(phase,direction):
        # Across a d=r-c cut positive normals are south and west.
        z=Counter()
        for c in range(3):
            f=int(c==phase)
            out=direction if f else (0 if (c+1)%3==phase else 2)
            z[var(c,0,letters(f,0,int((c+1)%3==phase),out))]-=1
            z[var(c,1,letters(f,1,f,out))]+=1
        return z
    for a,b in product((1,3),repeat=2):
        low=rail(1,a);low.subtract(rail(0,b))
        low['margin']-=1
        # Want low-high+3*M >= margin.
        constraints.add(lpstr(low)+f" >= {-3*(int(a==1)+int(b==3))}")
    text="max: margin;\n"+";\n".join(sorted(constraints))+";\nfree "+", ".join([*names.values(),"margin"])+";\n"
    res=subprocess.run(["lp_solve"],input=text,text=True,capture_output=True)
    print("tile size",2 if pair else 1,"variables",len(names)+1,"constraints",len(constraints),
          res.stdout.splitlines()[:3],res.stderr[:200])
    if not pair:
        vals={a:Q(b) for line in res.stdout.splitlines() if len(line.split())==2
              for a,b in [line.split()] if a in names.values()}
        for c,d in product(range(3),range(2)):
            print(c,d,[(e,5*vals[v]) for (i,j,e),v in sorted(names.items()) if (i,j)==(c,d)])
    return res.stdout


if __name__=="__main__":
    import sys
    audit()
    if '--witnesses' in sys.argv:
        for p in (2,3):check_witness(p)
    if '--synthesize' in sys.argv:
        bound()
