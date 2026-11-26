"""Local-current test on a real square, retaining boundary and internal edge data."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import subprocess
from .height_free_flux import TABLE,STATES

DIR=((0,1),(1,0),(0,-1),(-1,0))


def states(dirs):
    for f in (0,1):
        for nb in product((0,1),repeat=len(dirs)):
            m=dict(zip(dirs,nb))
            if any(m.get(i) and m.get((i+1)%4) for i in range(4)):continue
            for out in [-1]+[i for i in dirs if f or m[i]]:
                sig={}
                for i in dirs:
                    a,b=(f,m[i]) if i<2 else (m[i],f)
                    sign=(1 if out==i else -1)*(1 if i<2 else -1) if a or b else 0
                    sig[i]=(a,b,sign)
                yield f,sig


def lpterms(c):
    return " ".join(("+" if v>=0 else "-")+f" {abs(v)} "+s for s,v in c.items() if v)


def problem(depth,period,n,root=False):
    def axis(i):
        if i<depth:return i
        if i>=n-depth:return depth+period+i-(n-depth)
        return depth+(i-depth)%period
    kinds=Counter((axis(i),axis(j)) for i,j in product(range(n),repeat=2))
    locs=defaultdict(list)
    for i,j in product(range(n),repeat=2):locs[axis(i),axis(j)].append((i,j))
    coords={};marg=defaultdict(Counter);cons=[];objective=Counter()
    for t,sites in locs.items():
        i,j=sites[0]
        dirs=[s for s,(x,y) in enumerate(DIR) if 0<=i+x<n and 0<=j+y<n]
        row={}
        for f,sig in states(dirs):
            if root and (i,j)==(0,0) and any((s<2 and a[2]==1) or (s>=2 and a[2]==-1) for s,a in sig.items()):continue
            x=f"x{len(coords)}";coords[x]=(t,f,sig);row[x]=1
            if f:objective[x]=kinds[t]
            for s,e in sig.items():marg[t,s,e][x]=1
        cons.append((row,1))
    edges=set()
    for i,j in product(range(n),repeat=2):
        for s,(a,b) in enumerate(DIR[:2]):
            if i+a<n and j+b<n:
                edges.add(((axis(i),axis(j)),(axis(i+a),axis(j+b)),s))
    letters=[(0,0,0)]+[(a,b,c) for a,b in [(0,1),(1,0),(1,1)] for c in (-1,1)]
    for u,v,s in sorted(edges):
        for e in letters:
            row=marg[u,s,e].copy();row.subtract(marg[v,s+2,e])
            if any(row.values()):cons.append((row,0))
    return coords,cons,objective


def solve(depth,period,n,root=False):
    coords,cons,obj=problem(depth,period,n,root)
    text="max: "+lpterms(obj)+";\n"+"".join(lpterms(c)+f" = {b};\n" for c,b in cons)
    result=subprocess.run(["lp_solve"],input=text,text=True,capture_output=True,check=True)
    vals={x:Q(y).limit_denominator(10000) for line in result.stdout.splitlines() if len(line.split())==2
          for x,y in [line.split()] if x in coords}
    assert len(vals)==len(coords) and min(vals.values())>=0
    assert all(sum(v*vals[x] for x,v in c.items())==b for c,b in cons)
    return coords,vals,sum(v*vals[x] for x,v in obj.items())


FILE=Path(__file__).with_name("square_current_obstruction.json")


def generate():
    # Fit only 81 tile types, on a 14-square. Store sparse positive
    # local state weights, not an optimizer's claimed objective value.
    coords,vals,_=solve(4,1,14,root=True)
    atom=defaultdict(list)
    for x,(t,f,sig) in coords.items():
        if not vals[x]:continue
        # Physical directions absent from this type are denoted 9.
        nb=tuple(sig[s][1 if s<2 else 0] if s in sig else 9 for s in range(4))
        out=next((s for s in sig if sig[s][2]==(1 if s<2 else -1)),-1)
        atom[t].append([f,*nb,out,str(vals[x])])
    FILE.write_text(json.dumps([atom[i,j] for i,j in product(range(9),repeat=2)],separators=(',',':'))+'\n')


def load():
    groups=json.loads(FILE.read_text())
    assert len(groups)==81
    data={}
    for t,ls in zip(product(range(9),repeat=2),groups):
        dirs=[s for s,v in enumerate((t[1]<8,t[0]<8,t[1]>0,t[0]>0)) if v]
        allowed=list(states(dirs))
        dist=[]
        for f,*row in ls:
            a,b,c,d,out,mass=row; nb=[a,b,c,d]
            assert all(nb[s]==9 for s in range(4) if s not in dirs)
            assert out==-1 or out in dirs and (f or nb[out])
            assert t!=(0,0) or out==-1
            sig={s:((f,nb[s]) if s<2 else (nb[s],f))+
                 (((1 if s==out else -1)*(1 if s<2 else -1) if f or nb[s] else 0),)
                 for s in dirs}
            assert (f,sig) in allowed and Q(mass)>0
            dist.append((f,sig,out,Q(mass)))
        assert sum(v for *_,v in dist)==1
        data[t]=dist
    return data


def axis(i,n):
    return i if i<4 else i-n+9 if i>=n-4 else 4


def marginal(dist,s):
    m=Counter()
    for _,sig,_,v in dist:m[sig[s]]+=v
    return m


def proof(data):
    # Side 10 realizes every possible neighboring type pair including an
    # interior-to-interior edge. Each larger side has exactly these pairs.
    n=10;edge_types=set()
    for i,j in product(range(n),repeat=2):
        u=axis(i,n),axis(j,n)
        for s,(a,b) in enumerate(DIR[:2]):
            if i+a<n and j+b<n:edge_types.add((u,(axis(i+a,n),axis(j+b,n)),s))
    for u,v,s in edge_types:
        assert marginal(data[u],s)==marginal(data[v],s+2)
    weights={t:sum(f*v for f,_,_,v in dist) for t,dist in data.items()}
    outer=[i for i in range(9) if i!=4]
    A=weights[4,4];B=sum(weights[4,j]+weights[j,4] for j in outer)
    C=sum(weights[i,j] for i,j in product(outer,repeat=2))
    assert (A,B,C)==(Q(1,3),Q(19,3),Q(82,3))
    print("rooted vertex types",len(data),"positive states",sum(map(len,data.values())),
          "matching edge-type marginals",len(edge_types))
    print("score = (n-8)^2/3 + 19(n-8)/3 + 82/3 = n^2/3 + n - 2")


def currents(data,n):
    # Orient each sector's *coordinate system* by its nearest side, rotating
    # clockwise from top through right, bottom, left. Ties are deterministic.
    ed=defaultdict(list);slack=0;total=0
    for r,c in product(range(n),repeat=2):
        sep=(r,n-1-c,n-1-r,c);side=sep.index(min(sep))
        col=(c,r,n-1-c,n-1-r)[side]
        dist=data[axis(r,n),axis(c,n)]
        avg=0
        for s,(x,y) in enumerate(DIR):
            loc=(s-side)%4;direction=1 if loc<2 else -1
            table=TABLE[(col-int(loc==2))%3][loc%2]
            cur=0
            for f,sig,out,v in dist:
                if s in sig:
                    a,b,_=sig[s]
                    neighbor=b if s<2 else a
                else:
                    # Ghost U leaf; an F-boundary star is completed by an
                    # incoming ghost arrow. It consumes no physical outgoing slot.
                    neighbor=0
                edge=(f,neighbor) if loc<2 else (neighbor,f)
                sign=direction*(1 if out==s else -1) if f or neighbor else 0
                cur+=v*direction*table[STATES.index(edge+(sign,))]
            avg+=cur
            edge_id=tuple(sorted(((r,c),(r+x,c+y))))
            ed[edge_id].append((side,cur))
        mass=sum(f*v for f,_,_,v in dist);total+=mass
        assert avg>=5*(3*mass-1)
        slack+=avg-5*(3*mass-1)
    boundary=cut=0
    for terms in ed.values():
        amount=sum(v for _,v in terms)
        if len(terms)==1:boundary+=amount
        elif terms[0][0]!=terms[1][0]:cut+=amount
        else:assert amount==0
    assert boundary+cut-slack==5*(3*total-n*n)
    target=(n*n+3*n-10)//3
    print("n",n,"target",target,"local score",total,"outer",boundary,
          "internal cut",cut,"vertex slack",slack,"net",boundary+cut-slack)


def forest_cuts(data,n):
    """Look for missing global forest constraints. Stop at the first counter-cut.

    For any nonempty vertex set S, |S|-sum(x_e:e internal to S)
    equals the cut capacity to the sink, using the marginal arc capacities
    and the per-source probability of spending no outgoing arrow.
    """
    from collections import deque
    from math import lcm
    den=lcm(*(v.denominator for xs in data.values() for _,_,_,v in xs))
    sink=n*n;edges=[]
    for r,c in product(range(n),repeat=2):
        i=r*n+c
        caps=Counter()
        for _,_,out,v in data[axis(r,n),axis(c,n)]:
            j=sink if out==-1 else (r+DIR[out][0])*n+c+DIR[out][1]
            caps[j]+=int(den*v)
        edges.extend((i,j,w) for j,w in caps.items() if w)
    adj=[[] for _ in range(sink+1)];initial=[]
    for i,j,w in edges:
        k=len(initial);initial.extend((w,0))
        adj[i].append((j,k));adj[j].append((i,k+1))
    for src in range(sink):
        residual=initial.copy();flow=0
        while flow<den:
            prev={src:None};q=deque([src])
            while q and sink not in prev:
                for j,k in adj[q.popleft()]:
                    if residual[k] and j not in prev:
                        prev[j]=k;q.append(j)
            if sink not in prev:
                S=set(prev);amount=sum(w for i,j,w in edges if i in S and j not in S)
                assert amount==flow<den
                print("n",n,"violated rank cut:",len(S),"vertices,",
                      "internal edge mass",len(S)-Q(flow,den),"limit",len(S)-1)
                return S
            path=[];j=sink
            while j!=src:
                k=prev[j];path.append(k);j=edges[k//2][k%2]
            value=min(residual[k] for k in path);flow+=value
            for k in path:residual[k]-=value;residual[k^1]+=value
    print("n",n,"all nonempty-subset forest rank inequalities pass;",
          sink,"source flow checks")


def face_test(data):
    # A necessary consistency test strictly stronger than sharing one
    # edge. Stars specify their own corner and the two neighboring corners.
    def tri(t,dirs):
        out=Counter()
        for f,sig,o,w in data[t]:
            out[(f,*(sig[s][1 if s<2 else 0] for s in dirs))]+=w
        return out
    for r,c in product(range(9),repeat=2):
        t=[(axis(r+a,10),axis(c+b,10)) for a,b in ((0,0),(0,1),(1,0),(1,1))]
        # physical triples 012, 103, 203, 312
        triples=[tri(t[i],dirs) for i,dirs in enumerate(((0,1),(2,1),(3,0),(3,2)))]
        legal=[b for b in product(range(2),repeat=4) if not(b[0]*b[3] or b[1]*b[2])]
        indices=[(0,1,2),(1,0,3),(2,0,3),(3,1,2)]
        # All allowed patterns (empty, one of four singles, one of four
        # adjacent pairs). Their probabilities are determined uniquely
        # from the single and pair marginals.
        def one(i):return sum(v for (f,a,b),v in triples[i].items() if f)
        weights={}
        for b in legal:
            if sum(b)!=2:continue
            i,j=[i for i,x in enumerate(b) if x]
            h=indices[i].index(j)
            weights[b]=sum(v for k,v in triples[i].items() if k[0] and k[h])
        for i in range(4):
            weights[tuple(int(j==i) for j in range(4))]=one(i)-sum(v for k,v in weights.items() if k[i])
        weights[0,0,0,0]=1-sum(weights.values())
        for i,idx in enumerate(indices):
            probs=Counter()
            for k,v in weights.items():probs[tuple(k[j] for j in idx)]+=v
            if min(weights.values())<0 or probs!=triples[i]:
                print("face obstruction, upper-left",r,c,"on n=10 type template;",
                      "minimum inferred face weight",min(weights.values()),
                      "triple",i,dict(triples[i]),"vs",dict(probs))
                return
    print("all unit-face label marginals consistent")


def oriented_faces(data):
    # Each corner exposes two internal edge states. Find a joint law on
    # all four edges with those required pair distributions.
    axes=((0,1),(2,1),(3,0),(3,2))
    edges=((0,1),(0,2),(1,3),(2,3))
    picks=((0,1),(0,2),(1,3),(2,3))
    patterns=[]
    for f in product(range(2),repeat=4):
        if f[0]*f[3] or f[1]*f[2]:continue
        for signs in product(*[(-1,1) if f[i] or f[j] else (0,) for i,j in edges]):
            src=[u if s==1 else v for (u,v),s in zip(edges,signs) if s]
            if len(set(src))!=len(src):continue
            es=[(f[u],f[v],s) for (u,v),s in zip(edges,signs)]
            patterns.append(tuple(tuple(es[j] for j in ii) for ii in picks))
    seen=set()
    for r,c in product(range(9),repeat=2):
        ds=[data[axis(r+x,10),axis(c+y,10)] for x,y in ((0,0),(0,1),(1,0),(1,1))]
        probs=Counter()
        for i,(ls,dirs) in enumerate(zip(ds,axes)):
            for f,s,o,w in ls:probs[i,tuple(s[x] for x in dirs)]+=w
        sig=tuple(sorted(probs.items()))
        if sig in seen:continue
        seen.add(sig)
        pats=[p for p in patterns if all((i,p[i]) in probs for i in range(4))]
        terms={x:{f'x{j}':v.denominator for j,p in enumerate(pats) if p[x[0]]==x[1]} for x,v in probs.items()}
        if not all(terms.values()):
            print('oriented face fails support at',r,c,next(x for x,row in terms.items() if not row))
            return
        text='min: x0;\n'+''.join(lpterms(row)+f' = {probs[x].numerator};\n' for x,row in terms.items())
        res=subprocess.run(['lp_solve'],input=text,text=True,capture_output=True)
        if res.returncode!=0:
            print("oriented face unresolved at",r,c,"solver status",res.returncode)
            return
        vals={s:Q(v).limit_denominator(10000) for l in res.stdout.splitlines() if len(l.split())==2
              for s,v in [l.split()] if s.startswith('x') and s[1:].isdigit()}
        assert min(vals.values())>=0 and all(sum(v*vals[s] for s,v in row.items())==probs[x].numerator for x,row in terms.items())
    print("oriented unit-face joint distributions verified:",len(seen),"distinct cases")


if __name__=="__main__":
    import sys
    if '--generate' in sys.argv:generate()
    data=load();proof(data)
    for n in (17,20,23,26,32):currents(data,n)
    if '--forest-cuts' in sys.argv:
        for n in (14,17,20,23,26,32):forest_cuts(data,n)
    face_test(data)
    if '--faces' in sys.argv:oriented_faces(data)
