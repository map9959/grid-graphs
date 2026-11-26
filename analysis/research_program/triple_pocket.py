"""Three-column pocket and both frame strips in one voltage-graph repeat."""
from pathlib import Path
import argparse
import json
import subprocess
from collections import defaultdict


def model(lo,hi,period,score):
    assert lo<=0 and hi>=2 and period>=1
    w=3*period
    sites=[('C',r,c) for c in range(w) for r in range(lo,hi+1)]
    sites += [(s,r,c) for s in ('T','B') for r in range(3) for c in range(w)]
    ids={p:i for i,p in enumerate(sites)}
    def split(p):
        s,r,c=p
        return (s,r,c%w),c//w
    def comp(p):
        s,r,c=p
        if s!='C':return p
        # Local r is relative to 3*floor(c/3). Search neighboring rods
        # since a support vertex may belong to a rod in the next repeat.
        j=c//3;y=r+3*j
        for a in range(j-1,j+2):
            if abs(c-3*a-1)+max(0,y-(3*a+lo-1))<=1:return ('A',0,3*a)
            if abs(c-3*a)+max(0,3*a+hi+1-y)<=1:return ('D',0,3*a)
        return p
    def fixed(p):
        s,r,c=p
        return s=='C' and (r<lo and c%3==1 or r>hi and c%3==0)
    def neighbors(p):
        s,r,c=p
        if s=='C':
            for dr,dc in ((-1,0),(1,0),(0,-1),(0,1)):
                yield s,r+dr+3*(c//3-(c+dc)//3),c+dc
        else:
            yield s,r,c-1
            yield s,r,c+1
            if r<2:yield s,r+1,c
            if r:yield s,r-1,c
    edges={};nodes={}
    def node(p):
        name,shift=split(comp(p))
        return nodes.setdefault(name,len(nodes)),shift
    for p in sites:
        for q in neighbors(p):
            if fixed(q):continue # already contracted
            a,b=sorted((p,q))
            # Canonicalize edge in physical coordinates BEFORE contraction.
            e=(split(a)[0],split(b)[0],split(b)[1]-split(a)[1])
            if e in edges:continue
            u,i=node(a);v,j=node(b)
            edge_sites=[ids[k] for k in (split(a)[0],split(b)[0]) if k in ids]
            edges[e]=(u,v,j-i,edge_sites)
    for c in range(w):
        for s,root,force in [('T',3*(c//3),c%3==1),('B',3*((c+1)//3),c%3==0)]:
            u,i=node((s,0,c));v,j=node(('A' if s=='T' else 'D',0,root))
            edges['port',s,c]=(u,v,j-i,[] if force else [ids[s,0,c]])
    # Removed A tail, B head, and one satellite per block.
    debit=period*((1-lo)+(hi-1)+1)
    forbid=set()
    for p in sites:
        s,r,c=p
        for dy in (-1,1):
            rr=r+dy+(3*(c//3-(c+1)//3) if s=='C' else 0)
            q=(s,rr,c+1);q0=split(q)[0]
            if q0 in ids:
                forbid.add(tuple(sorted((ids[p],ids[q0]))))
            elif fixed(q):forbid.add((ids[p],))
        if s=='C':
            for dy in (-1,1):
                if fixed((s,r+dy+3*(c//3-(c-1)//3),c-1)):forbid.add((ids[p],))
    return dict(n=len(nodes),sites=len(sites),target=score+debit,edges=list(edges.values()),
                forbid=sorted(forbid)),sites,debit


def run(lo,hi,period,score):
    data,sites,debit=model(lo,hi,period,score)
    assert len(sites)==period*(3*(hi-lo+1)+18)
    assert sum(not cs for u,v,w,cs in data["edges"])==2*period
    binary=Path(__file__).resolve().parents[2]/'target/release/triple_pocket'
    result=json.loads(subprocess.run([binary],input=json.dumps(data),text=True,capture_output=True,check=True).stdout)
    print("rows",lo,hi,"blocks",period,"net required",score,"debit",debit,
          "status",result["status"],"cuts",result["cuts"],flush=True)
    if result["status"]=="sat":
        coords=defaultdict(list)
        for i in result["selected"]:coords[sites[i][0]].append(sites[i][1:])
        print("witness",dict(coords),flush=True)
        for copies in (1,2,5):
            gain=physical(lo,hi,period,coords,copies)
            assert gain==copies*(len(result["selected"])-debit)
            print("open primal replay",copies,"repeats, net",gain,"forest",flush=True)
    return result,sites


def physical(lo,hi,period,coords,copies):
    # Independent open strip: actual long vertical rods, no contractions,
    # no quotient, no horizontal wrap and no end caps. Move both physical
    # boundaries far enough away for the chosen number of repeats.
    left=4+max(abs(lo),abs(hi))
    blocks=copies*period
    k=left+blocks+left
    n=3*k+2;width=3*blocks;height=n+6
    centers=set();before=0
    for x in range(width):
        j=left+x//3;col=x%3
        for y in range(height):
            r=y-3;rel=r-3*j
            if r<0:sel=(2-y,x%(3*period)) in coords['T']
            elif r>=n:sel=(r-n,x%(3*period)) in coords['B']
            else:
                old=(col==0 and rel>=2 or col==1 and rel<=0 or col==2 and rel==2)
                before+=old
                sel=(rel,x%(3*period)) in coords['C'] if lo<=rel<=hi else old
            if sel:centers.add((y,x))
    par={}
    def find(u):
        while u in par:
            v=par[u]
            if v in par:par[u]=par[v]
            u=v
        return u
    for y in range(height):
        for x in range(width):
            u=(y,x)
            for v in ((y,x+1),(y+1,x)):
                if v[0]>=height or v[1]>=width or not (u in centers or v in centers):continue
                a,b=find(u),find(v)
                assert a!=b,"cycle in physical replay"
                par[a]=b
    return len(centers)-before


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for s in ('lo','hi','period','score'):p.add_argument(s,type=int)
    run(**vars(p.parse_args()))
