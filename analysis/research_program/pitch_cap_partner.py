"""Rank spectrum of a finite pitch cap, paired with an unrestricted opposite cap."""
import argparse
import subprocess
from itertools import product


def spectrum(n,h):
    pos={};earlier=[];tags=[];fix=[]
    def add(key,terminal):
        pos[key]=len(pos);earlier.append([]);tags.append(int(terminal));fix.append(0 if terminal else -1)
    for x in range(n):
        root=('tooth',(x+1)//3)
        if root not in pos:add(root,True)
        for y in range(h):
            key=(y,x);add(key,False);es=earlier[-1]
            if x:es.append((pos[y,x-1],False))
            if y:es.append((pos[y-1,x],False))
            else:es.append((pos[root],x%3==0))
    N=len(pos);inp=[N,*[v for es in earlier for v in (len(es),*(1+j+N*b for j,b in es))],
                    *fix,-2,*tags]
    out=subprocess.run(['target/annular_frontier','--counts'],input=' '.join(map(str,inp)),
                       text=True,capture_output=True,check=True)
    r=(n+2)//3
    return {r-c:m-h*r for c,m in (map(int,line.split()) for line in out.stdout.splitlines())}


def upper(n,spec):
    k=n//3;r=k+1
    def total(j,b,d=0,v=0):
        # v counts lateral vacancy runs only on the unrestricted partner.
        t=k-j-d
        return n*r+b+min((6*k+15*t-10*v)//20,(2*k+t-3)//3)
    return {j:total(j,b) for j,b in spec.items()}


def two_ends(h):
    """A price for both *outer* caps with a free (possibly very long) middle band."""
    from .seam_rank_cost import run
    from unittest.mock import patch
    with patch('sys.argv',['cap','--free-top','--prices=10,7','--classes','--quiet']):
        bins,_=run(103,h)
    connected=(bins[1]-7)//10-35*h
    other=bins[2]-350*h-245
    print('depth',h,'single-class bonus <=',connected,'other classes: 10b-7j <=',other)
    # Strip between the two outermost cuts costs its rank excess.
    def bound(j):
        return connected if j==34 else (other+7*j)//10
    result=3605+max(bound(i)+bound(j)-max(0,i+j-34) for i,j in product(range(35),repeat=2))
    print('two outer caps, both of depth at most',h,'integer upper',result,flush=True)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('heights',nargs='+',type=int)
    p.add_argument('--two-ends',action='store_true');args=p.parse_args()
    for h in args.heights:
        if args.two_ends:two_ends(h);continue
        s=spectrum(103,h);u=upper(103,s);print('depth',h,'rank-priced upper',max(u.values()),
             'possible shallow ranks at 3647',sorted(j for j,v in u.items() if v>=3647),flush=True)
