"""Projected seven-layer patch-defect arm DP, no SAT or connectivity states.
Explore the strength of allowing an independently chosen zero-price center
star in each patch, and arbitrary numbers of full-price patches.
"""
from .defect_window import table
from .odd_frames import frame
from .seven_threshold import masks
from itertools import product, combinations
from functools import lru_cache

def templates(n):
 T,P,S=table(n)
 @lru_cache(None)
 def dom(i,j):
    ds=tuple(range(4)); tabs=[S(T(0,i+1,j+1),ds,o,o==-1,False) for o in (-1,*ds)]
    def cross(m):return (m>>4&1)+2*(m>>5&1)+4*(m>>7&1)+8*(m>>3&1)+16*(m>>1&1)
    return {m for m,z in enumerate(P(T(1,i,j))) if z in (0,72) and any(t[cross(m)]==0 for t in tabs)}
 return dom

def arms(n,dom,swap,far,positions=None,endFree=False):
 F0=frame(n,(0,far,1,far));F={(j,i):z for (i,j),z in F0.items()} if swap else F0
 def opts(j):return tuple(x for x in range(128) if all((r,j) not in F or x>>r&1==F[r,j] for r in range(7)))
 rep=lambda j:j if j<8 or j+8>=n else 8+(j-8)%3
 @lru_cache(None)
 def succ(j,a,b):return tuple(c for c in opts(j+2) if all(m in dom(r,j) for r,m in enumerate(masks(a,b,c,7))))
 def obs(j,m):return sum(((m>>(c if swap else r))&1)<<i for i,(r,c) in enumerate(positions) if (r if swap else c)==j) if positions is not None else (m<<(7*j) if j<7 else 0)
 states={(a,b,obs(0,a)|obs(1,b)) for a,b in product(opts(0),opts(1))}
 for j in range(n-2):
    states={(b,c,l|obs(j+2,c)) for a,b,l in states for c in succ(rep(j),a,b)}
    if endFree and j==n-11:break
 return {l for a,b,l in states}

def main():
 n=35;dom=templates(n);out=[]
 for swap in [False,True]:
    L=set.union(*(arms(n,dom,swap,k) for k in (1,3)))
    if swap:L={sum(((m>>(7*r+c))&1)<<(7*c+r) for r,c in product(range(7),repeat=2)) for m in L}
    out.append(L)
 print('union',list(map(len,out)),'common',len(out[0]&out[1]),flush=True)
 keys=[(r,c) for r,c in product(range(2,7),repeat=2) if any(len({(m>>(7*c+r))&1 for m in L})>1 for L in out)]
 for d in range(1,8):
    for pts in combinations(keys,d):
      mask=sum(1<<(7*c+r) for r,c in pts);A,B=({m&mask for m in L} for L in out)
      if not A&B:print('signs',pts);return
if __name__=='__main__':main()
