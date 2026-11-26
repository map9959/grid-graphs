"""Remove a cycle mark from a near miss, then try every single mark insertion."""
from .zipper_rails import build,verify
from .side28_sat import cycle
from pathlib import Path
import sys


def exchange(n,S):
    sys.setrecursionlimit(n*n+100)
    adj=[[v for v in (u-n,u+n,u-1,u+1) if 0<=v<n*n and abs(u//n-v//n)+abs(u%n-v%n)==1] for u in range(n*n)]
    def root(par,u):
        while par[u]!=u:u=par[u]
        return u
    trav=cycle(S,n)
    if not trav:return S
    for a in set(trav)&S:
        s=S-{a};p=list(range(n*n));ok=True
        for u in s:
            for v in adj[u]:
                if v<u and v in s:continue
                x,y=root(p,u),root(p,v)
                if x==y:ok=False;break
                p[x]=y
            if not ok:break
        if not ok:continue
        reps=[root(p,i) for i in range(n*n)]
        for v in range(n*n):
            if v in S:continue
            parts=[reps[v]]+[reps[z] for z in adj[v] if z not in s]
            if len(parts)==len(set(parts)):return s|{v}


def save(n,s):
    rows=[''.join('#' if n*i+j in s else '.' for j in range(n)) for i in range(n)]
    print('verified',verify(rows),flush=True)
    Path(__file__).with_name(f'forest_{n}_exchange.txt').write_text('\n'.join(rows)+'\n')


if __name__=='__main__':
    n=77
    for e in range(6):
        for m in range(13):
            r=list(map(list,build(n,extra=e)));r[0][1]='.';r[1][0]='#'
            for a in range(m+1):
                r[a+2][3*a]='#'
                if a<m:r[a+2][3*a+2]='.'
            S={n*i+j for i,s in enumerate(r) for j,x in enumerate(s) if x=='#'}
            if len(S)!=2048:continue
            res=exchange(n,S)
            if res:save(n,res);sys.exit()
        print('single-exchange scan completed for wait',e,flush=True)
