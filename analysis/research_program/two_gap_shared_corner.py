"""Shared interior of the SW closed corner under root and word changes."""
from itertools import product
from pathlib import Path
import subprocess,sys
from inspect import getclosurevars
from pysat.formula import CNF,IDPool
from .defect_window import window,table,DIR
from .odd_frames import frame

def run(size,sec):
    n=329;T=table(n);base=CNF();pool=IDPool()
    depth=lambda i,j:min(i,j,n-1-i,n-1-j)
    dom=set(product(range(n-size,n),range(size)));colors={}
    for corner,root in product((1,3),((0,0),(n-1,0),(n-1,n-1))):
        marks=frame(n,(0,0,1,corner));q=[root];parent={root:-1}
        for u in q:
            for s,(a,b) in enumerate(DIR):
                v=u[0]+a,u[1]+b
                if v in marks and depth(*v)==0 and v not in parent and (marks[u] or marks[v]):parent[v]=(s+2)%4;q.append(v)
        assert all(p in parent for p in ((n-1,0),(n-1,n-1),(0,0)))
        def emit(f,bit,flags,arc,sheet):
            vp=getclosurevars(bit).nonlocals['vp']
            for u,b in marks.items():
                if u in dom:f.append([bit(*u) if b else -bit(*u)])
            for u in dom:
                if depth(*u)==2:
                    for s,(a,b) in enumerate(DIR):
                        v=u[0]+2*a,u[1]+2*b
                        # Only constrain an outward port if its foot is marked.
                        # The long-arc endpoint is oriented outward too.
                        if v in marks and depth(*v)==0 and marks[v]:
                            f.append([-bit(*u),arc(*u,s)])
                if min(*u,n-1-u[0],n-1-u[1])>=14 and u[0]%3==u[1]%3==2:
                    for delta in (-1,1):
                        v=u[0],u[1]+delta
                        if v in dom:f.append([-bit(*u),-bit(*v)])
            ids=[0]
            for z in range(1,vp.top+1):
                obj=vp.obj(z);t,i,j,*rest=obj
                shared=t=='v' and depth(i,j)>=1 or t=='a' and depth(i,j)>=2 and depth(i+DIR[rest[0]][0],j+DIR[rest[0]][1])>=2
                ids.append(pool.id(obj if shared else (corner,root,obj)))
                if t=='ext':base.append([-ids[z]])
            base.extend([[ids[abs(v)]*(1 if v>0 else -1) for v in c] for c in f.clauses])
        window(n,'rim',1,T,domain=dom,want=False,root_site=root,orient=parent,matching=True,emit_graph=emit)
    for i,j in sorted(dom):
        if depth(i,j)<2:continue
        z=pool.id(('v',i,j))
        if depth(i,j)==2:
            colors[i,j]=len(colors)
        for h in range((2*size).bit_length()):
            v=pool.id(('col',i,j,h))
            if (i,j) in colors:base.append([-z,v if colors[i,j]>>h&1 else -v])
            for x,y in ((i+1,j),(i,j+1)):
                if (x,y) in dom and depth(x,y)>=2:
                    w=pool.id(('col',x,y,h))
                    for g in (z,pool.id(('v',x,y))):base.extend([[-g,-v,w],[-g,v,-w]])
    p=Path(f'target/two_gap_shared_sw_{size}.cnf');base.to_file(str(p));base.clauses.clear()
    with p.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(p),str(p.with_suffix('.drat'))],stdout=fd).returncode
    if rc==20:
        chk=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],check=True,capture_output=True).stdout
        assert b's VERIFIED' in chk;p.with_suffix('.check').write_bytes(chk);print('s VERIFIED')
    else:print('shared corner SAT' if rc==10 else 'UNKNOWN')
if __name__=='__main__':run(*map(int,sys.argv[1:]))
