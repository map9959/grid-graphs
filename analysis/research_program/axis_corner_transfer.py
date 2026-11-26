"""Four filled corners, a pumpable rim, and bulk tile tracks across the gaps."""
from itertools import product
from pathlib import Path
from hashlib import file_digest
import subprocess,sys
from .odd_frames import frame,rotate
from .defect_window import table,window
from .saturated_tile_phase import relation,ROW,COL
from .tight_corner_sat import cover

def bulk_graph(tables,di,dj):
    x=40;G=[]
    def emit(f,bit,flags):
        G.append(relation(f,[[bit(x+i+k*di*3,x+j+k*dj*3) for i,j in product(range(3),repeat=2)] for k in (0,1)]))
    window(119,'rim',1,tables,want=False,turn_domain=set(),emit=emit,
           domain=set(product(range(34,49+di*3),range(34,49+dj*3))))
    g=G[0];p=g
    for _ in range(3):p={a:set().union(*(g.get(b,()) for b in bs)) for a,bs in p.items()}
    assert p=={a:set().union(*(g.get(b,()) for b in bs)) for a,bs in p.items()}
    assert sum(map(len,p.values()))==586
    return p

def test(W,seconds,code='all'):
    n=119;assert 20<=W<=39
    dep=lambda x:min(x,n-1-x)
    dom={(i,j) for i,j in product(range(n),repeat=2) if min(dep(i),dep(j))<7 or max(dep(i),dep(j))<W}
    tab=table(n);graphs=[bulk_graph(tab,0,1),bulk_graph(tab,1,0)]
    def emit(f,bit,flags):
        inds=[i for i in range(14,n-14,3) if dep(i)+1<W];L=[i for i in inds if i<n//2]
        assert inds==L+[n-1-i for i in reversed(L)] and (n-1-2*L[-1])//3>=4
        top=f.nv
        def fresh():
            nonlocal top
            top+=1;return top
        axis=fresh()
        def restrict(vs,words,guard):
            for mask,v in cover(tuple(m not in words for m in range(512))):
                f.append(guard+[(-z if v>>k&1 else z) for k,z in enumerate(vs) if mask>>k&1])
        def bits(i,j):return [bit(i+a,j+b) for a,b in product((-1,0,1),repeat=2)]
        for vert,g,allowed,nb in zip((False,True),graphs,(ROW,COL),((1,7),(3,5))):
            sets={}
            for u,v in g.items():sets.setdefault(tuple(sorted(v)),set()).add(u)
            for i in inds:
                track=[bits(j,i) if vert else bits(i,j) for j in inds]
                flag=fresh();f.append([-flag,-axis if vert else axis])
                for tile in track:
                    for k in nb:f.append([-tile[k],-tile[4],flag])
                    restrict(tile,allowed,[-flag])
                left,right=track[len(L)-1:len(L)+1];sels=[]
                for rightset,leftset in sets.items():
                    z=fresh();sels.append(z)
                    restrict(left,leftset,[-z]);restrict(right,rightset,[-z])
                f.append(sels)
        words=['0011','0013','0031','0033','0112','0132','0211','0213','0231','0312'] if code=='all' else [code]
        ds=[]
        for word in words:
            z=fresh();ds.append(z)
            for u,v in sorted(frame(n,tuple(map(int,word))).items()):f.append([-z,bit(*u)*(1 if v else -1)])
        f.append(ds)
        stem=Path(f'target/axis_corner_transfer_{W}_{code}');cnf=stem.with_suffix('.cnf');proof=stem.with_suffix('.drat')
        f.to_file(str(cnf))
        with cnf.open('rb') as inp:print('width',W,'vertices',len(dom),'frames',words,'sha256',file_digest(inp,'sha256').hexdigest(),flush=True)
        with stem.with_suffix('.log').open('w') as log:
            st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(proof)],stdout=log).returncode
        if st==20:
            out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out);print('s VERIFIED')
        else:print('corner-track relaxation SAT' if st==10 else 'UNKNOWN')
    window(n,'rim',7,tab,domain=dom,exit_only=True,emit=emit)
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]),*sys.argv[3:])
