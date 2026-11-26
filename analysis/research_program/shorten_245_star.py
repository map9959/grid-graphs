"""Test rectangular 42-step surgery on a one-gap board, with four seven-row ports."""
from itertools import combinations,product
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess,sys
from .defect_window import table,window,DIR
from .depth_two_203_ledger import boundary

H=7
def nb(u,d):
    return u[0]+DIR[d][0],u[1]+DIR[d][1]

def plan(d):
    # Two nonoverlapping possible longitudinal strips in the large square.
    # A 78-step strip will be shortened to 36. Leave a two-column halo.
    x=144 if d<142 else 60
    assert d<x-1 or d>x+79
    return 102,x,d if d<x else d-42

def domain(n,y,x,wide):
    # narrow: ten columns/rows cut out, enough to duplicate the
    # periodic wire. wide: the whole standard 36/78-step pump and halo.
    def slot(c):
        return range(c-1,c+38+n-203) if wide else range(c+14,c+24+n-203)
    I,J=slot(y),slot(x)
    return {(i,j) for i,j in product(range(n),repeat=2)
            if min(i,j,n-1-i,n-1-j)<H or (i not in I and j not in J)}

def audit(n,A,X,out,star,w,tab,frame_path=None,root_site=(0,0)):
    marks,path=frame_path or boundary(n,w)
    assert all((p in X)==bool(v) for p,v in marks.items() if p in A)
    assert all(out.get(p,-1)==(d if d>=0 and nb(p,d) in A else -1) for p,d in path.items() if p in A)
    T,P,S=tab;parent={};count=0
    def root(u):
        while u in parent:
            if parent[u] in parent:parent[u]=parent[parent[u]]
            u=parent[u]
        return u
    charges=[]
    for p in A:
        i,j=p;ds=tuple(d for d in range(4) if min(nb(p,d))>=0 and max(nb(p,d))<n)
        if all(nb(p,d) in A for d in ds):
            m=int(p in X)+sum((nb(p,d) in X)<<(1+k) for k,d in enumerate(ds))
            q=S(T(0,i,j),ds,out.get(p,-1),p==root_site,len(ds)==2)[m]
            assert q==72*(p==star),(p,q)
            if q:charges.append(p)
        sq=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
        if all(u in A for u in sq):assert not P(T(1,*p))[sum((u in X)<<k for k,u in enumerate(sq))]
        for d in (0,1):
            v=nb(p,d)
            if v not in A:continue
            forced=p in X or v in X
            assert int(out.get(p)==d)+int(out.get(v)==d+2)==int(forced)
            if forced:
                a,b=root(p),root(v);assert a!=b;parent[a]=b;count+=1
    assert charges==([] if star is None else [star])
    return len(A),count,{p:root(p) for p in A}

def test(d,west=False,wide=False):
    y,x,s=plan(d)
    if west:y,x=x,y
    site=(s,2) if west else (2,s);n=203
    A=domain(n,y,x,wide);tab=table(n);tab2=table(245)
    w=(1,1,1);frame,path=boundary(n,w)
    def emit(f,bit,flags,arc,sheet):
        assert set(flags)=={('s',*site)}
        for p,b in frame.items():
            if p in A:f.append([bit(*p) if b else -bit(*p)])
        for p in A:
            ds=[k for k in range(4) if nb(p,k) in A]
            if all(k in ds or min(nb(p,k))<0 or max(nb(p,k))>=n for k in range(4)):continue
            for a,b in combinations(ds,2):f.append([-arc(*p,a),-arc(*p,b)])
            for k in ds:
                v=nb(p,k);a=arc(*p,k);b=arc(*v,(k+2)%4)
                f.extend([[-a,-b],[-bit(*p),a,b],[-bit(*v),a,b],[-a,bit(*p),bit(*v)],[-b,bit(*p),bit(*v)]])
                for h in range(4):
                    if nb(v,h) not in A or h==(k+2)%4:continue
                    c=sheet(*v)*(-1 if abs(h-k)==3 else 1)
                    f.extend([[-a,-arc(*v,h),-sheet(*p),c],[-a,-arc(*v,h),sheet(*p),-c]])
        # A sufficient, not necessary, seam condition for a constructive
        # countermodel: repeat a directed three-column word at each cut.
        for axis,start in ((0,y),(1,x)):
            for r in [*range(H),*range(n-H,n)]:
                for j in range(start+15,start+20):
                    u=(j,r) if axis==0 else (r,j);v=(j+3,r) if axis==0 else (r,j+3)
                    for a,b in [(bit(*u),bit(*v))]+[(arc(*u,k),arc(*v,k)) for k in range(4) if nb(u,k) in A]:
                        f.extend([[-a,b],[a,-b]])
        with TemporaryDirectory(dir='target') as tmp:
            cnf=Path(tmp)/'query.cnf';log=Path(tmp)/'model'
            f.to_file(str(cnf));f.clauses.clear()
            with log.open('w') as o:st=subprocess.run(['target/cadical/build/cadical','-t','60',str(cnf)],stdout=o).returncode
            if st!=10:
                print('stationary-wire test, NOT a witness exclusion:',st,d,west,wide,flush=True);return
            model={int(z) for l in log.read_text().splitlines() if l.startswith('v ') for z in l[2:].split()}
        X={p for p in A if bit(*p) in model};out={}
        for p in A:
            dirs=[k for k in range(4) if nb(p,k) in A and arc(*p,k) in model]
            assert len(dirs)<=1
            if dirs:out[p]=dirs[0]
        v,e,cc=audit(n,A,X,out,site,w,tab)
        # Repeat a three-column/row word fourteen times. In the overlap
        # of the two cut bands there are no sites. All untouched vertices
        # embed in the enlarged board; compare their ENTIRE partition.
        def proj(z,c):return z if z<=c else c-2+(z-c-1)%3 if z<=c+42 else z-42
        def lift(z,c):return z if z<=c else z+42
        cy,cx=y+18,x+18
        B=domain(245,y,x,wide);Y=set();o2={}
        for i,j in B:
            u=proj(i,cy),proj(j,cx);assert u in A
            if u in X:Y.add((i,j))
            if u in out:o2[i,j]=out[u]
        star=(d,2) if west else (2,d)
        vv,ee,cc2=audit(245,B,Y,o2,star,w,tab2)
        corr={(a,cc2[lift(i,cy),lift(j,cx)]) for (i,j),a in cc.items()}
        assert len(corr)==len(set(cc.values()))==len({b for a,b in corr})
        print(f'{245} -> {203}',star,'->',site,'frame 0111',('wide' if wide else 'thin'),
              'sites/forced edges',(vv,ee),'->',(v,e),'preserved components',len(corr),flush=True)
    window(n,'rim',H,tab,domain=A,orient=path,defects={('s',*site)},emit_graph=emit)

if __name__=='__main__':
    remain=[d for d in range(5,240,3) if d%6==5 or d>194]
    for d in remain:
        y,x,s=plan(d)
        assert 5<=s<=197 and s%6==d%6
    print('phase-compatible clean cuts:',len(remain),'remaining distances per arm')
    test(int(sys.argv[1]),'--west' in sys.argv,'--wide' in sys.argv)
