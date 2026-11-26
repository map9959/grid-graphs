"""Brute physical comparisons for the two-sided ring and weighted bridge kernels."""
from .dense_bridge_price import data
from .dense_joint_collar import joint,ring,free_ended,dense_cap
from .arbitrary_collar_transfer import engine
from .sparse_component_exchange import graph
from .extend_forest_28 import verify

def brute():
    assert free_ended(103,329,0)==3646 and dense_cap(103)==1147
    n=6;d=1;m=4;rim=[(y+1,x+1) for y,x in ring(4)]
    form=lambda M:[''.join('#' if (i,j) in M else '.' for j in range(n)) for i in range(n)]
    count=0
    for outer,inside in (({(0,0),(0,3),(4,0)},{(2,2)}),
                         ({(0,1),(0,2),(5,3),(1,5)},set()),
                         (set(),{(2,2),(2,3)})):
        rows=form(outer|inside);verify(rows)
        sites,o,k,*_=data(rows,d,1);S=set(o)|set(k)
        B=[['A']*m for _ in range(m)]
        for (i,j),(ps,f) in sites.items():
            B[i][j]=chr(65+9*f+3*sum(g in S and b for g,b in ps)+sum(g in S and not b for g,b in ps))
        cap=sum(engine(('closed-price',1,0,3,1),[''.join(s) for s in B])[0])
        _,eo,ei,_,_=joint(rows,d);bo=bi=z=0
        for mask in range(1<<len(rim)):
            M={p for i,p in enumerate(rim) if mask>>i&1};cost=len(M);count+=1
            if cost>bi:
                try:verify(form(M|inside));bi=cost
                except AssertionError:pass
            if cost>bo:
                try:verify(form(M|outer));bo=cost
                except AssertionError:pass
            if any(f and (y+1,x+1) in M for (y,x),(_,f) in sites.items()):continue
            try:F=graph(form(M),set())
            except AssertionError:continue
            contacts=[]
            for (y,x),(ports,_) in sites.items():
                p=y+1,x+1
                contacts.extend(F.root(p) for g,b in ports if g in S and (b or p in M))
            z=max(z,3*cost-len(contacts)+len(set(contacts)))
        assert (bo,bi,z)==(eo,ei,cap),((bo,bi,z),(eo,ei,cap))
    print(count,'physical candidate rings: inside maximum, outside maximum and closed weighted price all matched')
if __name__=='__main__':brute()
