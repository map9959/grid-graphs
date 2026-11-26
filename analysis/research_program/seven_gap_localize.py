"""Flat clusters and corner charges with seven missing perimeter edges."""
from .sector_gap_cover import data,generate,gaps,verify,product
from pysat.pb import PBEnc
from pysat.formula import CNF

def test(n):
    k=n//3;t=3*k*k+(16*k-7)//3;tables=data(n,t)
    def local(D,events,limit,tag):
        cost={};f,X=generate(n,t,D,False,tables,bill=cost)
        for es,z in events:gaps(f,X,es,n,z)
        if limit<60:f.extend(PBEnc.atmost(lits=list(cost),weights=list(cost.values()),bound=limit,top_id=f.nv,encoding=8).clauses)
        return verify(f,f'seven{n}_{tag}')
    e=lambda j:((0,j),(0,j+1))
    # In an entirely homogeneous part of a side. Use the same halo for
    # every placement. Separate blocks with nonoverlapping physical stars.
    flat=local(set(product(range(12),range(35,51))),[([e(j) for j in range(40,43)],1)],51,'flat52')
    near=local(set(product(range(26),repeat=2)),[([z for j in range(24) for z in (e(j),((j,0),(j+1,0)))],2)],8,'near9')
    outer=local(set(product(range(12),range(18,42))),[([e(j) for j in range(24,34)],1)],8,'shoulder9')
    # Normalize the *first* flat edge in a cluster to one of three residues.
    clusters=[]
    for j in range(36,39):
        clusters.append(local(set(product(range(12),range(j-6,j+25))),
              [([e(j)],1),([e(x) for x in range(j+1,j+18)],2)],60,f'cluster{j%3}'))
    assert flat and near and outer and all(clusters)
    pos=tables[0]
    def same(i,c,x):
        return all(pos(i,c,tag)==pos(i,x,tag) for tag in (0,1))
    for j in range(34,n-1-34):
        anchor=40+(j-40)%3
        assert all(same(i,c,c+j-anchor) for i,c in product(range(12),range(35,51)))
    for j in range(34,(n-1)//2+1):
        anchor=36+(j-36)%3
        assert all(same(i,c,c+j-anchor) for i,c in product(range(12),range(anchor-6,anchor+25)))
    print(n,'seven gaps: no edge at distance >=52 from both corners',flush=True)
if __name__=='__main__':
    import sys
    test(int(sys.argv[1]))
