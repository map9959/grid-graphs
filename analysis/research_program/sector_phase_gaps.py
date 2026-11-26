"""How many nonstripe words can separate two pure phases on a diagonal arm?"""
from itertools import combinations,product
from .square_current import DIR

def test(R=10,limit=2):
    origins={(i,j) for i,j in product(range(R),repeat=2) if abs(i-j)<=1}
    cells={p:{(p[0]+a,p[1]+b) for a,b in product(range(3),repeat=2)} for p in origins}
    hits=set();count=0;axis=set()
    for d in range(1,limit+1):
        for gone in combinations(sorted(origins),d):
            rem=origins-set(gone);groups=[]
            while rem:
                a=rem.pop();q=[a]
                for i,j in q:
                    for di,dj in DIR:
                        t=i+di,j+dj
                        if t in rem:rem.remove(t);q.append(t)
                groups.append(q)
            if len(groups)==1:continue
            vs=[set.union(*(cells[p] for p in g)) for g in groups]
            for ph in product(range(6),repeat=len(vs)):
                if len(set(ph))==1:continue
                marks={p for v,k in zip(vs,ph) for p in v if p[k//3]%3==k%3}
                if any(any((p[k//3]%3==k%3)!=(p in marks) for p in v) for k,v in zip(ph,vs)):continue
                if any((i+1,j+h) in marks for i,j in marks for h in (-1,1)):continue
                count+=1;hits.add((d,tuple(sorted(len(g) for g in groups))))
                if len({v//3 for v in ph})>1:axis.add(d)
                if count<=2:print('example',gone,ph,groups)
    print('width-three arm',R,'steps; compatible nonuniform components',count,sorted(hits),'axis changes at costs',sorted(axis))
    if R==5 and limit==2:assert count==0
if __name__=='__main__':
    import sys
    test(*map(int,sys.argv[1:]))
