"""Locate the exact sector-dual deficit on an uncontracted comb-cap witness."""
from .diagonal_score import data,DIR,Q,Counter,product
from .comb_cap_transfer import construct
import sys
def run(n):
    rows=construct(n,4);mark={(i,j) for i,r in enumerate(rows) for j,z in enumerate(r) if z=='#'}
    pos,patch,star,sc,budget=data(n,len(mark));parent={};events=[]
    for u in product(range(n),repeat=2):
        if u in parent:continue
        parent[u]=-1;todo=[u]
        for i,j in todo:
            for d,(a,b) in enumerate(DIR):
                z=i+a,j+b
                if 0<=z[0]<n and 0<=z[1]<n and z not in parent and ((i,j) in mark or z in mark):
                    parent[z]=(d+2)%4;todo.append(z)
    for i,j in product(range(n),repeat=2):
        ds=tuple(s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        z=int((i,j) in mark)+sum(int((i+DIR[d][0],j+DIR[d][1]) in mark)<<(h+1) for h,d in enumerate(ds))
        q=star(pos(i,j,0),ds,len(ds)==2 and (i,j)!=(0,0))[parent[i,j]][z]
        if q:events.append(('s',i,j,q))
        if i<n-2 and j<n-2:
            m=sum(1<<(3*a+b) for a,b in product(range(3),repeat=2) if (i+a,j+b) in mark)
            q=patch(pos(i,j,1))[m]
            if q:events.append(('p',i,j,q))
    assert sum(w for _,_,_,w in events)==budget
    print('side',n,'exact deficit',Q(budget,sc),'positive atoms',len(events))
    print([(s,i,j,str(Q(w,sc))) for s,i,j,w in events])
if __name__=='__main__':run(int(sys.argv[1]))
