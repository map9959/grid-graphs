"""Read both variable budgets from the same physical side-103 mark board."""
from itertools import product
from collections import Counter
from .rank44_faces import canon,table,test,labels
from .skeleton_exit_chart import DIR,trans
from .skeleton_floor_words import priced
from .rank48_word_audit import compare
from .skeleton_cross_rank import DSU,graphs,split,physical
from .comb_cap_transfer import construct
from .cross_minor_refill import refill,shell_control


def check(rows,chart,allow_pure=False):
    n=len(rows);f,j,a,x=physical(rows)
    score=sum(w.count('#') for w in rows)
    if allow_pure:x=3605+f-a-j-score
    assert x is not None
    sk=DSU(n*n)
    for u,v in graphs(split(rows)):assert sk.join(u,v)
    joins=0
    for i,k in product(range(0,n-1,3),repeat=2):
        q=canon(sk.root((i+y)*n+k+z) for y,z in product((0,3),repeat=2))
        m=sum((rows[i+y][k+z]=='#')<<(4*y+z) for y,z in product(range(4),repeat=2))
        joins+=table(4,3)[m,q]
    axes=(rows,[''.join(s) for s in zip(*rows)])
    T=sum(lines[::3].count('#..'*34+'#') for lines in axes)
    d=[sum(compare(w) or 0 for w in lines[::3]) for lines in axes]
    assert joins<=j and max(d)<=x+(T if allow_pure else 0) and x==3605+f-a-j-score
    print('M,F,C',score,f,a+j,'face ranks / j',joins,j,'axis debits / X',*d,x)
    # Rotate the physical input, including the same full-forest
    # orientation, and accumulate eight times each canonical frequency.
    ns,A,b,M,bo,F,sink,ex=chart
    adj=[[] for _ in range(n*n)]
    for u,v in graphs(rows):adj[u].append(v);adj[v].append(u)
    par={}
    for root in [u*n+v for u,v in product(range(0,n,3),repeat=2)]+list(range(n*n)):
        if root in par:continue
        todo=[root];par[root]=-1
        for u in todo:
            for v in adj[u]:
                if v not in par:par[v]=u;todo.append(v)
    cnt=Counter()
    def add(key):
        if key in ns:cnt[ns[key]]+=1
    def loc(i,k,t):
        N=n-2*t;clip=lambda z:max(-9,min(9,z))
        return (*labels(i,k,N,8-t),clip(i-k),clip(i+k+1-N))
    for g in range(8):
        r=[[0]*n for _ in range(n)];D={};classes={}
        for u,v in product(range(n),repeat=2):
            i,k=trans(u,v,n,g);r[i][k]=int(rows[u][v]=='#')
            if u%3==v%3==0:classes[i,k]=sk.root(u*n+v)
            parent=par[u*n+v];o=-1
            if parent>=0:
                y,z=trans(*divmod(parent,n),n,g);o=DIR.index((y-i,z-k))
            D[i,k]=o
        for i,k in product(range(n),repeat=2):
            nb=tuple(r[i+y][k+z] if 0<=i+y<n and 0<=k+z<n else 9 for y,z in DIR)
            add(('s',(loc(i,k,0),r[i][k],nb,D[i,k])))
            if i<n-2 and k<n-2:
                m=sum(r[i+y][k+z]<<(3*y+z) for y,z in product(range(3),repeat=2))
                add(('p',(loc(i,k,1),m)))
            if i%3==k%3==0 and i<n-3 and k<n-3:
                q=canon(classes[i+y,k+z] for y,z in product((0,3),repeat=2))
                m=sum(r[i+y][k+z]<<(4*y+z) for y,z in product(range(4),repeat=2))
                add(('rankFace',(labels(i,k,n-3,2),m,q)))
        for i in range(0,n,3):
            st=('pre' if any(r[i][j] for j in range(n) if j%3) else 'p0',None,0)
            prev=None
            for k in range(0,n,3):
                y,p=labels(i,k,n,8);letter=tuple(r[i][z] if 0<=z<n else 0 for z in (k-1,k,k+1))
                u,_=priced(st,letter,k==n-1,allow_zero=allow_pure)
                cnt[ns['floorLine',y,(prev,p,st,u)]]+=1
                prev,st=p,u
    dot=lambda row:sum(w*cnt[v] for v,w in row)
    aux={v for key,v in ns.items() if key[0]=='complete'}
    for (row,_),rhs in zip(A,b):
        for v,w in row:
            if v in aux and w==-1:cnt[v]=max(0,dot(row)-8*rhs)
    assert [dot(c.items()) for c in (M,F,sink,ex)]==[8*t for t in (score,f,a,j)]
    assert not any(cnt[v] for v in bo)
    if allow_pure:
        total=sum(2*cnt[x] for k,x in ns.items() if k[0]=='floorLine' and
                  k[2][1]==labels(0,102,103,8)[1] and k[2][3][0]=='p0')
        assert total==8*T
    failed=[]
    for index,((row,op),rhs) in enumerate(zip(A,b)):
        gap=dot(row)-8*rhs
        if not {'=':gap==0,'<=':gap<=0,'>=':gap>=0}[op]:failed.append((index,gap))
    print('violated rows',failed[:20],len(failed))
    assert not failed


if __name__=='__main__':
    comb=construct(103,4);chart=test(weighted=True,free=True,cuts=False)
    chart[1].append((list(chart[6].items()),'>='));chart[2].append(1)
    for board in (comb,shell_control(103)):
        check(refill(['.'+r[:-1] for r in board])[0],chart)
    check(refill([5*('#' if i%3==1 else '.')+'.'+r[6:] for i,r in enumerate(comb)])[0],chart)
