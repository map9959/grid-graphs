"""Intersect the same physical patch event in four rooted parity quotients."""
from itertools import product
from .odd_frames import prep,evaluate,rotate,trans,SYM

def bucket(x,S):
    return x if x<5 else 16+x-S if x>=S-5 else 5+(x-5)%6

def candidates(n):
    S=n-2
    for i,j in product(range(4,S-4,3),repeat=2):
        if i<=22 and j<=22:continue
        yield i,j

def run():
    data=prep(); common=[None,None];counts=[]
    for tail in product((1,3),repeat=3):
        w=(0,*tail)
        # g rotates the physical board until the tested corner is NW.
        A=[list(map(set,evaluate(data,rotate(w,g)))) for g in range(4)]
        for p,n in enumerate((119,161)):
            S=n-2;res=set();first=set()
            for i,j in candidates(n):
                keys=[]
                for g in range(4):
                    u,v=trans(i,j,S,g);keys.append((1,bucket(u,S),bucket(v,S)))
                for k,m in A[0][p]:
                    if k!=keys[0]:continue
                    first.add((i,j,m))
                    if all((keys[g],SYM[m][g]) in A[g][p] for g in range(1,4)):
                        res.add((i,j,m))
            masks=sorted({m for i,j,m in res})
            expected={(i,j,m) for i,j in candidates(n) if (i+j)%2
                      for m in (1,4,64,256)}
            assert res==first==expected
            print(''.join(map(str,w)),n,'NW -> four',len(first),'->',len(res),
                  'sites',len({(i,j) for i,j,m in res}),'masks',masks,flush=True)
            types={(bucket(i,S),bucket(j,S),m) for i,j,m in res}
            # Check the underlying finite type identity too, *without*
            # discarding any origin in the open-corner box. On growth by
            # 84, bulk multiplicities change, but these tuples do not.
            def at(i,j):
                keys=[(1,*(bucket(x,S) for x in trans(i,j,S,g))) for g in range(4)]
                before={m for k,m in A[0][p] if k==keys[0]}
                return before,{m for m in before if all((keys[g],SYM[m][g]) in A[g][p] for g in range(1,4))}
            sample={}
            for i in range(4,S-4,3):
                for j in range(4,S-4,3):sample[bucket(i,S),bucket(j,S)]=(i,j)
            assert len(sample)==16
            for i,j in sample.values():
                before,after=at(i,j)
                assert before==after==({1,4,64,256} if (i+j)%2 else set())
            if common[p] is None:common[p]=types
            counts.append((w,p,types==common[p]))
    print('same physical bucket/mask lists for every frame and parity:',
          all(ok for _,_,ok in counts) and common[0]==common[1],flush=True)
    for a,b in sorted({(a,b) for a,b,m in common[0]}):
        print('bucket',a,b,sorted(m for x,y,m in common[0] if (x,y)==(a,b)))
if __name__=='__main__':run()
