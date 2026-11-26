"""Solver-free side-28 lift separation and replay on the repeating coefficient rows."""
from collections import Counter
from .patch_square import MASKS,SYM,trans
from .repeating_patch_dual import polynomial,Q,Path,json


def run():
    n=28;S=n-2
    f={x:tuple(map(Q,v)) for x,v in json.loads(Path(__file__).with_name('face_r1_pinned.json').read_text()).items()}
    n0,names,A,b,obj=polynomial(2,3,1,'pinned')
    assert n0==19
    val=lambda v:v[0]+3*v[1]+3*v[2]
    z={x:val(v) for x,v in f.items()}
    assert min(z.values())>=0
    for (row,op),v in zip(A,b):
        s=sum(w*z.get(x,0) for x,w in row)-val(v)
        assert {'=':s==0,'>=':s>=0,'<=':s<=0}[op]
    score=sum(w*z.get(x,0) for x,w in obj.items())
    print('verified pinned rows',len(A),'score',score)
    def ax(t):return t if t<5 else 13-S+t if t>=S-5 else 5+(t-5)%3
    def mass(i,j,m):
        pos=[tuple(map(ax,trans(i,j,S,g))) for g in range(8)]
        return z.get(names['p',min(zip(pos,SYM[m]))],0)
    for ii in ([0],list(range(4,S-4,3)),list(range(5,S-4,3))):
        # Sum over whole fine types, never assume equal probabilities per site.
        types=Counter(map(ax,ii));assert all(types[t]==sum(ax(i)==t for i in range(S)) for t in types)
        result=[]
        for j,start in [(3,1),(4,0)]:
            assert sum(ax(v)==ax(j) for v in range(S))==1
            tot=Q(0)
            for t in types:
                i=next(i for i in ii if ax(i)==t)
                assert sum(mass(i,j,m) for m in MASKS)==types[t]
                tot+=sum(mass(i,j,m) for m in MASKS if all(not m&(1<<(3*r+c)) for r in range(3) for c in (start,start+1)))
            result.append(tot)
        assert result[0]!=result[1]
        print('strip origins',ii,'all-zero overlap totals',*result)
    _,ns,C,_,_=polynomial(2,3,1,'r28')
    assert ns==names
    setA=set(A)
    added=[row for row in C if row not in setA]
    assert len(added)==3
    for row,op in added:
        assert op=='='
        rr=tuple(sum(w*f.get(x,(0,0,0))[i] for x,w in row) for i in range(3))
        assert val(rr)!=0
        print('repeating row residual in Newton basis:',*[str(q) for q in rr])


if __name__=='__main__':run()
