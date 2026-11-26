"""Check whether the refined model still meets the previous dual on its tight face."""
from .repeating_patch_dual import polynomial,filename,Q,json,Path
from .strip_period_primal import recover
from collections import Counter


def run(mode='pinned',replay=False):
    n0,names,A,b,obj=polynomial(2,3,1,mode)
    path=Path(__file__).with_name(f'face_r1_{mode}.json')
    if replay:
        f={x:tuple(map(Q,v)) for x,v in json.loads(path.read_text()).items()}
    else:
        _,_,B,_,_=polynomial(2,3,1,'pinned')
        _,pairs=json.loads(filename(2,3,1,'pinned').read_text())
        rc=Counter(obj)
        for i,y in pairs:
            for x,w in B[i][0]:rc[x]-=Q(y)*w
        assert max(rc.values())<=0
        AA=[];bb=[]
        for (row,op),v in zip(A,b):
            cs=tuple((x,w) for x,w in row if rc[x]==0)
            if cs:AA.append((cs,op));bb.append(v)
            else:assert v==(0,0,0)
        target={x:w for x,w in obj.items() if rc[x]==0}
        print('tight variables',sum(rc[x]==0 for x in names.values()),flush=True)
        f=recover(AA,bb,target,15,lambda v,j:v[0]+v[1]*j+v[2]*j*(j-1)//2)
    def lhs(row):return tuple(sum(w*f.get(x,(0,0,0))[i] for x,w in row) for i in range(3))
    constraints=list(f.values())
    for (row,op),v in zip(A,b):
        s=tuple(x-y for x,y in zip(lhs(row),v))
        if op=='=':assert not any(s)
        else:constraints.append(s if op=='>=' else tuple(-x for x in s))
    score=lhs(obj.items())
    assert score==(Q(421,3),45,6)
    for j in range(100):
        if all(a+j*b+j*(j-1)//2*c>=0 and b+j*c>=0 and c>=0 for a,b,c in constraints):break
    else:raise ValueError('no certified tail')
    print(mode,'rows',len(A),'score Newton coefficients',score,'valid for n >=',n0+3*j)
    if not replay:path.write_text(json.dumps({x:list(map(str,v)) for x,v in f.items()},separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run(sys.argv[1],'--replay' in sys.argv)
