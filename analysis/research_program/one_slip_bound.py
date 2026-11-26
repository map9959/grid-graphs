"""Length-synchronized dual for one 4-spacing on the upper cut, ordinary lower cut."""
from itertools import product
from .seam_rank_chart import model,verify,recover,Counter,Q,Path,json,sys,solve
from .seam_rank_cost import run as caps

def seam(train):
    def chart(a,b,c):
        sys.argv=['chart','--rank-both','--price=7/10',f'--slip={15+3*a}']
        return model(12+3*c,31+3*(a+b),0)
    A,_,o,ns,keys=chart(0,0,0)
    path=Path(__file__).with_name('one_slip_seam.json')
    if train:
        _,rhs,_,_,kk=chart(5,19,3);mass=dict(zip(kk,rhs))
        _,y,_=solve(A,[mass.get(k,0) if k else 0 for k in keys],o,ns,interior=False)
        raw={i:Q(z) for i,z in enumerate(y) if abs(z)>1e-9}
        Y={i:z.limit_denominator(100000) for i,z in raw.items()}
        if verify(A,o,Y)>0:Y=recover(A,Counter(o),raw)
        assert verify(A,o,Y)<=0;path.write_text(json.dumps({i:str(z) for i,z in Y.items() if z},separators=(',',':'))+'\n')
    Y={int(i):Q(z) for i,z in json.loads(path.read_text()).items()}
    assert verify(A,o,Y)<=0
    sig=lambda mat,kk:{(tuple(sorted(row)),op,key) for (row,op),key in zip(mat,kk)}
    old=sig(A,keys)
    for a,b,c in product(range(2),repeat=3):
        aa,r,o1,ns1,ks=chart(a,b,c);mass=dict(zip(ks,r))
        assert old==sig(aa,ks) and ns1==ns and o1==o
        val=sum(z*mass[keys[i]] for i,z in Y.items() if keys[i])
        assert val==(Q(127,10)+3*c)*(11+a+b)+Q(3-b,10)
    print('one-slip seam: exact three-parameter charge, coefficient -1/10 per eastern triple')

def cap():
    # Test the first sizes at which separated 3-column template blocks
    # can be pumped on both sides of the slip. A dominating vector
    # suffices; equality of optimum paths is not required.
    for z in (30,33):
        n=z+34
        sys.argv=['cap','--free-top','--classes','--prices=10,7','--quiet',f'--slip={z}']
        for i in (12,z+12):
            v,log=caps(n,2,(i,i+3))
            assert 'dominated true shift 30' in log
            assert max(v.values())==27*(n//3+1)+3*(n//3)+4
    print('depth-two slipped cap: both insertions dominated at shift 30')
if __name__=='__main__':
    train='--train' in sys.argv;seam(train);cap()
