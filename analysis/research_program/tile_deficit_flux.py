"""Price the deficit of a bulk tile by flux through its four tile edges."""
from fractions import Fraction
from itertools import product
from .tile_flux_closure import ports,closure,edges,enumerate_blocks,table

def price(B):
    import highspy as hp
    p=hp.Highs();p.setOptionValue('output_flag',False);p.setOptionValue('threads',1)
    es=sorted({e for b in B for e in edges(b)});v=p.addVariables(len(es),lb=-hp.kHighsInf)
    ids=dict(zip(es,v));r=p.addVariable(lb=0)
    for z in v:p.addConstr(z<=r);p.addConstr(z>=-r)
    for b in B:
        t,q,s,l=edges(b);p.addConstr(ids[t]+ids[q]-ids[s]-ids[l]>=3-b[0].bit_count())
    p.minimize(r)
    if p.getModelStatus()!=hp.HighsModelStatus.kOptimal:
        print('no perimeter-only upper pricing on this alphabet');return
    sol={e:Fraction(p.val(z)).limit_denominator(10000) for e,z in ids.items()}
    def valid():
        return all(sol[t]+sol[q]-sol[s]-sol[l]>=3-b[0].bit_count() for b in B for t,q,s,l in [edges(b)])
    if not valid():
        # A finer exact representation of the same numerical basis can
        # have very large denominators. Seek half-integral prices instead.
        for z in v:p.changeColIntegrality(int(z),hp.HighsVarType.kInteger)
        for i,b in enumerate(B):p.changeRowBounds(2*len(es)+i,2*(3-b[0].bit_count()),hp.kHighsInf)
        p.run()
        if p.getModelStatus()!=hp.HighsModelStatus.kOptimal:return
        sol={e:Fraction(round(p.val(z)),2) for e,z in ids.items()}
    assert valid()
    print('exactly feasible deficit prices; max absolute',max(map(abs,sol.values())))
    return sol
if __name__=='__main__':
    bs=enumerate_blocks(0);T=table(119);pp={(d,f):ports(T,d,f,False) for d,f in product(range(2),repeat=2)}
    for axis in (0,1,2):
        B=closure([b for b in bs if not axis or all(not(m&16 and m&(40 if axis==1 else 130)) for m in b)],pp,(0,0))
        print('axis',axis,'plaquettes',len(B));price(B)
