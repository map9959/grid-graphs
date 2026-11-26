"""Rebuild the three integer-count leaf proposals at side 43 (single LP worker).

An orbit of eight sites contains at most seven marks or exactly eight.
The second split is needed only on the first branch. No D4 symmetry
is assumed for the selected set. The independent Lean checker sums
physical scalar prices; it does not use this solver's optimality claim.
"""
from collections import Counter
from .patch_square import relaxation, trans
from .side28_score import solve
from .export_finite_one_stencil import proposal, DEST


def run():
    n = 43
    ns,rows,obj = relaxation(n)
    marg = {(6,9):Counter(),(9,15):Counter()}
    for (kind,(p,*w)),x in ns.items():
        if kind!='s' or not w[0] or p not in marg:
            continue
        _,nb,o = w
        def image(g):
            def turn(d):return ((6-d if g>=4 else d)+g)%4
            return trans(*p,n,g),tuple(sorted((turn(d),v) for d,v in enumerate(nb))),turn(o) if o>=0 else -1
        marg[p][x] = len({image(g) for g in range(8)})
    defs = ['import GridGraphs.FiniteOne.Splits', '', 'namespace GridGraphs.FiniteOne.Cuts43']
    for name,path in [('LL',[((6,9),'<=',7),((9,15),'<=',7)]),
                      ('LH',[((6,9),'<=',7),((9,15),'>=',8)]),('H',[((6,9),'>=',8)])]:
        A = [(cs,o) for cs,o,_ in rows]+[(list(marg[p].items()),op) for p,op,_ in path]
        b = [v for _,_,v in rows]+[v for _,_,v in path]
        opt,y,_ = solve(A,b,obj,ns,interior='cross')
        assert opt < 661
        ys = [(i,round(1e6*z)) for i,z in enumerate(y) if abs(z)>5e-7]
        proposal(43,name,ys)
        weights = [8*round(round(1e6*z)/10) for z in y[len(rows):]]
        label = {'LL':'ll','LH':'lh','H':'hi'}[name]
        terms = [f'⟨({r},{c}),{w},{bound}⟩' for ((r,c),_,bound),w in zip(path,weights,strict=True)]
        defs.append(f'def {label} : List Cut := ['+','.join(terms)+']')
    (DEST.parent/'Cuts43.lean').write_text('\n'.join(defs+['end GridGraphs.FiniteOne.Cuts43','']))


if __name__=='__main__':
    run()
