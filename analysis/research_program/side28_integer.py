"""Exact physical integer model; D4 event-count splits for upper certificates."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
from .patch_square import relaxation,verify_upper


def physical(n):
    # Binary selected sites; each forced edge chooses a direction. Strict
    # potential growth excludes cycles, and each site has <=1 outgoing arc.
    # Conversely orient every forest towards one root per component.
    vs=range(n*n);out=[[] for _ in vs];rows=[]
    for u in vs:
        for v in (u+1,u+n):
            if v>=n*n or (v==u+1 and v%n==0):continue
            a,b=f'a{u}_{v}',f'a{v}_{u}';out[u].append(a);out[v].append(b)
            for t in (u,v):rows.append(f'{a} + {b} >= s{t};')
            rows.append(f'{a} + {b} <= 1;')
            for x,y,z in ((u,v,a),(v,u,b)):
                rows.append(f'h{x} - h{y} + {n*n} {z} <= {n*n-1};')
    for u in vs:
        rows+=[' + '.join(out[u])+' <= 1;',f'h{u} <= {n*n-1};']
    return '\n'.join(['max: '+' + '.join(f's{u}' for u in vs)+';',
                      ' + '.join(f's{u}' for u in vs)+' >= 289;',*rows,
                      'bin '+','.join([f's{u}' for u in vs]+sum(out,[]))+';'])


def counts(names,n=28):
    from .patch_square import SYM,trans
    cands={}
    for (kind,atom),x in names.items():
        pos,*ev=atom
        if kind=='p':
            orbit={(trans(*pos,n-2,g),SYM[ev[0]][g]) for g in range(8)}
        else:
            f,nb,o=ev
            def turn(d,g):return ((2-d if g&4 else d)+g%4)%4
            orbit={(trans(*pos,n,g),tuple(sorted((turn(d,g),v) for d,v in enumerate(nb))),
                    -1 if o<0 else turn(o,g)) for g in range(8)}
        cands[x]=len(orbit)
    return cands


def run(replay=False,n=28):
    target={28:289,34:420,35:440}[n]
    names,rs,obj=relaxation(n);rows=list(rs)
    # Root the specified corner's component there. Each other component
    # chooses a leaf (or its only vertex); all such roots have degree <=1.
    forbidden=[]
    for (kind,atom),x in names.items():
        if kind!='s':continue
        (i,j),f,nb,out=atom
        if (i,j)==(0,0) or out!=-1:continue
        if sum(v!=9 and (f or v) for v in nb)>1:forbidden.append((x,1))
    rows.append((tuple(forbidden),'=',0))
    cols=list(names.values());ids={x:i for i,x in enumerate(cols)}
    mult=counts(names,n);path=Path(__file__).with_name(f'side{n}_integer_tree.json')
    if not replay:
        import highspy as H
        h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
        h.addVars(len(cols),[0.]*len(cols),[1.]*len(cols))
        h.changeColsCost(len(cols),list(range(len(cols))),[obj[x] for x in cols])
        for c,o,b in rows:
            h.addRow(b if o!='<=' else -H.kHighsInf,b if o!='>=' else H.kHighsInf,
                     len(c),[ids[x] for x,w in c],[w for x,w in c])
        h.setMaximize()
    leaves=[]
    def visit(bounds,node=None):
        if replay:
            if len(node)==1:
                ys={int(i):Q(v) for i,v in node[0]}
            else:x,k,left,right=node;ys=None
        else:
            h.run()
            assert h.getModelStatus()==H.HighsModelStatus.kOptimal
            sol=h.getSolution()
            if h.getObjectiveValue()<target-1e-5:
                ys={i:Q(round(v*10**8),10**8) for i,v in enumerate(sol.row_dual) if abs(v)>1e-9}
            else:
                ys=None
                def priority(x):
                    p=sol.col_value[ids[x]]*mult[x];frac=p%1
                    return (min(frac,1-frac),-ids[x])
                x=max(cols,key=priority);assert priority(x)[0]>1e-6
                k=int(sol.col_value[ids[x]]*mult[x]);left=right=None
        if ys is not None:
            ub,_=verify_upper(rows+bounds,obj,ys)
            assert ub<target,ub
            leaves.append(ub)
            return [list((i,str(q)) for i,q in ys.items())]
        assert x in mult and isinstance(k,int)
        children=[]
        for op,t,child in [('<=',k,left),('>=',k+1,right)]:
            row=(((x,mult[x]),),op,t)
            if not replay:h.addRow(t if op=='>=' else -H.kHighsInf,t if op=='<=' else H.kHighsInf,1,[ids[x]],[mult[x]])
            children.append(visit(bounds+[row],child))
            if not replay:h.deleteRows(1,[h.getNumRow()-1])
        return [x,k,*children]
    tree=visit([],json.loads(path.read_text()) if replay else None)
    print('side',n,'split leaves',len(leaves),'largest exact leaf upper',max(leaves),flush=True)
    if not replay:path.write_text(json.dumps(tree,separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    if '--model' in sys.argv:print(physical(28))
    else:run('--replay' in sys.argv,35 if '--35' in sys.argv else 34 if '--34' in sys.argv else 28)
