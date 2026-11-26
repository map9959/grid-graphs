"""Recover a primal on a union of joined-word corridors from independent prices."""
from .fourteen_bound import *
from .side28_score import solve

def run():
    from .all_pinned_sites import primal
    ns,A,b,obj,l=model(15);start,fn,_=pathspec(15)
    _,aa=json.loads(fn.read_text());prior={(j,(a,v,tuple(p)),c) for j,(a,v),p,c,q in aa}
    for tag in ('deepqp','main','elastic','mixqp','balanced','quadratic','graphqp','slice','ref lect'.replace(' ',''),'box','alt','master','residual','aspire'):
        pp=Path('target/fifteen_'+tag+'.json')
        if not pp.exists():continue
        _,cc,B,*_=json.loads(pp.read_text());c={tuple(k):q for k,q in cc}
        res=oracle(c,B,'witness',15)
        if res:
            prior.update(res[2]);prior.update(reflect_paths(res[2],15))
    print('union legal arc support',len(prior),flush=True)
    flow=defaultdict(list);links=defaultdict(list)
    for i,(j,s,c) in enumerate(sorted(prior)):
        a,v,p=s;q=move(v,p,c);assert q is not None
        x=f'z{i}';ns['arc',j,s,c]=x;flow[j,s].append((x,1))
        if j<108:flow[j+1,(v,c,q)].append((x,-1))
        if j>=2:
            for r,m in enumerate(masks(a,v,c,15)):links[fine_axis(j-2,15),r,m].append((x,1))
    for k,x in l.items():A.append((links[k]+[(x,-1)],'='));b.append(0)
    for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,start)))
    val,_,v=solve(A,b,obj,ns,interior=True);print('joint corridor LP',val,flush=True)
    if val>4091.334:
        sub={k:x for k,x in ns.items() if v[x]>1e-8};support=set(sub.values())
        thin=[([(x,w) for x,w in cs if x in support],op) for cs,op in A];_,_,v=solve(thin,b,obj,sub);save(primal(thin,b,v),ns,fn.stem);replay(15)

if __name__=='__main__':run()
