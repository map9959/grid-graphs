"""All-size Farkas checks on integer charge profiles for sides 35+42t."""
from .charge_profiles import model,profiles,Counter,Q
from pathlib import Path
import json
save=Path(__file__).with_name('odd_charge_certificates.json')

def setup():
    ns,rr,obj,cell,q,mu,ban=model();xs=list(ns.values());ix={x:i for i,x in enumerate(xs)}
    W=sorted({v for x,v in q.items() if x not in ban and 0<v<=72})
    A=[];b=[];normal={}
    for cs,op,r in rr:
        rhs=(r,0,0)
        if op=='=' and r>0:
            pt,d,p=cell[cs[0][0]]
            vals=[]
            for n in (35,77,119):
                S=n-2*p
                def count(z):
                    if d<=z<d+6:return (S-2*d+5-(z-d))//6
                    return 1
                vals.append(count(pt[0])*count(pt[1]))
            a,v,e=vals;rhs=a,v-a,e-2*v+a
            for x,w in cs:normal[x]=len(A),w
        A.append((cs,op));b.append(rhs)
    wi={}
    for w in W:
        wi[w]=len(A);A.append(([(x,mu[x]) for x in xs if q[x]==w and x not in ban],'='));b.append((0,0,0))
    A.append((list(obj.items()),'='));b.append((440,1608,1176)) # U(11+14t), Newton coefficients
    for t in range(3):
        k=11+14*t;assert 440+1608*t+1176*t*(t-1)//2==3*k*k+7*k-(k-5)//7
    return xs,A,b,wi,normal,q,ban

def run(replay):
    xs,A,b0,wi,norm,charge,ban=setup()
    bank=json.loads(save.read_text()) if save.exists() else {}
    passed=[]
    for pr in profiles(sorted(wi)):
        key=','.join(map(str,pr));allowed=set(xs)-ban-{x for x in xs if charge[x] and charge[x] not in pr}
        b=b0.copy()
        for w,i in wi.items():b[i]=(pr.count(w),0,0)
        if replay and key not in bank:continue
        if key in bank:y={int(i):Q(z) for i,z in bank[key].items()}
        else:
            import highspy as H
            h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
            ids={x:i for i,x in enumerate(sorted(allowed))};N=len(ids)
            h.addVars(N+2,[0.]*(N+2),[H.kHighsInf]*(N+2))
            for (cs,op),(a,d,e) in zip(A,b):
                row=[(ids[x],w) for x,w in cs if x in ids]
                if d:row.append((N,-d))
                if e:row.append((N+1,-e))
                h.addRow(a if op!='<=' else -H.kHighsInf,a if op!='>=' else H.kHighsInf,
                         len(row),[i for i,w in row],[w for i,w in row])
            h.run()
            if h.getModelStatus()==H.HighsModelStatus.kOptimal:continue
            assert h.getModelStatus()==H.HighsModelStatus.kInfeasible
            _,ok,ray=h.getDualRay();assert ok
            # Prefer a sparse normalized separating combination. A simplex
            # ray may have a huge common denominator even when a short
            # contradiction exists.
            lp=H.Highs();lp.setOptionValue('threads',1);lp.setOptionValue('output_flag',False)
            for _ in range(N+2):lp.addRow(0,H.kHighsInf,0,[],[])
            lp.addRow(1,H.kHighsInf,0,[],[]);tags=[]
            for i,((cs,op),(a,d,e)) in enumerate(zip(A,b)):
                row=[(ids[x],w) for x,w in cs if x in ids]
                row += [(N+j,-v) for j,v in enumerate((d,e,a)) if v]
                if not row:continue
                for s in (1,-1):
                    if op!='=' and (s>0)!=(op=='<='):continue
                    lp.addCol(1,0,H.kHighsInf,len(row),[j for j,w in row],[s*w for j,w in row]);tags.append((i,s))
            lp.run();assert lp.getModelStatus()==H.HighsModelStatus.kOptimal
            y=Counter()
            for (i,s),z in zip(tags,lp.getSolution().col_value):
                if abs(z)>1e-9:y[i]+=s*Q(z).limit_denominator(10**7)
        slack=Counter()
        for i,z in y.items():
            cs,op=A[i];assert op=='=' or (z>=0 if op=='<=' else z<=0)
            for x,w in cs:
                if x in allowed:slack[x]+=w*z
        if not replay:
            repair=Counter()
            for x in allowed:
                if slack[x]<0:
                    i,w=norm[x];repair[i]=max(repair[i],-slack[x]/w)
            for i,z in repair.items():
                y[i]=y.get(i,0)+z
                for x,w in A[i][0]:slack[x]+=z*w
        poly=[sum(z*b[i][j] for i,z in y.items()) for j in range(3)]
        assert min(slack[x] for x in allowed)>=0
        if not (poly[0]<0 and max(poly[1:])<=0):
            print('unrecovered',key,poly,flush=True);assert not replay;continue
        bank[key]={i:str(z) for i,z in y.items() if z};passed.append(pr)
        print('excluded for every 35+42t',pr,*(str(z) for z in poly),flush=True)
    if not replay:save.write_text(json.dumps(bank,separators=(',',':'))+'\n')
    print('remaining charge profiles', [p for p in profiles(sorted(wi)) if p not in passed])
if __name__=='__main__':
    import sys
    run('--build' not in sys.argv)
