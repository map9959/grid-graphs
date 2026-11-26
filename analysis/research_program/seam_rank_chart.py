"""A rectangular star/patch relaxation for rail-seam marks plus detached roots."""
from collections import Counter,defaultdict
from itertools import product
from .patch_square import MASKS,DIR,local
from .square_current import states
from .side28_score import solve
from .repeating_patch_dual import Q,verify,recover
import sys
import json
from pathlib import Path

def model(H,N,d,world=None):
    wired='--wired-box' in sys.argv
    diag=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--box-diag=')),None)
    phases=[next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--'+end+'-phase=')),0) for end in ('top','bottom')]
    slip=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--slip=')),None)
    def rail(y,p,top):
        if top and slip is not None:return 0<=y<N and (y<=slip and y%3==0 or y>=slip+4 and y%3==1)
        return 0<=y<N and y%3==p
    def coord(x,S,h):return x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
    def pt(i,j,t,fine):
        h=d+4-t if fine else d
        base=coord(i,H-2*t,h),coord(j,N-2*t,h)
        if diag is not None:
            bound=diag+(5 if fine else 0)
            y=i if world is None else world(i,t)
            base+=tuple(max(-bound,min(bound,v)) for v in (y-j,y+j+1-(N-2*t)))
        return base if slip is None else (*base,max(-h-1,min(h+1,j-slip)))
    mass=[Counter(pt(i,j,t,1) for i,j in product(range(H-2*t),range(N-2*t))) for t in (0,1)]
    star={};patch={};names={};rows=[];rhs=[];norm=[];obj={}
    price=next((Q(s[8:]) for s in sys.argv if s.startswith('--price=')),Q(1))
    def var(k):return names.setdefault(k,'x'+str(len(names)))
    def push(c,z,key=None):
        ls=[(x,v) for x,v in c.items() if v]
        if not ls:assert z==0;return
        rows.append((ls,'='));rhs.append(z);norm.append(key)
    for i,j in product(range(H),range(N)):
        z=pt(i,j,0,1)
        if z in star:continue
        freebottom='--free-bottom' in sys.argv
        freetop='--free-top' in sys.argv
        ds=tuple(s for s,(x,y) in enumerate(DIR) if ('--four-ports' in sys.argv or 0<=j+y<N) and not(freebottom and i==H-1 and s==1) and not(freetop and i==0 and s==3))
        outside=[s for s,(u,v) in enumerate(DIR) if not(0<=i+u<H and 0<=j+v<N)]
        if wired:ds=tuple(s for s in range(4) if s not in outside[1:])
        ls=[]
        for f,sg in states(ds):
            nb=tuple(sg[s][int(s<2)] if s in sg else 9 for s in range(4))
            o=next((s for s,v in sg.items() if v[2]==(1 if s<2 else -1)),-1)
            if wired:
                if outside and (nb[outside[0]] or (o==outside[0])!=bool(f)):continue
            elif '--wired-bars' in sys.argv and i in (0,H-1):
                t=3 if i==0 else 1
                if nb[t] or (o==t)!=bool(f):continue
            elif (i==0 and not freetop or i==H-1 and not freebottom) and '--free-ports' not in sys.argv:
                t=3 if i==0 else 1
                p=phases[int(i!=0)]
                if nb[t]!=int(rail(j,p,i==0)) or f and (rail(j-1,p,i==0) or rail(j+1,p,i==0)):continue
                if not i and '--unwired' not in sys.argv and '--rank-both' not in sys.argv and (o==3)!=bool(f or rail(j,p,i==0)):continue
            x=var(('s',z,f,nb,o));obj[x]=f+price*int(i==H-1 and o==1 and '--unwired' not in sys.argv)
            if '--wired-bars' in sys.argv or wired:obj[x]=f
            if '--free-ports' in sys.argv:
                direction=3 if i==0 else 1 if i==H-1 else None
                obj[x]=f-price*int(direction is not None and bool(f or nb[direction]) and o!=direction)
                if '--four-ports' in sys.argv and j in (0,N-1):
                    e=2 if j==0 else 0
                    obj[x]-=price*int(bool(f or nb[e]) and o!=e)
            if '--rank-both' in sys.argv and i in (0,H-1):
                assert not (freebottom or freetop or '--unwired' in sys.argv)
                p=phases[int(i!=0)]
                ghost=not any(rail(j+a,p,i==0) for a in (-1,0,1))
                obj[x]=f+price*int(o==(3 if i==0 else 1) or ghost and not f)
            ls.append((x,f,nb,o))
        star[z]=ls;push(Counter(x for x,*_ in ls),mass[0][z],(0,z))
    for i,j in product(range(H-2),range(N-2)):
        z=pt(i,j,1,1)
        if z in patch:continue
        tab={}
        for m in MASKS:
            if wired and any(sum(m>>(3*a+b)&1 for a,b in group)>1 for group,active in (
                    ([(0,b) for b in range(3)],i==0), ([(2,b) for b in range(3)],i==H-3),
                    ([(a,0) for a in range(3)],j==0), ([(a,2) for a in range(3)],j==N-3)) if active):continue
            if not wired and '--free-ports' not in sys.argv and '--wired-bars' not in sys.argv and any((x==0 and '--free-top' not in sys.argv or x==H-1 and '--free-bottom' not in sys.argv) and (rail(y-1,phases[int(x!=0)],x==0) or rail(y+1,phases[int(x!=0)],x==0)) and (m>>(3*a+b)&1) for a,b in product(range(3),repeat=2) for x,y in [(i+a,j+b)]):continue
            tab[m]=var(('p',z,m))
        patch[z]=tab;push(Counter(tab.values()),mass[1][z],(1,z))
    acc=defaultdict(Counter)
    occ=Counter()
    # Sum each side of a physical incidence once per participating
    # fine type. Its multiplicity is already carried by its variables.
    used=set()
    def use(k,t,z,mapper,sign):
        if (k,t,z,sign) in used:return
        used.add((k,t,z,sign))
        for sig,v in mapper():acc[k,sig][v]+=sign
    for i,j in product(range(H),range(N)):
        for s,(a,b) in enumerate(DIR[:2]):
            if i+a>=H or j+b>=N:continue
            k=('edge',s,pt(i,j,0,0),pt(i+a,j+b,0,0))
            for x,y,r,sign in ((i,j,s,1),(i+a,j+b,(s+2)%4,-1)):
                z=pt(x,y,0,1)
                use(k,0,z,lambda:(((f,nb[r],o==r) if sign==1 else (nb[r],f,bool(f or nb[r]) and o!=r),v) for v,f,nb,o in star[z]),sign)
    for i,j in product(range(H-2),range(N-2)):
        z=pt(i,j,1,1)
        for a,b in product(range(3),repeat=2):
            q=3*a+b;u=pt(i+a,j+b,0,1);k='sp',q,pt(i,j,1,0),pt(i+a,j+b,0,0)
            dirs=[d0 for d0,(x,y) in enumerate(DIR) if 0<=a+x<3 and 0<=b+y<3]
            use(k,0,u,lambda:(((f,*[nb[s] for s in dirs]),v) for v,f,nb,o in star[u]),1)
            use(k,1,z,lambda:((local(m,q),v) for m,v in patch[z].items()),-1)
        for a,b in DIR[:2]:
            if i+a>=H-2 or j+b>=N-2:continue
            k='pp',a,b,pt(i,j,1,0),pt(i+a,j+b,1,0)
            for di,dj,sign in ((0,0,1),(a,b,-1)):
                v=pt(i+di,j+dj,1,1)
                use(k,1,v,lambda:((tuple(m>>(3*(x-di)+y-dj)&1 for x in range(a,3) for y in range(b,3)),u) for m,u in patch[v].items()),sign)
    for row in acc.values():push(row,0)
    return rows,rhs,obj,names,norm
def run(H,N,d):
    A,b,o,ns,norm=model(H,N,d);print('chart',H,N,'atoms',len(ns),'rows',len(A),flush=True)
    topfree='--free-top' in sys.argv
    cert=Path(__file__).with_name(f'seam_rank_{H}_{N}_{d}'+('_unwired' if '--unwired' in sys.argv else '')+('_free' if '--free-bottom' in sys.argv else '')+('_topfree' if topfree else '')+'.json')
    if any(s.startswith('--price=') for s in sys.argv):cert=cert.with_name(cert.stem+'_price'+str(next(s[8:] for s in sys.argv if s.startswith('--price='))).replace('/','_')+'.json')
    if '--rank-both' in sys.argv:cert=cert.with_name(cert.stem+'_rankboth.json')
    for end in ('top','bottom'):
        ph=next((s.split('=')[1] for s in sys.argv if s.startswith('--'+end+'-phase=')),None)
        if ph is not None:cert=cert.with_name(cert.stem+f'_{end}{ph}'+'.json')
    if '--replay' in sys.argv:yy={int(k):Q(v) for k,v in json.loads(cert.read_text()).items()}
    else:
        val,y,_=solve(A,b,o,ns,interior='--exact' not in sys.argv)
        print('seam excess over straight',val-H*(N//3+1))
        if '--exact' not in sys.argv:return
        raw={i:Q(v) for i,v in enumerate(y) if abs(v)>1e-9};yy={i:v.limit_denominator(100000) for i,v in raw.items()}
        if verify(A,o,yy)>0:yy=recover(A,o,raw)
    if '--exact' in sys.argv or '--replay' in sys.argv:
        assert verify(A,o,yy)<=0
        def count(t,z,U,V):
            h=d+4-t
            return (1+(H-2*t-1-h-z[0])//3+U if h<=z[0]<h+3 else 1)*(1+(N-2*t-1-h-z[1])//3+V if h<=z[1]<h+3 else 1)
        success=min(H,N)>=2*(d+4)+3
        shifted='--shifted-certificate' in sys.argv
        if shifted:assert '--rank-both' in sys.argv and '--price=7/10' in sys.argv
        for U,V in product(range(2),repeat=2):
            ub=sum(q*count(*norm[i],U,V) for i,q in yy.items() if norm[i])
            expected=(H+3*U+int(topfree))*((N+3*V)//3+1)
            if '--rank-both' in sys.argv:expected+=Q(next(s[8:] for s in sys.argv if s.startswith('--price=')))*((N+3*V)//3+1)
            print('symbolic corner',U,V,ub,'excess',ub-expected)
            success &= ub<=expected if shifted else ub==expected
        if '--replay' in sys.argv:assert success
        if '--matrix' in sys.argv:
            def signature(rows,labels):
                return {(tuple(sorted(ls)),op,k) for (ls,op),k in zip(rows,labels)}
            for U,V in ((0,1),(1,0),(1,1)):
                aa,bb,oo,nn,zz=model(H+3*U,N+3*V,d)
                assert nn==ns and oo==o and signature(aa,zz)==signature(A,norm)
                assert all(v==count(*k,U,V) if k else v==0 for v,k in zip(bb,zz))
            print('all three growth matrices and normalization counts checked')
        if success and '--exact' in sys.argv:cert.write_text(json.dumps({i:str(v) for i,v in yy.items() if v},separators=(',',':'))+'\n')
if __name__=='__main__':run(*map(int,sys.argv[1:4]))
