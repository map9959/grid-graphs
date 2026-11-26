"""Try a sufficient, rather than necessary, period-three fractional primal ansatz."""
from .patch_square import relaxation,Q,Path,json
from .side28_score import solve


def model(d,n):
    base=2*d+10
    base+=(1-base)%3
    ns,r,o=relaxation(base,depth=d,period=3)
    def count(N,p):
        return ((N-2*d+2-(p-d))//3 if d<=p<d+3 else 1)
    obj={}
    for (kind,atom),x in ns.items():
        if o[x]:
            a,b=atom[0]
            v=o[x]*count(n,a)*count(n,b)
            w=count(base,a)*count(base,b);assert v%w==0
            obj[x]=v//w
    return ns,list(r),obj


def replay():
    d=8;ns,rows,_=model(d,49)
    p={x:Q(v) for x,v in json.loads(Path(__file__).with_name('tied_cap_obstruction_r1.json').read_text()).items()}
    assert set(p)<=set(ns.values()) and min(p.values())>=0
    for c,op,b in rows:
        z=sum(w*p.get(x,0) for x,w in c)-b
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    def count(j,t):
        return 1 if not d<=t<d+3 else (49-2*d+2-(t-d))//3+10*j
    # Expand the physical site objective directly, one D4 event per bit:
    # use base multiplicities only to recover the labeled-orbit factor.
    _,_,raw=relaxation(28,depth=d,period=3)
    coeff=[Q(0)]*3
    for (kind,atom),x in ns.items():
        if not raw[x] or x not in p:continue
        a,b=atom[0]
        den=lambda t:(28-2*d+2-(t-d))//3 if d<=t<d+3 else 1
        orbit=Q(raw[x],den(a)*den(b));assert orbit.denominator==1
        u,v=count(0,a),count(0,b);U,V=count(1,a)-u,count(1,b)-v
        for i,w in enumerate((u*v,U*v+V*u,U*V)):coeff[i]+=orbit*p[x]*w
    excess=[a-b for a,b in zip(coeff,(851,1013,300))]
    assert excess==[Q(4,9),Q(1,3),0]
    print('verified',len(rows),'pointwise rows;',len(p),'nonzero rational variables')
    print('fractional score minus cap for n=49+30j:',*[str(z) for z in excess], '(constant,linear,quadratic)')
    print('side 109: cap 4077; fractional score',sum(a*2**i for i,a in enumerate(coeff)))


def physical(n):
    """Independent large-board check on the original unpooled constraint matrix."""
    from .patch_square import SYM,trans
    d=8;ns,_,_=model(d,n)
    y={x:Q(v) for x,v in json.loads(Path(__file__).with_name('tied_cap_obstruction_r1.json').read_text()).items()}
    names,rows,obj=relaxation(n);p={}
    for (kind,atom),x in names.items():
        pos,*event=atom
        D,S=(8,n) if kind=='s' else (7,n-2)
        def ax(t):return t if t<D else 2*D+3-S+t if t>=S-D else D+(t-D)%3
        orbit=[]
        for g in range(8):
            q=tuple(map(ax,trans(*pos,S,g)))
            if kind=='p':orbit.append((q,SYM[event[0]][g]));continue
            f,nb,arrow=event
            turn=lambda i:((2-i if g&4 else i)+(g%4))%4
            v=[9]*4
            for i in range(4):v[turn(i)]=nb[i]
            orbit.append((q,f,tuple(v),turn(arrow) if arrow>=0 else -1))
        v=y.get(ns[kind,min(orbit)],0)
        if v:p[x]=v
    for c,op,b in rows:
        z=sum(w*p.get(x,0) for x,w in c)-b
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    print('unpooled side',n,'rows',len(rows),'exact primal',sum(w*p.get(x,0) for x,w in obj.items()))


if __name__=='__main__':
    import sys
    if '--replay' in sys.argv:
        replay();sys.exit()
    if '--physical' in sys.argv:
        physical(int(sys.argv[-1]));sys.exit()
    d,n=map(int,sys.argv[1:3]);ns,r,obj=model(d,n)
    score,y,p=solve([(c,op) for c,op,b in r],[b for c,op,b in r],obj,ns)
    k=(n-1)//3
    print('depth',d,'side',n,'fractional candidate excess',score-(3*k*k+5*k+(3*k-13)//10),flush=True)
    Path(f'target/tied_cap_{d}_{n}.json').write_text(json.dumps({x:v for x,v in p.items() if v>1e-8}))
