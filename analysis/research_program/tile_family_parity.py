"""Unaveraged residue test for the parametric rooted-plaquette count problem."""
from collections import defaultdict,deque,Counter

def check(atoms,eqs,types,mass):
    t=len(types);idx={v:i for i,v in enumerate(types)};vec=[];occ=defaultdict(list)
    for h,(_,ls,_) in enumerate(atoms):
        ds=Counter()
        for k,s in ls:ds[eqs[k]]+=s
        ds=[(i,s) for i,s in ds.items() if s];vec.append(ds)
        for i,s in ds:occ[i,s].append(h)
    cnt=Counter({k:len(z) for k,z in occ.items()});gone=set();work=deque(k for k in occ if not cnt[k[0],-k[1]])
    while work:
        for h in occ[work.popleft()]:
            if h in gone:continue
            gone.add(h)
            for i,s in vec[h]:
                cnt[i,s]-=1
                if not cnt[i,s]:work.append((i,-s))
    # Put seam rows above the type normalizations and score in pivot order.
    piv={};live=set()
    for h,(typ,_,score) in enumerate(atoms):
        if h in gone:continue
        live.add(typ);v=(1<<(idx[typ]+1))|(score&1)
        for i,s in vec[h]:
            if s&1:v^=1<<(t+1+i)
        while v:
            k=v.bit_length()-1
            if k not in piv:piv[k]=v;break
            v^=piv[k]
    print('removed by zero support',len(gone),'remaining types',len(live),'of',len(types),'GF2 rank',len(piv))
    k=39;d=5*k-1+(k-5)//7;v=(d&1)|sum((a%2)<<(j+1) for j,a in enumerate(mass(k)))
    assert mass(k)!=mass(k+14) and all(not (a-b)%2 for a,b in zip(mass(k),mass(k+14)))
    rem=0
    while v:
        i=v.bit_length()-1
        if i in piv:v^=piv[i]
        else:rem^=1<<i;v^=1<<i
    print('parametric one-gap target parity remainder weight',rem.bit_count(),'; zero = not excluded')
    import sys
    if '--seven' in sys.argv:seven(atoms,vec,gone,idx,mass)

def seven(atoms,vec,gone,idx,mass):
    # Coordinatewise GF(7), in three bit planes. Multiplication by two
    # rotates the planes. Addition uses end-around carry modulo 2^3-1.
    def add(x,y):
        c=0;out=[]
        for a,b in zip(x,y):
            u=a^b;out.append(u^c);c=(a&b)|(u&c)
        for i in range(3):b=out[i];out[i]=b^c;c&=b
        bad=out[0]&out[1]&out[2]
        return tuple(z^bad for z in out)
    def scale(x,a):
        if a in (3,5,6):
            g=x[0]|x[1]|x[2];x=tuple(z^g for z in x);a=7-a
        return x if a==1 else (x[2],x[0],x[1]) if a==2 else (x[1],x[2],x[0])
    def enc(items):return tuple(sum(1<<i for i,a in items if a%7>>j&1) for j in range(3))
    def digit(v,i):return sum((b>>i&1)<<j for j,b in enumerate(v))
    for a in range(7):
        for b in range(1,7):
            x=enc([(0,a)]);y=enc([(0,b)])
            assert digit(add(x,y),0)==(a+b)%7 and digit(scale(x,b),0)==a*b%7
    piv={};off=1+len(idx)
    for h,(typ,_,cost) in enumerate(atoms):
        if h in gone:continue
        v=enc([(0,cost),(1+idx[typ],1)]+[(i+off,s) for i,s in vec[h]])
        while (i:=(v[0]|v[1]|v[2]).bit_length()-1)>=0:
            a=digit(v,i)
            if i not in piv:piv[i]=scale(v,pow(a,-1,7));break
            v=add(v,scale(piv[i],7-a))
    ok=[]
    for t in range(7):
        k=39+14*t;D=5*k-1+(k-5)//7
        v=enc([(0,D)]+[(i+1,z) for i,z in enumerate(mass(k))])
        while (i:=(v[0]|v[1]|v[2]).bit_length()-1) in piv:v=add(v,scale(piv[i],7-digit(v,i)))
        if not any(v):ok.append(t)
    print('GF7 rank',len(piv),'surviving side 119+42t residues t mod 7',ok,flush=True)
