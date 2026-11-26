"""Glue a growing number of east-side bands with physical cut connectivity."""
from functools import lru_cache
from .arm_budget_bands import B,advance,physical,spectrum,transpose
from .neighbor_diagonal import group,interface,row

def phase(k,q):
    """The exact marked components still active on the common cut."""
    n=3*k
    if q<0:return -1,tuple(range(n+1)),(0,)*n+(1,)
    s,_=row(k,q);m,pp=interface(k,q);root=3*s+2
    # advance labels by first occurrence on the frontier, virtual root last.
    part=tuple(0 if i==n else i for i in pp)
    flags=tuple(3 if i==0 else 2 if i==root+2 else 0 for i in range(n+1))
    return sum(b<<j for j,b in enumerate(m)),part,flags

def certify_groups():
    # The physical one-gap chart is not assumed to be transpose-invariant.
    BT={(v,u):{tuple(transpose(w[h]) for h in (0,2,1,3)) for w in ws}
        for (u,v),ws in B.items()}
    for j in range(6,13):assert all(a==448 for a,b,c,d in BT[6,j] if c==448)
    assert all(b==192 for a,b,c,d in BT[6,12] if (c,d)==(448,192))
    for a in range(4):
        k=16+4*a;n=3*k;front=phase(k,3*a-1)
        group(k,a,BT,interface(k,3*a-1))
        for q in range(3*a,3*a+3):
            _,w=row(k,q)
            if q==0:assert all(transpose(v)!=192 for v in w)
            for lane in (2,1,0):
                m=sum((v>>(3*lane+b)&1)<<(3*j+b) for j,v in enumerate(w) for b in range(3))
                teeth=(1<<n)-1 if q==0 and lane==1 else 2|(1<<(n-2))
                front=advance(front,m,teeth,0)
                assert front is not None,'cycle or closed unrooted marked component'
        assert front==phase(k,3*a+2)
    print('4 common-cut transfers verified; exactly one unrooted marked component, one exposed site')

def layout(t):
    k=39+14*t;H=12*((k-12)//16);R=k-H
    g=(R-3)//4;two=(R-3)%4
    assert two in (0,2)
    extra=t//8
    d=5*k-1+(k-5)//7
    first=d-(6*H-2)-10*g-(5 if two else 0)-2*extra
    groups=[(0,3,first)]
    groups.extend((3 if j==0 else 7,4,12 if 1<=j<=extra else 10) for j in range(g))
    if two:groups.append((7,2,5))
    assert extra<g and sum(c for _,_,c in groups)+6*H-2==d
    return k,H,groups

@lru_cache(None)
def west(axis,r,h,c):
    bits,get=spectrum(r,h,axis,True,0,True);assert bits>>c&1
    return get(c)

def audit():
    certify_groups()
    for t in range(8):
        k,H,gs=layout(t);k2,h2,gs2=layout(t+8)
        assert (k2-k,h2-H,len(gs2)-len(gs),gs2[0])==(112,84,7,gs[0])
    for axis in (1,2):
        for t in range(8):
            k,H,gs=layout(t);r=0;total=0;s=k-4*H//3
            # Join one additional freely filled band to the diagonal. The
            # exact spectrum is computed without a pump or a shape constraint
            # on this side of the cut; also extract a stationary witness.
            _,h,c0=gs.pop()
            bs=spectrum(7,h,axis,False,None,True,s)
            c=(bs&-bs).bit_length()-1;assert c==6*h
            ps,get=spectrum(7,h,axis,True,0,True,s)
            # Pick a nonminimum cost to test a continuation distinct from
            # simply extending the canonical six-deficit diagonal sequence.
            c+=1;assert ps>>c&1
            joined=get(c);j=s+4;joined=joined[:j+1]+[joined[j]]*(14*t)+joined[j+1:]
            gs[0]=(0,3,gs[0][2]-(c-c0))
            for ref,h,c in gs:
                path=west(axis,ref,h,c);p=path[:13]+[path[12]]*(14*t)+path[13:]
                assert physical(p,r,k,axis,True)==(c,0);r+=h;total+=c
            assert r==k-H-len(joined[0])
            # Independent, unsliced graph traversal across every internal
            # cut of the joined region. The east is processed as ONE band.
            east=list(zip(*(row(k,q)[1] for q in reversed(range(H)))))
            united=[(*a,*b) for a,b in zip(joined,east)]
            cost,sealed,route=physical(united,r,k,axis,True,(3*len(joined[0]),3*s+4))
            assert sealed==0 and cost==6*(H+len(joined[0]))-1
            assert total+cost==198+72*t
            assert route==(1,False)
            print('axis',axis,'t',t,'joined tile columns',len(united[0]),'score deficit',total+cost,
                  'old free component (teeth, touches remaining cut)',route)
        print('axis',axis,'eight classes: exact budgets 198..702; joined-band minima 12/24, replayed 13/25')
        rooted_audit(axis)

def rooted_audit(axis):
    for t in range(9):  # also replay one full induction enlargement
        k,H,gs=layout(t)
        if gs[-1][1]==2:
            # Two columns alone cannot discharge all new components.
            s=k-4*H//3
            assert spectrum(7,2,axis,False,None,True,s,True)==0
            gs[-2:]=[gs[-1],gs[-2]]
        if t%8==5:
            # Trade the last three diagonal columns for a cheap bulk band.
            H-=3;gs.insert(-1,(7,3,7));gs[0]=(0,3,gs[0][2]+18-7)
        s=k-4*H//3;_,h,old=gs.pop();assert h==4
        bs=spectrum(7,h,axis,False,None,True,s,True)
        c=(bs&-bs).bit_length()-1;assert c==s+21
        ps,get=spectrum(7,h,axis,True,0,True,s,True);assert ps>>c&1
        p=get(c);j=s+4
        p=p[:j+1]+[p[j]]*(14*t)+p[j+1:]
        gs[0]=(0,3,gs[0][2]+old-c)
        total=r=0
        for ref,h,d in gs:
            w=west(axis,ref,h,d)
            assert physical(w[:13]+[w[12]]*(14*t)+w[13:],r,k,axis,True)==(d,0)
            total+=d;r+=h
        assert r==k-H-4
        e=zip(*(row(k,q)[1] for q in reversed(range(H))))
        cost,closed=physical([(*a,*b) for a,b in zip(p,e)],r,k,axis,True,require_roots=True)
        assert closed==0 and cost==6*H-2+c and total+cost==198+72*t
        print('all marked components rooted: axis',axis,'t',t,'joined columns',H+4,
              'last-band cost',c,'total deficit',total+cost)

if __name__=='__main__':audit()
