"""Exact recovery and width transport of the free-count no-pitch dual."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json,heapq
from .rank44_faces import test


def chart(n):
    ns,A,b,M,bo,_,S,_=test(weighted=True,free=True,cuts=False,n=n)
    A.append((list(S.items()),'>='));b.append(1)
    return ns,A,b,M,bo


def exact(A,M,bo,raw):
    # Fix short rationals tentatively, solve tight column equations on
    # the remaining support, and accept only after checking every column.
    guess={i:Q(v).limit_denominator(16384) for i,v in raw.items()}
    fixed={i:q for i,q in guess.items() if abs(raw[i]-float(q))<3e-12}
    cols=defaultdict(dict);rc=Counter(M)
    for i,a in raw.items():
        for x,w in A[i][0]:
            if x in bo:continue
            rc[x]-=w*a
            if i in fixed:continue
            cols[x][i]=w
    rhs=Counter(M)
    for i,z in fixed.items():
        for x,w in A[i][0]:rhs[x]-=w*z
    eq=[];v=[];inc=defaultdict(set);heap=[];pivs=[]
    for x,c in cols.items():
        if abs(rc[x])>2e-9:continue
        t=len(eq);eq.append({i:Q(w) for i,w in c.items()});v.append(rhs[x])
        for i in c:inc[i].add(t)
        heapq.heappush(heap,(len(c),t))
    while heap:
        size,t=heapq.heappop(heap);c=eq[t]
        if not c or len(c)!=size:continue
        i=min(c,key=lambda s:(len(inc[s]),s));w=c[i]
        for s in c:inc[s].remove(t)
        del c[i];c={s:z/w for s,z in c.items()};b=v[t]/w
        eq[t]={};pivs.append((i,c,b))
        for j in inc.pop(i):
            row=eq[j];z=row.pop(i);v[j]-=z*b
            for s,u in c.items():
                if s not in row:inc[s].add(j)
                row[s]=row.get(s,0)-z*u
                if not row[s]:del row[s];inc[s].remove(j)
            if row:heapq.heappush(heap,(len(row),j))
            else:assert v[j]==0,('inconsistent recovery',j,v[j])
    y={**{i:Q(a).limit_denominator(10**6) for i,a in raw.items()},**fixed}
    for i,c,b in reversed(pivs):y[i]=b-sum(z*y[s] for s,z in c.items())
    return y


def verify(A,M,bo,y):
    rc=Counter(M)
    for i,z in y.items():
        row,op=A[i];assert op=='=' or (z>=0 if op=='<=' else z<=0)
        for x,w in row:rc[x]-=w*z
    assert not any(bo.values())
    assert max(z for x,z in rc.items() if x not in bo)<=0


def recover(n):
    from .side28_score import solve
    ns,A,b,M,bo=chart(n)
    rawfile=Path(f'target/free_basic_{n}.json')
    if rawfile.exists():raw={int(i):z for i,z in json.loads(rawfile.read_text()).items()}
    else:
        _,y,_=solve(A,b,M,ns,interior='cross',bounds=bo)
        raw={i:z for i,z in enumerate(y) if abs(z)>1e-9}
    if n==25:
        # A bounded-error dual suffices at a single finite width.
        y={i:Q(round(v*10**10),10**10) for i,v in raw.items()}
    else:
        y=exact(A,M,bo,raw);verify(A,M,bo,y)
    ub=sum(b[i]*z for i,z in y.items())
    print('exact dual',n,'upper',ub,'multipliers',len(y),flush=True)
    Path(__file__).with_name(f'free_width_{n}.json').write_text(json.dumps(
        [(i,str(z)) for i,z in sorted(y.items()) if z],separators=(',',':'))+'\n')


def tail(base,source):
    from .chart_counts import count
    from .rank44_faces import labels
    from .skeleton_floor_words import priced,LETTERS
    from itertools import product
    # No new fine label can appear: their exact nonnegative bucket
    # counts already exhaust the entire square polynomial.
    for S,h in ((base,8),(base-2,7)):
        clip=lambda z:max(-9,min(9,z))
        types={(*labels(i,j,S,h),clip(i-j),clip(i+j+1-S))
               for i,j in product(range(S),repeat=2)}
        coeff=[count(S,h,9,p) for p in types]
        assert tuple(map(sum,zip(*coeff)))==(S*S,12*S+36,72)
    # Extra triples insert interior layers of the same automaton.
    states={('p0',None,0),('pre',None,0)}
    for i in range(5):
        new={v[0] for s in states for a in LETTERS if i or not a[0]
             for v in [priced(s,a,False)] if v is not None}
        if i==4:assert new==states
        states=new
    y={i:Q(z) for i,z in json.loads(Path(__file__).with_name(
        f'free_width_{source}.json').read_text())}
    for n in (base,base+6,base+12):
        ns,A,b,M,bo=chart(n);verify(A,M,bo,y)
        k=n//3;ub=sum(b[i]*z for i,z in y.items())
        assert ub==3*k*k+Q(21*k,4)-Q(79,64)
        if n==base:ref=(ns,[ (dict(row),op) for row,op in A],M,bo)
        else:assert (ns,[(dict(row),op) for row,op in A],M,bo)==ref
    print('base',base,'step 6: exact no-pitch upper 3k²+21k/4-79/64;',len(y),'multipliers')


def finite(n):
    from .comb_cap_transfer import construct,verify as tree
    ns,A,b,M,bo=chart(n)
    y={i:Q(z) for i,z in json.loads(Path(__file__).with_name(
        f'free_width_{n}.json').read_text())}
    rc=Counter(M)
    for i,z in y.items():
        row,op=A[i];assert op=='=' or (z>=0 if op=='<=' else z<=0)
        for x,w in row:rc[x]-=z*w
    assert not any(bo.values())
    ub=sum(b[i]*z for i,z in y.items())+n*n*sum(z for x,z in rc.items() if z>0 and x not in bo)
    k=n//3;comb=3*k*k+5*k+(3*k-13)//10
    assert ub<comb+1 and tree(construct(n,4))[-1]==comb
    print('side',n,'conditional no-pitch upper',ub,'attained',comb)


if __name__=='__main__':
    import sys
    if sys.argv[1:]:
        for n in map(int,sys.argv[1:]):recover(n)
    else:
        tail(58,106);tail(61,103)
        for n in (19,22,25,52):finite(n)
