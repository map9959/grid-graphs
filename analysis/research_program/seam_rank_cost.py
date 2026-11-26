"""Price a free rewiring band by the number of detached lower components."""
import subprocess,sys

def run(n,h,check=(),prove=False):
    assert n%3==1
    ix={};es=[];fix=[];tags=[];cp=[]
    def node(key,tag):
        ix[key]=len(es);es.append([]);fix.append(0 if tag else -1);tags.append(tag)
    def edge(u,v,always=False):
        a,b=sorted((ix[u],ix[v]));es[b].append((a,always))
    node('upper',2)
    phase=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--lower-phase=')),0)
    slip=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--slip=')),None)
    assert (not phase and slip is None) or '--free-top' in sys.argv
    mask={j for j in range(n) if (j%3==phase if slip is None else j<=slip and j%3==0 or j>=slip+4 and j%3==1)}
    for j in range(n):
        center=next((u for u in (j-1,j,j+1) if u in mask),j)
        r=('lower',0 if '--wired-bottom' in sys.argv else center)
        if r not in ix:node(r,2 if '--wired-bottom' in sys.argv else 1)
        for i in range(h):
            node((i,j),0)
            if i:edge((i,j),(i-1,j))
            if j:edge((i,j),(i,j-1))
        if '--free-top' not in sys.argv:edge('upper',(0,j),j%3==0)
        edge(r,(h-1,j),j in mask)
        if j in check:cp.append(len(es)-1)
    if '--by-row' in sys.argv:
        assert not check
        order=[ix['upper'],*[ix[i,j] for i in range(h) for j in range(n)],*[ix['lower',r] for r in range((n+2)//3)]]
        where={v:i for i,v in enumerate(order)};ls=[[] for _ in order]
        for i,links in enumerate(es):
            for j,u in links:
                a,b=sorted((where[i],where[j]));ls[b].append((a,u))
        es=ls;fix=[fix[i] for i in order];tags=[tags[i] for i in order]
    N=len(es);inp=[N,*[a for ls in es for a in (len(ls),*(i+1+N*u for i,u in ls))],*fix,-2,*tags,*cp]
    weights=next((s[9:].split(',') for s in sys.argv if s.startswith('--prices=')),[])
    if '--counts' in sys.argv:weights.append('--counts')
    if '--classes' in sys.argv:weights.append('--classes')
    if '--prefix' in sys.argv:weights.append('--prefix')
    r=subprocess.run(['target/annular_frontier',*weights],input=' '.join(map(str,inp)),text=True,capture_output=True,check=True)
    if '--counts' in sys.argv:return dict(tuple(map(int,ln.split())) for ln in r.stdout.splitlines())
    if '--classes' in sys.argv:
        if check and '--quiet' not in sys.argv:print(r.stderr.strip(),flush=True)
        return dict(tuple(map(int,ln.split())) for ln in r.stdout.splitlines()),r.stderr
    z,W,peak=map(int,r.stdout.split())
    if prove:
        assert z==h*(n//3+1)
        if check:assert f'dominated true shift {h}\n' in r.stderr
    if '--quiet' not in sys.argv:print('n',n,'height',h,'prices',weights or [1,1],'maximum',z,'states',peak,r.stderr.strip(),flush=True)
    if '--two-profiles' in sys.argv and check:
        assert f'same true dominated true shift {300 if h==2 else 720}' in r.stderr
    return z
if __name__=='__main__':
    if '--six-cap-price' in sys.argv:
        sys.argv.extend(['--free-top','--prices=10,7','--classes'])
        _,log=run(163,6,[99,129]);assert 'same true dominated true shift 700' in log
        for n in range(19,131,3):
            vals,_=run(n,6);k=n//3
            assert vals[1]==70*k+57 and vals[2]<=70*k+54,(n,vals)
        print('six-row cap: connected score <= 6r+k-1; otherwise 10*marks+7*classes <=70k+54, all widths 3k+1 >=19')
    elif '--two-profiles' in sys.argv:
        sys.argv.extend(['--free-top','--prices=10,9','--quiet'])
        for h in (2,6):run(133,h,[60,90])
        for n in range(19,92,3):
            k=n//3;r=k+1;C=3*k*k+5*k+(3*k-13)//10
            upper=run(n,2)+run(n,6)-9*(r+1)+10*(n-8)*r
            print(n,'tenths above comb',upper-10*C)
            if n>=64:assert 10*C<=upper<10*(C+1)
    elif '--prove' in sys.argv:
        for h in range(6,10):
            run(34,h,prove=True);run(40,h,[30,33],True)
    else:run(int(sys.argv[1]),int(sys.argv[2]),[int(s) for s in sys.argv[3:] if not s.startswith('--')])
