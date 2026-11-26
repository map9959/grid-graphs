"""Try the actual 102-lane 78 -> 36 relation at the ports of a 245 donor."""
from itertools import product,combinations
from pathlib import Path
from hashlib import file_digest
import gzip,sys,subprocess
from .defect_window import table,window
from .shorten_245_star import nb

def run(lo,hi,right,mode,seconds,sweep=-1,H=102,consensus=0):
    name=f'long_quarters_{lo}_{hi}'
    raw=gzip.decompress((Path(__file__).with_name('one_gap_projection_examples')/(name+'.gz')).read_bytes())
    big={(i,j) for i,j in product(range(245),repeat=2) if min(i,j,244-i,244-j)<8 or i<=101 or j>=143}
    data=dict(zip(sorted(big),raw[2:],strict=True));X={p for p,b in data.items() if b>=5}
    if consensus:
        from .southwest_ports import patterns
        assert right and mode==0 and H==102 and sweep>=0 and (lo,hi)==(5,5)
        shared=patterns(True)
    out={p:b%5-1 for p,b in data.items() if b%5}
    assert 3<=H<=102
    s=150 if right else 60
    if sweep>=0:
        assert right and mode==0 and sweep<=2
        s+=sweep
    pt=lambda n,i,j:(j,n-1-i) if right else (i,j)
    back=3 if right else 2
    # All steps have zero charge; preserve the location of the star.
    assert raw[1]<60 or raw[1]>139 or right
    A={pt(203,r,j) for r,j in product(range(H),range(s,s+37))}
    parent={}
    def rt(u):
        while u in parent:u=parent[u]
        return u
    for j in range(s,s+79):
        for r in range(H):
            u=pt(245,r,j)
            for rr,jj in ((r,j+1),(r+1,j)):
                if rr==H or jj==s+79 or (jj==j==s):continue
                v=pt(245,rr,jj)
                if u in X or v in X:
                    a,b=rt(u),rt(v);assert a!=b;parent[a]=b
    ports={pt(203,r,s+h*36):rt(pt(245,r,s+h*78)) for h,r in product(range(2),range(H))}
    lab={c:k for k,c in enumerate(sorted(set(ports.values())))}
    small=table(203);bigtyp=table(245)[0]
    def emit(f,bit,flags,arc,sheet):
        # At the weakest setting ONLY the mark masks of the two end
        # columns are fixed. No directed or connectivity label is needed.
        starts=[s] if sweep<0 else list(range(102+sweep,161,3))
        for t in starts:
            for tag in (0,1):
                for k,r in product(range(79-2*tag),range(H)):
                    p=pt(245,r,t+k);q=pt(203,r,s+k%3)
                    if max(p)<245-2*tag:assert bigtyp(tag,*p)==small[0](tag,*q)
        top=max(f.nv,max(bit(*u) for u in A))
        sels=list(range(top+1,top+1+len(starts))) if sweep>=0 else []
        if sels:f.append(sels)
        for idx,t in enumerate(starts):
            guard=[-sels[idx]] if sels else []
            for j,jj in [(s,t),(s+36,t+78)]+([(s+35,t+77)] if mode>0 else []):
                for r in range(H):
                    u,v=pt(203,r,j),pt(245,r,jj)
                    if consensus and v not in shared[t]:continue
                    f.append(guard+[bit(*u)*(1 if v in X else -1)])
                    if mode and j==s+36:f.append([arc(*u,back)*(1 if out.get(v)==back else -1)])
        # Ground the entire tangent boundary as required by the frame.
        for j in range(s,s+37):
            for r in (0,1):f.append([bit(*pt(203,r,j))*(1 if not r else -1)])
        if mode==2:
            bits=(len(lab)-1).bit_length();ids={u:f.nv+1+k*bits for k,u in enumerate(sorted(A))}
            for u,c in ports.items():
                for k in range(bits):f.append([(ids[u]+k)*(1 if lab[c]>>k&1 else -1)])
            for u in A:
                for d in (0,1):
                    v=nb(u,d)
                    if v not in A or (u[0 if right else 1]==v[0 if right else 1]==s):continue
                    for k in range(bits):
                        a,b=ids[u]+k,ids[v]+k
                        for z in (bit(*u),bit(*v)):f.extend([[-z,-a,b],[-z,a,-b]])
        stem=Path(f'target/star_strip_{lo}_{hi}_{right}_{mode}'+(f'_sw{sweep}' if sels else ''));fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        if H!=102:
            stem=stem.with_name(stem.name+f'_h{H}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        if consensus:
            stem=stem.with_name(stem.name+'_shared');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        f.to_file(str(fn))
        with fn.open('rb') as fd:print('donor star',raw[1],'channel',('right' if right else 'top'),'start',s,'port classes',len(lab),'mode',mode,'CNF',file_digest(fd,'sha256').hexdigest(),flush=True)
        with stem.with_suffix('.log').open('w') as fd:st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=fd).returncode
        if st==20:
            with stem.with_suffix('.check').open('wb') as fd:subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],stdout=fd,check=True)
            assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
            print('78-step donor interface has NO 36-step realization: s VERIFIED',starts)
        elif st==10:
            model={int(z) for l in stem.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for z in l[2:].split()}
            marks={u for u in A if bit(*u) in model};p={}
            def root(u):
                while u in p:u=p[u]
                return u
            cycles=0
            for u in A:
                for d in (0,1):
                    v=nb(u,d)
                    if v in A and (u in marks or v in marks):
                        a,b=root(u),root(v)
                        if a==b:cycles+=1
                        else:p[a]=b
            print('relaxed strip SAT, physical forced cycles',cycles,flush=True)
            if H==37 and not cycles and mode==0 and not sels:
                assert all((pt(203,r,s+k) in marks)==(pt(245,r,s+ell) in X)
                           for r in range(H) for k,ell in ((0,0),(36,78)))
                T,P,S=table(203);adj={u:[] for u in A};ok={}
                for u in A:
                    i,j=u;square=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
                    if all(q in A for q in square):
                        assert P(T(1,i,j))[sum((q in marks)<<k for k,q in enumerate(square))]==0
                    ds=[d for d in range(4) if min(nb(u,d))>=0 and max(nb(u,d))<203]
                    adj[u]=[nb(u,d) for d in ds if nb(u,d) in A and (u in marks or nb(u,d) in marks)]
                    if all(nb(u,d) in A for d in ds):
                        m=int(u in marks)+sum((nb(u,d) in marks)<<(1+k) for k,d in enumerate(ds))
                        ok[u]={nb(u,d) if d>=0 else None for d in (-1,*ds)
                               if S(T(0,i,j),tuple(ds),d,False,False)[m]==0}
                unseen=set(A)
                while unseen:
                    a=unseen.pop();q=[a]
                    for a in q:
                        for b in adj[a]:
                            if b in unseen:unseen.remove(b);q.append(b)
                    for root0 in q:
                        par={root0:None};order=[root0]
                        for u in order:
                            for v in adj[u]:
                                if v not in par:par[v]=u;order.append(v)
                        if all(u not in ok or par[u] in ok[u] for u in q):break
                    else:raise AssertionError('no valid orientation')
                print('37 lanes: both physical end masks, zero patch/star charges and acyclic orientation replayed')
        else:print('UNKNOWN')
        return st
    return window(203,'rim',1,small,domain=A,want=False,emit_graph=emit)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
