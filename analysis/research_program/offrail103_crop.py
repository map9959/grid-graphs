"""Cheaper necessary CNFs: price only atoms entirely in the selected strips."""
from pathlib import Path
import sys, subprocess
from .diagonal_score import generate

def test(depth,other,sec):
    n=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--side=')),103)
    assert n>=103 and (n-103)%9==0
    k=n//3;target=3*k*k+(16*k-7)//3
    limit=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--west-max=')),0)
    northlimit=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--north-max=')),0)
    span=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--row-span=')),None)
    section=next((tuple(map(int,s.split('=')[1].split(':'))) for s in sys.argv if s.startswith('--west-section=')),None)
    sitehex=next((s.split('=')[1] for s in sys.argv if s.startswith('--west-sites=')),None)
    signature=next((s.split('=')[1] for s in sys.argv if s.startswith('--west-signature=')),None)
    excepthex=next((s.split('=')[1] for s in sys.argv if s.startswith('--west-except=')),None)
    size=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--corner-size=')),None)
    if size:assert '--first' not in sys.argv  # positive earlier witnesses need not lie in the crop
    if section:assert 0<=section[0]<=section[1]<n
    from pysat.card import CardEnc
    def depths(arg):
        ends=list(map(int,arg.split(':')))
        return range(ends[0],ends[-1]+1) if ends[0]>=0 else ()
    north,west=depths(depth),depths(other)
    dom={(i,j) for i in range(n) for j in range(n)
         if i<=max(north)+4 or (west and j<=max(west)+4)}
    if size:
        assert size>=max(max(north),max(west,default=0))+2
        dom={(i,j) for i,j in dom if max(i,j)<size}
    remote='--remote-root' in sys.argv
    if remote:dom={(n-1-i,j) for i,j in dom}
    f,X=generate(n,target,dom)
    if remote:X=[X[n*(n-1-i)+j] for i in range(n) for j in range(n)]
    for ds,tr in ((north,False),(west,True)):
        if not tr and '--north-free' in sys.argv:continue
        if not ds:continue
        flags=[f.nv+1+i for i in range(len(ds))] if len(ds)>1 else []
        if flags:f.append(flags)
        for t,d in enumerate(ds):
            along=range(section[0],min(section[1]+1,size or n)) if tr and section else range(size or n)
            bits=[X[n*j+i if tr else n*i+j] for i in range(max(0,d-1),d+2) for j in along if j%3]
            guard=[-flags[t]] if flags else []
            if '--first' in sys.argv and not tr:
                for b in range(d):
                    f.append(guard+[X[n*i+j] for i in range(max(0,b-1),b+2) for j in range(n) if j%3])
            cap=limit if tr else northlimit
            if tr and excepthex:
                assert d==7 and signature and not sitehex
                for h in excepthex.split(','):
                    m=int(h,16);assert 0<=m<64
                    f.append(guard+[X[n*(7+b//3)+6+b%3]*(-1 if m>>b&1 else 1) for b in range(6)])
            if tr and signature:
                assert d==7 and not section and not cap
                for t_group in range(6):
                    vs=[X[n*j+i] for j in (1+3*t_group,2+3*t_group) if j<=16 for i in (6,7,8)]
                    if str(t_group) in signature:
                        if not signature.startswith('sub'):f.append(guard+vs)
                    else:f.extend([guard+[-x] for x in vs])
                if not sitehex:continue
            if tr and sitehex:
                assert d==7 and not section and not cap
                sel=[]
                for mask in map(lambda s:int(s,16),sitehex.split(',')):
                    assert 0<=mask<64
                    z=f.nv+1;sel.append(z)
                    for b in range(6):
                        x=X[n*(7+b//3)+6+b%3];f.append(guard+[-z,x if mask>>b&1 else -x])
                f.append(guard+sel);continue
            if tr and ('--count-rows' in sys.argv or span is not None):
                assert cap or span is not None
                used=[]
                coords=[]
                for j in along:
                    if j%3==0:continue
                    z=f.nv+1
                    for i in range(max(0,d-1),d+2):
                        f.append(guard+[-X[n*j+i],z])
                    used.append(z)
                    coords.append(j)
                bits=used
                if span is not None:
                    for a,r in enumerate(coords):
                        for b in range(a+1,len(coords)):
                            if coords[b]-r>span:f.append(guard+[-used[a],-used[b]])
                    if not cap:continue
            if cap:
                for c in CardEnc.atmost(bits,cap,top_id=f.nv).clauses:f.append(guard+c)
            else:
                for x in bits:f.append(guard+[-x])
    stem=Path(f'target/offrail{n}_crop_{depth}_{other}'.replace(':','to')+(f'_max{limit}' if limit else '')+(f'_northmax{northlimit}' if northlimit else '')+('_first' if '--first' in sys.argv else '')+('_rows' if '--count-rows' in sys.argv else '')+(f'_span{span}' if span is not None else ''));cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if section:
        stem=stem.with_name(stem.name+f'_section{section[0]}to{section[1]}');cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if size:
        stem=stem.with_name(stem.name+f'_size{size}');cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if sitehex:
        stem=stem.with_name(stem.name+'_sites'+sitehex.replace(',','-'));cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if signature:
        stem=stem.with_name(stem.name+'_sig'+signature);cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if excepthex:
        stem=stem.with_name(stem.name+'_except'+excepthex.replace(',','-'));cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if '--north-free' in sys.argv:
        stem=stem.with_name(stem.name+'_northfree');cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    if remote:
        stem=stem.with_name(stem.name+'_remote');cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    f.to_file(str(cnf))
    with stem.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(cnf),str(drat)],stdout=fd).returncode
    if rc==20:
        out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(drat)],capture_output=True,check=True).stdout
        assert b's VERIFIED' in out
        stem.with_suffix('.check').write_bytes(out);print(depth,other,'s VERIFIED')
    else:print(depth,other,'crop SAT' if rc==10 else 'UNKNOWN')
if __name__=='__main__':test(sys.argv[1],sys.argv[2],int(sys.argv[3]))
