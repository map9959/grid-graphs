"""Full southwest completion with only a disjunction of band ends prescribed."""
from itertools import product
from pathlib import Path
import gzip,json,sys
from .depth_two_far_quarter import run
from .extend_forest_28 import verify

def patterns(consensus=False):
    raw=gzip.decompress((Path(__file__).with_name('one_gap_projection_examples')/'long_quarters_5_5.gz').read_bytes())
    B=sorted((i,j) for i,j in product(range(245),repeat=2) if min(i,j,244-i,244-j)<8 or i<=101 or j>=143)
    X={u for u,b in zip(B,raw[2:],strict=True) if b>=5}
    masks={s:{(i,j):int((i,j) in X) for i in (s,s+78) for j in range(143,245)} for s in range(102,161)}
    if consensus:
        folder=Path(__file__).with_name('one_gap_projection_examples')
        for name in ('11_53','59_101','107_149','155_191'):
            data=gzip.decompress((folder/f'long_quarters_{name}.gz').read_bytes())
            marks={p for p,h in zip(B,data[2:],strict=True) if h>=5}
            masks={s:{p:v for p,v in m.items() if (p in marks)==v} for s,m in masks.items()}
    return masks

def test(lo,hi,a,b,seconds,crop=0,shared=0,block=0):
    n=245;assert 5<=lo<=hi<=191 and lo%6==hi%6==5 and 102<=a<=b<=160
    masks=patterns(bool(shared));starts=range(a,b+1,3 if shared else 1)
    dom={(i,j) for i,j in product(range(n),repeat=2) if crop!=1 or
                         min(i,j,n-1-i,n-1-j)<8 or i>=100 or j<=101}
    forest={(i,j) for i,j in dom if min(i,j,244-i,244-j)<8 or i<=101 or j>=143} if crop==2 else None
    cases=Path(f'target/southwest_ports_{lo}_{hi}_{a}_{b}'+{0:'',1:'_omitNE',2:'_SWlocal'}[crop]+('_shared' if shared else '')+{0:'',1:'_blocked',2:'_axis'}[block])
    def extra(f,bit,flags):
        assert set(flags)=={('s',2,d) for d in range(lo,hi+1,6)}
        top=f.nv
        sels=list(range(top+1,top+len(starts)+1)) if not block else []
        if block:
            assert not shared
            for s in starts:f.append([-bit(*u) if x else bit(*u) for u,x in masks[s].items()])
        else:
            f.append(sels)
            for s,v in zip(starts,sels):
                for u,x in masks[s].items():f.append([-v,bit(*u) if x else -bit(*u)])
        for i,j in product(range(102,237),range(8,143)):
            f.append([bit(i,j),bit(i+1,j),bit(i-1,j),bit(i,j+1),bit(i,j-1)])
        if block==2:
            from .saturated_tile_phase import axis_clauses
            assert crop==0
            axis_clauses(f,bit,n)
        meta={'flags':{d:flags['s',2,d] for d in range(lo,hi+1,6)},
              'ports':dict(zip(starts,sels)), 'marks':[bit(*u) for u in sorted(dom)]}
        cases.with_suffix('.ids.gz').write_bytes(gzip.compress(json.dumps(meta,separators=(',',':')).encode(),mtime=0))
        print('SW coverage clauses',135**2,'end pairs',len(sels),'star distances',len(flags),'frame/arm words',16,flush=True)
    def replay(w,star,X,out):
        hits=[s for s in starts if all((u in X)==bool(v) for u,v in masks[s].items())]
        assert bool(hits)==(not block)
        if crop==1:
            from .shorten_245_star import audit
            from .slit_star_transfer import frame_path
            from .defect_window import table
            v,e,cc=audit(n,dom,X,out,star,None,table(n),frame_path(n,w),(244,244))
            print('omit NE only; replay frame',w,'star',star,'start(s)',hits,'edges',e,'cycles 0')
            return
        rows=[''.join('#' if (i,j) in X else '.' for j in range(n)) for i in range(n)]
        if crop==2:
            from .defect_window import table,DIR
            from .shorten_245_star import audit,nb
            from .slit_star_transfer import frame_path
            tab=table(n);T,P,S=tab
            audit(n,forest,X&forest,{u:d for u,d in out.items() if u in forest and nb(u,d) in forest},star,None,tab,frame_path(n,w),(244,244))
            edges=0;uncovered=[]
            for u in dom:
                ds=tuple(k for k in range(4) if nb(u,k) in dom)
                m=int(u in X)+sum((nb(u,k) in X)<<(h+1) for h,k in enumerate(ds))
                assert S(T(0,*u),ds,out.get(u,-1),u==(244,244),len(ds)==2)[m]==72*(u==star)
                if not m:uncovered.append(u)
                if max(u)<243:assert not P(T(1,*u))[sum(((u[0]+i,u[1]+j) in X)<<(3*i+j) for i,j in product(range(3),repeat=2))]
                for k in (0,1):
                    v=nb(u,k)
                    if v not in dom:continue
                    edge=u in X or v in X;edges+=edge
                    assert (out.get(u)==k)+(out.get(v)==k+2)==int(edge)
            assert uncovered==[star] and edges==60023 and len(X)==20240
            print('full-board local model replayed:',w,star,hits,'marks',len(X),'forced edges',edges)
            import gzip
            cases.with_suffix('.local.gz').write_bytes(gzip.compress(bytes([w,star[1]])+bytes(5*int(u in X)+1+out.get(u,-1) for u in sorted(dom)),mtime=0))
            return
        score=verify(rows);assert score[0]==score[-1]==20240
        Path('target/southwest_ports_245.tree').write_text('\n'.join(rows)+'\n')
        print('physical spanning tree',score)
    run(n,lo,hi,seconds,domain=dom,output=str(cases),extra=extra,replay=replay,turn_domain=forest)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
