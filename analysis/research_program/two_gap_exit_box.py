"""An ordinary short-arc exit, with true matching and isolated north teeth."""
from itertools import product
from pathlib import Path
import sys,subprocess
from .odd_frames import frame
from .defect_window import window,table
from .saturated_tile_phase import axis_clauses

def test(width,height,d,edge,seconds,merge=None,distances=None,tables=None,heading=0):
    n=next((int(s[7:]) for s in sys.argv if s.startswith('--side=')),329)
    assert n>=119 and (n-119)%42==0
    lo={'flat':d-width//2,'left':0,'right':n-width}[edge];hi=lo+width
    assert 0<=lo<hi<=n and height<n-6 and 3<=d<n-3
    rg=next((s[8:].split(':') for s in sys.argv if s.startswith('--exits=')),None)
    exits=distances if distances is not None else list(range(int(rg[0]),int(rg[1])+1,int(rg[2]))) if rg else [d]
    if heading:assert edge=='flat' and merge is not None and len(exits)==1
    charged=lo<=d<hi and not heading
    assert all(((lo<=e<hi and not heading)==charged) and 3<=e<n-3 for e in exits)
    dom=set(product(range(height),range(lo,hi)));m=frame(n,(0,0,1,1))
    axis=next((int(s[7:]) for s in sys.argv if s.startswith('--axis=')),0)
    bond='--bond-only' in sys.argv
    fstem=Path(f'target/exit_box_{edge}_{d}_{width}_{height}_paths'+(f'_axis{axis}' if axis else '')+('_'+'to'.join(rg) if rg else '')+('_bond' if bond else '')+(f'_n{n}' if n!=329 else ''))
    def emit(f,bit,flags,arc,sheet):
        assert set(flags)==({('s',0,e) for e in exits} if charged else set())
        for u,b in sorted(m.items()):
            if u in dom:f.append([bit(*u)*(1 if b else -1)])
        from .defect_window import DIR
        for e in exits:
            guard=[-flags['s',0,e]] if len(exits)>1 else []
            parent={(0,0):-1,(0,e):1};todo=list(parent)
            for i,j in todo:
                for s,(a,b) in enumerate(DIR):
                    v=i+a,j+b
                    if v in m and min(*v,n-1-v[0],n-1-v[1])==0 and v not in parent and (m[i,j] or m[v]):
                        parent[v]=(s+2)%4;todo.append(v)
            assert len(parent)==4*n-4
            for u,s in parent.items():
                if heading and u[0]==0:s=0 if heading>0 else 2
                if u in dom and s>=0 and (u[0]+DIR[s][0],u[1]+DIR[s][1]) in dom:f.append(guard+[arc(*u,s)])
            for j in range(max(3,lo),min(hi,n-3)):
                if heading or j!=e:f.append(guard+[-bit(2,j),arc(2,j,3)])
        # Allocate mark bits and names for local axes before creating colors.
        for i,j in dom:bit(i,j)
        if bond:
            assert axis in (1,2)
            for i,j in sorted(dom):
                if i%3!=2 or j%3!=2 or min(i,j,n-1-i,n-1-j)<14:continue
                for delta in (-1,1):
                    u=(i+delta,j) if axis==2 else (i,j+delta)
                    if u in dom:f.append([-bit(i,j),-bit(*u)])
        else:
            axisvar=f.nv+1;axis_clauses(f,bit,n,dom)
            if axis:
                assert axis in (1,2)
                f.append([axisvar if axis==1 else -axisvar]) # 1 forbids horizontal center bonds
        top=f.nv;bits=(width+height*2).bit_length()
        def col(i,j,h):return top+1+((i-2)*width+j-lo)*bits+h
        for i,j in sorted(dom):
            if min(i,j,n-1-i,n-1-j)<2:continue
            v=bit(i,j)
            if i==2 or not charged and j in (2,n-3):
                code=j-lo if i==2 else width+i+(height if j==n-3 else 0)
                for h in range(bits):f.append([-v,col(i,j,h)*(1 if code>>h&1 else -1)])
            for x,y in ((i+1,j),(i,j+1)):
                if (x,y) not in dom or y>n-3:continue
                for h in range(bits):
                    a,b=col(i,j,h),col(x,y,h)
                    for g in (v,bit(x,y)):f.extend([[-g,-a,b],[-g,a,-b]])
        if merge is not None:
            assert axis==1 and not bond
            merge(f,axisvar,{axisvar+1+h:i for h,i in enumerate(range(14,n-14,3))},bit,dom,exits,charged)
            return
        p=fstem.with_suffix('.cnf');pr=p.with_suffix('.drat');f.to_file(str(p))
        with fstem.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            out=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in out;p.with_suffix('.check').write_bytes(out);print(fstem,'s VERIFIED')
        elif rc==10:print(fstem,'SAT (local only)')
        else:assert rc==0;print(fstem,'UNKNOWN')
    window(n,'rim',height,tables or table(n),domain=dom,exit_only=True,want=charged,defects={('s',0,e) for e in exits},emit_graph=emit,matching=True)
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],int(sys.argv[5]))
