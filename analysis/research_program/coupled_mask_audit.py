"""Replay the all-isolate cover and positive/negative physical forest controls."""
from subprocess import run
from .coupled_mask_grid import instance,encode
from .joined_arm_budget import layout,row,spectrum,physical
from .absolute_ports import actual_hops

def execute(data,h=3,q=None):
    opts=[] if q is None else [f'--exit={q}']
    p=run(['target/coupled_mask_grid',str(h),*opts],input=data,text=True,check=True,capture_output=True)
    return p.stdout.splitlines()[-1]

def fixed(cols):
    k=len(cols);tabs=[];ids={};grid=[]
    for y in range(k-1):
        for x in range(k-1):
            p=(cols[x][y],cols[x][y+1],cols[x+1][y],cols[x+1][y+1])
            if p not in ids:ids[p]=len(tabs);tabs.append([p])
            grid.append(ids[p])
    return encode(k,tabs,grid)

def controls():
    k,H,_=layout(12);s=k-4*H//3
    bits,get=spectrum(7,4,1,True,0,True,s,True)
    cap=get((bits&-bits).bit_length()-1)
    cap=cap[:s+5]+[cap[s+4]]*168+cap[s+5:]
    region=[(*a,*b) for a,b in zip(cap,zip(*(row(k,q)[1] for q in reversed(range(H)))))]
    start=k-len(region[0])
    assert physical(region,start,k,1,True,require_roots=True)[1]==0
    cols=[(0,)*k]*start+list(zip(*region))
    peak=max(sum(bool(actual_hops(a>>3,b)) for a,b in zip(c,d)) for c,d in zip(cols,cols[1:]))
    assert peak>5 and execute(fixed(cols)).startswith('OPEN')
    print('side 623 rooted region with blank west padding: accepted, peak',peak,'hops')
    # Every tile pair has a common global assignment. Its single
    # marked line nevertheless joins west and east teeth.
    k=39;bad=[([0]*8+[73]+[0]*(k-9)) for _ in range(k)]
    assert execute(fixed(bad)).startswith('EMPTY')
    print('two-tooth horizontal line: rejected')
    # The same ordinary bridge line is illegal with the wrong exit but
    # is a singly attached component after omitting the designated tooth.
    k=39;q=19;bridge=[[0]*k for _ in range(k)]
    bridge[q]=[48]+[56]*(k-2)+[24]
    data=fixed(bridge)
    assert execute(data,q=q).startswith('OPEN') and execute(data,q=q+1).startswith('EMPTY')
    from .coupled_mask_check import check
    assert not check(1,k,'bridge control',data=data,q=q)
    assert check(1,k,'incorrect exit control',data=data,q=q+1)

def audit():
    run(['rustc','--edition=2021','-O','src/bin/coupled_mask_grid.rs','-o','target/coupled_mask_grid'],check=True)
    controls()
    for axis,interval,pos in ((1,(1,103),191),(1,(104,154),188),(1,(155,205),204),(2,(1,205),161)):
        ans=execute(instance(axis,207,interval))
        print(axis,interval,ans,flush=True)
        assert ans==f'EMPTY h=3 pass=0 horizontal=false start={pos}'
if __name__=='__main__':audit()
