"""Build and read in-memory full-mask domains; retain the labeled DP in the engine."""
from subprocess import run
from functools import lru_cache
from .coupled_mask_grid import instance,encode

def solve(data,options):
    output=run(['target/coupled_mask_grid','3','--rounds=12','--emit',*options],input=data,
               text=True,capture_output=True,check=True).stdout
    if output.splitlines()[-1].startswith('EMPTY'):return None
    assert output.splitlines()[-1]=='OPEN (joint strip fixed point)'
    ds,g=output.split('DOMAINS\n')[1].split('GRID\n')
    return [tuple(map(int,l.split())) for l in ds.splitlines()],list(map(int,g.splitlines()[0].split()))

@lru_cache(maxsize=32)
def domains(axis,k,q,gx,gy,block=1):
    return solve(instance(axis,k,q),[f'--gx={gx}',f'--gy={gy}',f'--block={block}',f'--period={block}'])

def unpack(p):return tuple((p>>(9*i))&511 for i in range(4))

def rectangle(grid,pool,W,H,gaps,rootfrom,south=False,ygaps=()):
    opts=[f'--height={H}',f'--root-from={rootfrom}']
    if gaps:opts.append(f'--gx={",".join(map(str,gaps))}')
    if ygaps:opts.append(f'--gy={",".join(map(str,ygaps))}')
    if not south:opts.append('--open-south')
    result=solve(encode(W,pool.items,grid),opts)
    if result is None:return False
    ds,g=result;ids=[pool.intern(frozenset(map(unpack,p))) for p in ds]
    grid[:]=[ids[x] for x in g]
    return True
