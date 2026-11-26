"""Audit the translating exit cover and replay the key two-gap certificates."""
from functools import lru_cache
import hashlib,subprocess,sys
from pathlib import Path
from .odd_frames import frame,DIR

PROOFS={
    'exit_box_flat_164_87_65_paths_axis2_bond':'840bb93cadcd25e6b91cdd8b0c443903a354cba6465691ec79dec8e7eeaa6513',
    'exit_box_left_32_104_74_paths_axis2_5to59to3_bond':'852deeb28da21efbe15c10b7e0aae8b650150c073cacf77cfbbc45b074d172b6',
    'exit_box_right_296_104_74_paths_axis2_269to323to3_bond':'37807370cafb60105f03772ce2915ba00c23ea578f286f24e18f09d072798990',
    'two_gap_rowlink_left':'27883342b748b942eb5a9d52ea0049a0f8fc3ead5b20d51e37978817c4fb0cf5',
    'two_gap_rowlink_right':'5108d1655fd5d626a9033a0837ab5884cc4b0a35de508d6c7979d199c46450a8',
}

@lru_cache(None)
def boundary(n):
    return frame(n,(0,0,1,1))

@lru_cache(None)
def arrows(n,d):
    q=[(0,0),(0,d)];p={q[0]:-1,q[1]:1};m=boundary(n)
    for i,j in q:
        for t,(a,b) in enumerate(DIR):
            z=i+a,j+b
            if z in m and min(*z,n-1-z[0],n-1-z[1])==0 and z not in p and (m[i,j] or m[z]):
                p[z]=(t+2)%4;q.append(z)
    assert len(p)==4*n-4;return p

def code(x,n):
    # More than the physical star/patch depth and the deep-axis threshold.
    return min(x,16),min(n-1-x,16),x%3

def box(n,d,width,height,lo,reflo,refd):
    assert all(code(lo+y,n)==code(reflo+y,329) for y in range(-2,width+2))
    assert all(code(i,n)==code(i,329) for i in range(-2,height+2))
    # All interiors agree in end distances or in bulk residues. Test
    # perimeter marks, directions and the exit's local position separately.
    a,b=boundary(n),boundary(329);p,q=arrows(n,d),arrows(329,refd)
    assert (d-lo if lo<=d<lo+width else None)==(refd-reflo if reflo<=refd<reflo+width else None)
    for j in range(width):
        for i in (0,1):
            u=i,lo+j;v=i,reflo+j
            assert a[u]==b[v] and p.get(u)==q.get(v)
    for i in range(height):
        for j in (0,1,width-2,width-1):
            u=i,lo+j;v=i,reflo+j
            assert a.get(u)==b.get(v) and p.get(u)==q.get(v)

def cover(n):
    cases=[0]*3
    for d in range(5,n-5,3):
        end=n-1-d
        if d<=59:box(n,d,104,74,0,0,d)
        elif end<=59:box(n,d,104,74,n-104,329-104,328-end)
        else:box(n,d,87,65,d-43,164-43,164)
        if d<=104:
            box(n,d,150,81,0,0,d);box(n,d,104,74,n-104,225,53);cases[0]+=1
        elif end<=104:
            box(n,d,104,74,0,0,275);box(n,d,150,81,n-150,179,328-end);cases[1]+=1
        else:
            box(n,d,104,74,0,0,164);box(n,d,104,74,n-104,225,164)
            box(n,d,87,65,d-43,121,164);cases[2]+=1
    print('side',n,'axis-2 all exits covered; axis-1 left/right excluded, flat open',cases)

def run():
    for n in (329,371,413):cover(n)
    for name,h in PROOFS.items():
        p=Path('target',name+'.cnf')
        with p.open('rb') as fd:assert hashlib.file_digest(fd,'sha256').hexdigest()==h
        data=p.with_suffix('.check').read_bytes()
        if '--drat' in sys.argv:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],check=True,capture_output=True).stdout
        assert b's VERIFIED' in data
        print(name,*[s for s in data.decode().splitlines() if 'resolution steps' in s or 's VERIFIED' in s])
if __name__=='__main__':run()
