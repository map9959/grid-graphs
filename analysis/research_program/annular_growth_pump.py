"""Upper-bound every +3 one-gap perimeter replacement on 35+42t."""
import subprocess,re
from .annular_growth import graph,solve

def template(es):
    # Relative transitions are independent of physical vertex labels.
    last=list(range(len(es)))
    for i,vs in enumerate(es):
        for v in vs:last[abs(v)-1]=i
    live=[];rules=[]
    for i,vs in enumerate(es):
        edges=tuple(sorted((live.index(abs(v)-1),v<0) for v in vs));live.append(i)
        keep=tuple(h for h,j in enumerate(live) if last[j]>i)
        rules.append((edges,keep));live=[live[h] for h in keep]
    return rules

def prove(a,b):
    n=77;w,es,check=graph(n,1,a,b,True)
    rules=template(es);_,es2,_=graph(n+42,1,a,b,True);larger=rules[:]
    for x,y in reversed(check):larger[y+1:y+1]=rules[x+1:y+1]
    assert template(es2)==larger
    txt=[len(es),*[v for ls in es for v in (len(ls),*ls)],*([-1]*len(es)),*[p for pair in check for p in pair]]
    s=subprocess.run(['target/annular_frontier'],input=' '.join(map(str,txt)),text=True,capture_output=True,check=True)
    best=int(s.stdout.split()[0]);shifts=[]
    for _,y in check:
        z=re.search(rf'checkpoint {y} same \w+ dominated true shift (\d+)',s.stderr)
        if not z:print('no full-vector domination',a,b,s.stderr);return False
        shifts.append(int(z[1]))
    assert best<=6*n-4 and sum(shifts)<=252
    print('shift',a,b,'base',best,'per +42 upper increment',sum(shifts),shifts)
    return True
if __name__=='__main__':
    for a in range(4):
        for b in range(a,4):
            assert solve(35,1,a,b)<=206
            assert prove(a,b)
