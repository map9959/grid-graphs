"""Replay the slit charges using parents of the actual padded rectangle forest."""
from .finite_cap_language import step,transfer
from .cap_vertex_arrows import transfer as vertices
from .cap_site_arrows import transfer as sites
from .comb_cap_transfer import construct
from .reflected_pitch_rank import ledger


def replay(cap):
    n=len(cap[0]);r=(n+2)//3;w=n+2
    rows=['.'+s+'.' for s in cap]+['.'*w]
    adj=[[] for _ in range(w*len(rows))]
    for y,s in enumerate(rows):
        for x,a in enumerate(s):
            u=y*w+x
            for v,b in ([(u+1,s[x+1])] if x+1<w else [])+([(u+w,rows[y+1][x])] if y+1<len(rows) else []):
                if a=='#' or b=='#':adj[u].append(v);adj[v].append(u)
    par={};roots=set()
    for root in [3*i+1 for i in range(r)]+[i for i,c in enumerate(''.join(rows)) if c=='#']+list(range(len(adj))):
        if root in par:continue
        roots.add(root);par[root]=-1;todo=[root]
        for u in todo:
            for v in adj[u]:
                if v!=par[u]:
                    assert v not in par
                    par[v]=u;todo.append(v)
    B=0;j=0;tapes=[]
    for t in range(r):
        drop=(3*t+1 not in roots);j+=drop
        edge='L' if not t else 'R' if t==r-1 else ''
        paid=0;left=[];right=[]
        for y,row in enumerate(rows[1:-1],1):
            def bit(x):return int(0<=x<w and row[x]=='#')
            m=sum(bit(3*t+i-1)<<i for i in range(5))
            def direction(x):return int(0<=x<w-1 and par[y*w+x]==y*w+x+1)
            a=(m&3)+4*direction(3*t-1);b=(m>>3)+4*direction(3*t+2)
            # Only two halo letters are emitted. To replay this *specific*
            # cap distinguish the hidden central bit as well.
            if y==1:s=(4,0,(0,0,0),(3 if drop else 2,0,0))
            s,z=step(s,m,a>>2,b>>2);paid+=z
            left.append(a);right.append(b)
        # Replay the blank end from the physical state.
        if len(rows)==2:s=(4,0,(0,0,0),(3 if drop else 2,0,0))
        m=s[0];e,z=step(s,0,0,0);assert 3 not in e[3]
        paid+=z+(14&~m).bit_count()+int(not(m&4))+2*e[3].count(1)
        for local in (transfer,vertices,sites):
            arcs,ends=local(edge,drop);states={(0,0)}
            for a,b in zip(left,right):
                states={(v,c+z) for u,c in states for x,y,v,z in arcs[u] if (a,b)==(x,y) and c+z<=paid}
            assert any(c+ends.get(u,10**7)==paid for u,c in states)
        if tapes:assert tapes[-1]==left
        tapes.append(right);B+=paid
    bonus=sum(row.count('#')-r for row in cap[1:])
    assert ledger(cap)==(0,j) and 4*bonus==2*r+2*j-B
    return j,bonus,B


if __name__=='__main__':
    count=0
    for m in range(1<<12):
        c=['#..#']+[''.join('#' if m>>(4*y+x)&1 else '.' for x in range(4)) for y in range(3)]
        if ledger(c)[0]:continue
        replay(c);count+=1
    print('width-four depth-three eligible physical caps',count)
    rows=construct(103,4)
    for c in [rows[2::-1],rows[2:],rows[96:]]:
        print('width 103, depth',len(c)-1,'j,b,B',replay(c))
