"""Physically execute arbitrary-length sparse-hole repairs in opposite aligned wings."""
from .sparse_spoke_tile import initial,advance,refines
from .extend_forest_28 import verify
from .comb_cap_transfer import construct
from . import alternating_spoke_tile as alt

class Forest:
    def __init__(self,n):
        self.n=n;self.p=list(range(n*n))
    def root(self,z):
        i=z[0]*self.n+z[1]
        while self.p[i]!=i:self.p[i]=self.p[self.p[i]];i=self.p[i]
        return i
    def join(self,a,b):
        i,j=self.root(a),self.root(b)
        if i==j:return False
        self.p[i]=j;return True

def graph(rows,omit):
    n=len(rows);F=Forest(n)
    for i in range(n):
        for j in range(n):
            for u,v in ((i+1,j),(i,j+1)):
                if u>=n or v>=n or rows[i][j]==rows[u][v]=='.':continue
                if ((i,j),(u,v)) not in omit:assert F.join((i,j),(u,v))
    return F

def replace_word(word,holes):
    old={s:z for s,z in initial(False).items() if s[0]==word[0]}
    dp=old.copy();pred=[]
    for y,v in enumerate(word[1:],1):
        old={s:z for s,z in advance(old,y in holes).items() if s[1]==v}
        step={};dp=advance(dp,False,step);pred.append(step)
    assert len(old)==1
    (a,b,q),score=next(iter(old.items()))
    val,key=max((z,s) for s,z in dp.items() if s[:2]==(a,b) and refines(s[2],q))
    assert val>=score
    out=[key[1]]
    for step in reversed(pred):key=step[key];out.append(key[1])
    return out[::-1],val-score

def replace_three(word,holes):
    old={s:z for s,z in alt.init().items() if s[0]==word[0]}
    dp=old.copy();pred=[]
    for y,v in enumerate(word[1:],1):
        old={s:z for s,z in alt.step(old,y not in holes,0,1).items() if s[1]==v}
        past={};dp=alt.step(dp,True,0,1,past);pred.append(past)
    (a,b,q),score=next(iter(old.items()));assert q[-1]==q[0]
    val,key=max((z,s) for s,z in dp.items() if s[:2]==(a,b) and refines(s[2][:-1],q[:-1]))
    out=[key[1]]
    for past in reversed(pred):key=past[key];out.append(key[1])
    return out[::-1],val-score

def repair(rows,a,b,with_rows=False):
    n=len(rows);out=list(map(list,rows));base=list(map(list,rows));joins=[];wing_gain=0;tariff=0;clipped=0
    for flip in (False,True):
        def ix(x):return n-1-x if flip else x
        holes={y for y in range(a,b+1) if rows[y][ix(3)]=='.'}
        assert all(a+2<=y<=b-2 and y+1 not in holes for y in holes)
        for y in range(a,b+1):
            if out[y][ix(4)]=='#':
                assert y-1 in holes and y+1 in holes
                clipped+=1;out[y][ix(4)]=base[y][ix(4)]='.'
        word=[sum((rows[y][ix(x)]=='#')<<x for x in range(3)) for y in range(a,b+1)]
        wide=any(m&4 for m in word)
        new,gain=(replace_three if wide else replace_word)(word,{y-a for y in holes})
        u=sum(bool(word[y-a]&2) for y in holes)
        bound=max(0,(u-2)//2 if any(y+2 in holes for y in holes) else u-2)
        if wide:bound=(u+1)//2-2
        assert gain>=bound;tariff+=bound
        wing_gain+=gain
        for y,v in enumerate(new,a):
            for x in range(3):out[y][ix(x)]='#' if v>>x&1 else '.'
        for y in sorted(holes):
            out[y][ix(3)]='#';joins.append(((y,ix(3)),(y,ix(4)),(y,ix(5))))
    old=graph(base,set());rho=sum(old.join(u,v) for u,v,_ in joins)
    assert rho>=2*clipped
    stage=graph(out,{tuple(sorted((u,v))) for u,v,_ in joins});repairs=0
    for u,v,t in joins:
        if not stage.join(u,v):
            assert out[t[0]][t[1]]=='#';out[t[0]][t[1]]='.';repairs+=1
    out=[''.join(r) for r in out]
    tree=verify(out)
    delta=tree[0]-sum(r.count('#') for r in rows)
    assert delta==wing_gain+len(joins)-repairs-clipped and delta>=wing_gain+rho-clipped
    result=rho,tariff,wing_gain,clipped,repairs,delta,tree
    return (result,out) if with_rows else result

def checks():
    n=103
    for rooted,ys in ((False,[43]),(False,range(22,81,8)),(True,range(22,81,8))):
        r=list(map(list,construct(n,4)))
        for x,sgn in ((3,1),(n-4,-1)):
            for y in ys:
                r[y][x]='.'
                for j in (x-3*sgn,x+3*sgn):
                    r[y-1][j]=r[y+1][j]='.'
                    if not rooted:r[y][j]='.'
                r[y][x-2*sgn]=r[y][x+2*sgn]='#'
        r=[''.join(row) for row in r];start=verify(r)
        ans=repair(r,3,93)
        oldprice=[]
        for d,A,B,C in ((3,10,20,70),(6,6,24,126),(9,3,30,183)):
            for side in (r,[z[::-1] for z in r],list(zip(*r)),list(zip(*r[::-1]))):
                bad=sum(''.join(z[:d])!='#..'*(d//3) for z in side)
                cut=sum(z[d]=='.' for z in side)
                oldprice.append(A*bad-B*cut-C)
        print('rooted donors' if rooted else 'free donors','holes',2*len(ys),'start',start[0],
              'max previous side debit (thirtieths)',max(oldprice),
              'rank, certified wing, actual wing, clipped, cycle repairs, net, tree',ans)
    rows=list(map(list,construct(n,4)))
    for y in (31,59,76):
        for x in (0,6):rows[y][x]='.'
        rows[y-1][3]=rows[y+1][3]='.'
        rows[y][2]=rows[y][4]='#'
    rows=[''.join(r) for r in rows]
    print('two-apart holes with third-column marks',verify(rows),repair(rows,3,93))
    # A guarded hole with a core donor, but no independent join:
    # the x=5 mark is linked to x=6 and thence to the same north tree.
    rows=list(map(list,construct(n,4)));y=n//2
    rows[y][3]=rows[y-1][6]=rows[y+1][6]='.';rows[y][5]='#'
    rows=[''.join(r) for r in rows];res=repair(rows,3,93)
    assert res[:2]==(0,0)
    print('single inward return',verify(rows),'repair',res)

if __name__=='__main__':checks()
