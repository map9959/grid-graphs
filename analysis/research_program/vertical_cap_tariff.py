"""Independent inventory of an open prefix between wired teeth and a floating full bar."""
from .comb_cap_transfer import construct

def inventory(rows,vertical=True):
    # Append bottom blank and full rows implicitly. Row 0 outside the
    # prefix is the prescribed pitch; row indices in rows are all free.
    w=len(rows[0]);r=w//3;h=len(rows);assert w==3*r and h>=2
    marks={(y,x) for y,row in enumerate(rows) for x,c in enumerate(row) if c=='#'}
    p=list(range(h*w));cycles=[0]*(h*w)
    def rt(i):
        while p[i]!=i:p[i]=p[p[i]];i=p[i]
        return i
    for y in range(h):
        for x in range(w):
            for a,b in ((y,(x+1)%w),(y+1,x)):
                if a>=h or not ({(a,b),(y,x)}&marks):continue
                i,j=rt(y*w+x),rt(a*w+b)
                if i==j:cycles[i]+=1
                else:p[i]=j;cycles[j]+=cycles[i]
    top={rt(3*i) for i in range(r)}
    bot={x for x in range(w) if (h-1,x) in marks};t=len(bot)
    lower={rt((h-1)*w+x) for x in bot}
    assert len(top)==r and len(lower)==t and not top&lower
    roots={rt(i) for i in range(w*h)}
    assert all(cycles[i]==0 for i in top|lower) and all(cycles[i]<=1 for i in roots)
    s=sum(cycles[i]==0 for i in roots-top-lower)
    runs=sum((y-1,x) not in marks and (y,(x-1)%w) not in marks for y,x in marks)
    T=sum(y==0 for y,x in marks);E=runs-T-t
    b=len(marks)+w-(h+2)*r
    assert 3*b==2*r-t-E-s
    # Add actual marked virtual teeth before counting clipped run
    # neighborhoods. Their old contact components are still distinct.
    aug=marks|{(-1,x) for x in range(0,w,3)}
    endpoint=join=isol=isol0=0
    for y in range(-1,h):
        for x in range(w):
            west=((y,(x-1)%w) in aug);east=((y,(x+1)%w) in aug)
            north=(y-1,x) in aug;south=(y+1,x) in aug
            if (y,x) in aug:
                if x%3==0 and (west or east):endpoint+=int(west!=east)
                elif x%3==0 and y!=-1 and not north:endpoint+=2
            else:
                join+=int(x%3!=0 and (west and east or north and south))
                if not any((west,east,north,south)):isol+=1;isol0+=int(x%3==0)
    X=s-isol;assert X>=0
    bill=t-sum(x%3==0 for x in bot)+endpoint+join+isol+isol0+2*X
    assert 4*b==2*r-bill
    print('endpoint bill (shifted bottom, central endpoints, joins, isolates, central isolates, other trees)',
          (sum(x%3!=0 for x in bot),endpoint,join,isol,isol0,X),flush=True)
    # Allocate blank rows separately inside each centered pitch triple.
    # Every surplus left over is a real join of two different runs.
    joins=0
    for x in range(0,w,3):
        cols=[(x-1)%w,x,(x+1)%w]
        masks=[sum(((y,c) in marks)<<k for k,c in enumerate(cols)) for y in range(h)]
        first=masks.index(0);used=set()
        for y,v in enumerate(masks):
            if v in (3,6,7):
                claims={y+1} if v!=7 else {y-1,y+1}
                assert all(0<=i<h and masks[i]==0 for i in claims) and not claims&used
                used.update(claims)
            elif v==5:joins+=1
        if first in used:assert masks[first+1]==7;joins+=1
    assert b<=joins<=E
    if vertical:
        assert all((y,(x+1)%w) not in marks for y,x in marks)
        doubles=0;zeros=0
        for x in range(0,w,3):
            cols={(x-1)%w,x,(x+1)%w}
            counts=[sum((y,c) in marks for c in cols) for y in range(h)]
            assert 0 in counts and max(counts)<=2
            doubles+=counts.count(2);zeros+=counts.count(0)
        assert b==doubles-zeros+r and doubles<=E and E+s>=2*(r-t) and 7*b<=2*r
    print('pitch groups',r,'bonus',b,'bottom teeth',t,'run joins',joins,'other runs',E,'other tree components',s,flush=True)

if __name__=='__main__':
    a=[l[30:60] for l in construct(193,4)[-7:-2]]
    inventory(a,False)
    # Thin the comb's five-mark horizontal bar to alternating teeth.
    b=list(a);k=b[-2].index('#####');b[-2]=b[-2][:k]+'#.#.#'+b[-2][k+5:]
    inventory(b)
