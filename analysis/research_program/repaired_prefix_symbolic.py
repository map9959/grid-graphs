"""Parametric repair_53 prefix and count: refute counterexamples in integer arithmetic."""
from z3 import Ints,And,Or,If,Not,Abs,Solver,unsat,simplify


def prove(base=53):
    even_k=base in (38,44,50,56,62,68,74)
    assert even_k or base in (47,53,71)
    t,r,c,s,d,a,b=Ints('t r c s d a b')
    n=base+42*t;k=(base-2)//3+14*t;F=(base-2)//6+7*t
    m=F if even_k else (4 if base==71 else 3)+2*t
    M=3*m;H=F+4
    def check(name,bad):
        solver=Solver();solver.add(t>=0,bad)
        assert solver.check()==unsat,(name,solver.model())
    def rod(kind,a,r,c):
        if kind=='B':return And(a==0,r==0,2<=c,c<=n-4)
        if kind=='W':
            return And(a>=0,a<k,c==3*a+2,r>=2,
                       r<=2+If(a<k-1-a,a,k-1-a)-If(a<m,1,0))
        left=kind=='L'
        start=If(a==0,0,3+a-If(And(left,a<=m),1,0))
        return And(0<=a,a<=F-int(even_k and not left),c==(3*a if left else n-1-3*a),start<=r,r<=H)
    kinds='BWLR'
    # Independent row-based description of zipper_rails.build through the second
    # regular row, followed by exactly the edits from repair_53.repaired.
    L=3*(r-3);R=n-1-L
    original=Or(And(r==0,Or(c<n-3,c==n-1)),And(r==1,c==n-1),
                And(r==2,Or(c%3==2,c==n-1)),
                And(3<=r,r<F+3,Or(And(c<=L,c%3==0),And(c>=R,(n-1-c)%3==0),
                                     And(L+5<=c,c<R-4,c%3==2))),
                And(r>=F+3,Or(And(c<=3*F,c%3==0),And(c>=3*F+4,(n-1-c)%3==0))))
    plus=Or(And(r==1,c==0),And(r>=2,r<=2+m,c==3*(r-2)))
    minus=Or(And(r==0,c==1),And(r>=2,r<2+m,c==3*(r-2)+2))
    byrow=And(Or(original,plus),Not(minus))
    geometry=Or(rod('B',0,r,c),rod('W',c/3,r,c),rod('L',c/3,r,c),rod('R',(n-1-c)/3,r,c))
    check('rod decomposition',And(r>=0,r<=H,c>=0,c<n,byrow!=geometry))
    # Exactly the listed contacts of different rods; inspect actual marked
    # endpoints, not just a pair of projected column indices.
    cases=0
    for i,A in enumerate(kinds):
        for B in kinds[i:]:
            contact=And(rod(A,a,r,c),rod(B,b,s,d),Or(A!=B,a<b),Abs(r-s)+Abs(c-d)<=2)
            expected=False
            if (A,B)==('B','W'):
                expected=And(a==0,b>=1,b<k-1,r==0,s==2,c==3*b+2,d==c)
            elif (A,B)==('B','L'):
                expected=And(a==0,b==0,r==0,s==0,c==2,d==0)
            elif (A,B)==('W','L') and not even_k:
                expected=And(a==m,b==m,r==m+2,s==r,c==M+2,d==M)
            elif (A,B)==('W','R'):
                expected=And(a==k-1,b==0,r==2,s==2,c==n-3,d==n-1)
            check('contact '+A+B,contact!=expected);cases+=1
    print('all t>=0: row/rod mismatch UNSAT; unexpected or missing contacts UNSAT for',cases,'rod-family pairs')
    extra={38:1,56:2,47:2,71:1}.get(base,0)
    B,rem=divmod(base-8-(base-2)//6-extra,7)
    bands=B+5*t
    check('band lengths',n-8-F!=extra+7*bands+rem)
    if not even_k:check('distinguished cap rail',3*(F-bands)!=M)
    count=(n-2+1+k+1)+F*k+bands*(7*(k+1)+1)+(rem+extra)*(k+1)+int(rem>=3)+(3*k+3+n)+1
    deficit=-((23-2*((base-2)//3))//14)+2*t
    target=3*k*k+7*k-deficit
    assert simplify(count-target,som=True).as_long()==-int(base==56)
    check('upper floor',(23-2*k)/14 != -deficit)
    print('all t>=0: count minus certified upper floor =',-int(base==56))


if __name__=='__main__':
    import sys
    prove(int(sys.argv[1]) if len(sys.argv)>1 else 53)
