"""Symbolic rod contacts and cardinality of the alternating 56+42t family."""
from z3 import Ints,And,Or,If,Not,Abs,Solver,unsat,simplify


def prove():
    t,a,b,r,c,s,d=Ints('t a b r c s d')
    n=56+42*t;k=18+14*t;F=9+7*t;H=F+3
    def check(bad):
        z=Solver();z.add(t>=0,bad);assert z.check()==unsat,z.model()
    def rod(K,a,r,c):
        if K=='B':return And(a==0,r==0,c>=3,c<n)
        if K=='W':return And(a>=0,a<=k-2,c==3*a+2,r>=2,r<=2+If(a<k-2-a,a,k-2-a))
        left=K=='L'
        start=If(a==0,0,a+3) if left else a+2
        return And(a>=0,a<=F-int(left),r>=start,r<=H,c==(3*a if left else n-1-3*a))
    h=r-2;L=3*(F-1)
    marked=Or(And(r==0,Or(c==0,c>=3)),And(r==1,c==0),
              And(r>=2,h<F,Or(c==0,And(c%3==0,c<3*h),
                               And(c%3==2,c>=2+3*h,c<n-5-3*h),
                               And((n-1-c)%3==0,c>=n-1-3*h))),
              And(h>=F,Or(And(c%3==0,c<=L),And((n-1-c)%3==0,c>=L+4))))
    rods=Or(rod('B',0,r,c),rod('W',c/3,r,c),rod('L',c/3,r,c),rod('R',(n-1-c)/3,r,c))
    check(And(r>=0,r<=H,c>=0,c<n,marked!=rods))
    for j,A in enumerate('BWLR'):
        for C in 'BWLR'[j:]:
            contact=And(rod(A,a,r,c),rod(C,b,s,d),Or(A!=C,a<b),Abs(r-s)+Abs(c-d)<=2)
            want=False
            if (A,C)==('B','W'):want=And(a==0,b>=1,b<=k-2,r==0,s==2,c==3*b+2,d==c)
            if (A,C)==('B','R'):want=And(a==0,b==0,r==0,s==2,c==n-1,d==c)
            if (A,C)==('W','L'):want=And(a==0,b==0,r==2,s==2,c==2,d==0)
            check(contact!=want)
    B=5+5*t
    check(n-7-F!=7*B+5)
    count=(n-2)+1+(F*k+1)+B*(7*(k+1)+1)+5*(k+1)+1+(2*n+1)
    upper=3*k*k+7*k-1-2*t
    assert simplify(count-upper,som=True).as_long()==0
    check((23-2*k)/14!=-1-2*t)
    print('all t>=0: prefix decomposition and all ten contact predicates checked; count minus upper = 0')


if __name__=='__main__':prove()
