"""DRAT bridge for a positive face/junction price discrepancy (exact dual prerequisite)."""
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from pysat.formula import CNF,IDPool
from .segment_face_turns import certify,geometry


def counter(f,p,vs):
    # Exact binary sum, not a one-sided cardinality encoding.
    digits=[]
    while vs:
        higher=[]
        while len(vs)>1:
            a=vs[-3:];del vs[-len(a):]
            s,c=p.id(),p.id();higher.append(c)
            for bits in product((0,1),repeat=len(a)):
                guard=[-x if v else x for x,v in zip(a,bits)]
                f.extend([guard+[s if sum(bits)%2 else -s],guard+[c if sum(bits)>=2 else -c]])
            vs.append(s)
        digits.append(vs[0]);vs=higher
    return digits


def replay(lo=51,hi=73):
    ub,scale,price=certify();assert 3647*scale-ub>0
    n=103;face,*_=geometry(n)
    f=CNF();p=IDPool();arc={};F={};E={};proof=[];on={}
    def disj(a):
        v=p.id();f.append([-v,*a]);f.extend([[-x,v] for x in a]);return v
    def conj(a):return -disj([-x for x in a])
    def mark(i,j):return p.id(('m',i,j))
    # The two measures are *not equated* in the CNF. Face bits read
    # marks; junction bits read the two candidate parent departures.
    for i,j in product(range(0,n,3),repeat=2):
        for t in (0,1):
            u,v=int(t==1),int(t==0)
            if max(i+3*u,j+3*v)>=n:continue
            left=[];right=[];bonds=[]
            for k in range(3):
                a,b=i+k*u,j+k*v;a1,b1=a+u,b+v
                fw=arc[a,b,t]=p.id();bw=arc[a1,b1,t+2]=p.id()
                h=disj([mark(a,b),mark(a1,b1)])
                f.extend([[-h,fw,bw],[-fw,h],[-bw,h],[-fw,-bw]])
                left.append(fw);right.append(bw);bonds.append(h)
            L,R=left[0],right[-1];w=i,j,t
            E[w]=disj([L,R]);F[w]=conj(bonds)
            f.extend([[-L,b] for b in left[1:]]+[[-R,b] for b in right[:-1]])
            # RUP: departures force their whole marked path. Conversely
            # if both end bonds point away from the two midpoints, those
            # two midpoints cannot orient the middle compulsory bond.
            proof.extend([[-L,F[w]],[-R,F[w]],[-E[w],F[w]],[E[w],-F[w]]])
    for (a,b,t),z in arc.items():
        for d in range(t):
            if (a,b,d) in arc:f.append([-z,-arc[a,b,d]])
    # Whole-board rational discrepancy >0 implies one rotation, face
    # and corner with a strictly larger face price than junction price.
    # For fixed observed marks this requires a signed bit mismatch.
    signs={}
    for tag,a,b,*_ in price:
        key=tag,a,b
        if key in signs:continue
        yes=set()
        for bits in product(range(2),repeat=3):
            for U,V in product(product(range(2),repeat=2),repeat=2):
                if price.get((*key,*bits,*U),0)>price.get((*key,*bits,*V),0):
                    # Only the inward horizontal bit enters the verified
                    # .#.. price; vertical discrepancies cannot pay it.
                    assert U[0]==0 and V[0]==1 and bits[:2]==(0,1)
                    yes.add((0,0))
        signs[key]=yes
    for i,j in product(range(0,n-1,3),repeat=2):
        for a,b in product((0,3),repeat=2):
            for t,positive in signs.get((face(i,j),a,b),()):
                w=(i+a,j,0) if t==0 else (i,j+b,1)
                key=w,positive
                if key in on:continue
                z=on[key]=p.id()
                f.extend([[-z,F[w] if positive else -F[w]],[-z,-E[w] if positive else E[w]]])
                proof.append([-z])
    f.append(list(on.values()));proof.append([])
    starts=[]
    for i in range(0,n,3):
        for t in (0,1):
            es=[E[(i,j,0) if not t else (j,i,1)] for j in range(0,n-1,3)]
            starts.extend([es[0],*[conj([-a,b]) for a,b in zip(es,es[1:])]])
    digits=counter(f,p,starts)
    with TemporaryDirectory(prefix='joint-price-',dir='target') as tmp:
        path=Path(tmp);cnf=path/'in.cnf';drat=path/'proof'
        with drat.open('w') as out:
            for row in proof:print(*row,0,file=out)
        with cnf.open('wb') as out:
            out.write(f'p cnf {f.nv} {len(f.clauses)+len(digits)}\n'.encode())
            for c in f.clauses:out.write((' '.join(map(str,c))+' 0\n').encode())
            offset=out.tell()
        for s in range(lo,hi+1):
            with cnf.open('r+b') as out:
                out.seek(offset)
                for k,z in enumerate(digits):out.write(f'{z if s>>k&1 else -z} 0\n'.encode())
                out.truncate()
            chk=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(drat)],capture_output=True)
            assert chk.returncode==0 and b's VERIFIED' in chk.stdout,(s,chk.stdout[-1000:])
            print('segments',s,'face/parent discrepancy UNSAT s VERIFIED',flush=True)
    return len(on),len(proof)


if __name__=='__main__':
    q,z=replay();print('signed mismatch alternatives',q,'DRAT additions',z)
