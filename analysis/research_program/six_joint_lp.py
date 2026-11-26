"""Sparse physical six-row automaton; solve and replay via core and event prices."""
from .full_top_transfer import *
from .six_support import advance6,masks6,setup
from .patch_square import relaxation


def core():
    n,ns,A,b,obj=polynomial(5,3,1)
    A.extend([(row(n,ns,template()),'>='),(pinned_overlap(n,ns),'=')]);b.extend([(1,0,0),(0,0,0)])
    for cs in agreements(n,ns,True)+cuts(n,ns)[0]:A.append((cs,'='));b.append((0,0,0))
    A.append((certificate(n,ns,load()),'>='));b.append((1,0,0))
    labels,_,_=setup(109,ns,{})
    return ns,A,[v+28*w+378*z for v,w,z in b],obj,labels


@lru_cache(None)
def layer(states):
    arcs=[];dest=set()
    for s in states:
        for c in range(64):
            d=advance6(s,c)
            if d is None:continue
            dest.add(d);arcs.append((s,c,d,masks6(*s[:2],c)))
    return arcs,tuple(sorted(dest))


def solve_disk():
    import highspy as H
    import numpy as np
    ns,A,rhs,obj,labels=core()
    xs=list(ns.values());ci={x:i for i,x in enumerate(xs)};N=len(xs)
    keys=list(labels);ei={k:len(A)+i for i,k in enumerate(keys)}
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('log_file','target/six_joint_highs.log')
    h.setOptionValue('solver','ipm')
    h.setOptionValue('output_flag',True)
    h.addVars(N,np.zeros(N),np.full(N,H.kHighsInf))
    h.changeColsCost(N,np.arange(N),[obj.get(x,0) for x in xs])
    for (cs,op),b in zip(A,rhs):
        h.addRow(b if op!='<=' else -H.kHighsInf,b if op!='>=' else H.kHighsInf,len(cs),
                 [ci[x] for x,w in cs],[w for x,w in cs])
    for k in keys:h.addRow(0,0,1,[ci[labels[k]]],[-1.])
    states=((0,0,tuple(range(6))),);fi={}
    for j in range(109):
        for s in states:fi[j,s]=len(ei)+len(A)+len(fi)
        _,states=layer(states)
    b=np.zeros(len(fi));b[0]=1;h.addRows(len(fi),b,b,0,[],[],[])
    states=((0,0,tuple(range(6))),)
    for j in range(109):
        arcs,states=layer(states);nr=len(arcs);terms=1+(j<108)+4*(j>=2)
        idx=np.zeros((nr,terms),dtype=np.int32);w=np.ones((nr,terms))
        if j<108:w[:,1]=-1
        for k,(s,c,d,ms) in enumerate(arcs):
            idx[k,0]=fi[j,s]
            if j<108:idx[k,1]=fi[j+1,d]
            if j>=2:idx[k,-4:]=[ei[axis(j-2,107),r,m] for r,m in enumerate(ms)]
        h.addCols(nr,np.zeros(nr),np.zeros(nr),np.full(nr,H.kHighsInf),nr*terms,
                  np.arange(0,nr*terms,terms,dtype=np.int32),idx.ravel(),w.ravel())
    h.setMaximize();h.run()
    assert h.getModelStatus()==H.HighsModelStatus.kOptimal
    s=h.getSolution()
    np.savez_compressed('target/six_joint_sol.npz',p=np.array(s.col_value),y=np.array(s.row_dual))
    print('candidate',h.getObjectiveValue(),flush=True)


if __name__=='__main__':solve_disk()
