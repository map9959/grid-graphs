"""Common crop masks in several exchangeable one-gap frames (positive test if open)."""
from .coupled_mask_grid import instance,encode
from .coupled_two_gap import instance as physical

def common(k,q,axis,frames):
    tabs,grid=instance(axis,k,q,as_tables=True)
    for one in frames:
        extra,ei=physical(k,q,one=one,axis=axis,as_tables=True)
        ids={};ds=[];out=[]
        for p,r in zip(grid,ei):
            key=p,r
            if key not in ids:ids[key]=len(ds);ds.append(tuple(set(tabs[p]).intersection(extra[r])))
            out.append(ids[key])
        tabs,grid=ds,out
    return encode(k,tabs,grid)
