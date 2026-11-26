"""Cross-check the actual four-port bulk glues against an independent graph."""
from functools import lru_cache
from unittest.mock import patch
from . import ordered_ports
from .three_port_glue_audit import reference

def check():
    glue=ordered_ports.glue;counts=[0,0]
    @lru_cache(None)
    def checked(L,R,trees,p,cap,lineage=False):
        ports=[*range(L),*range(cap,cap+R)]
        groups=[]
        for j in ports:
            owner,=[k for k,t in enumerate(trees) if t&(4<<j)]
            groups.append(owner)
        teeth=[bool(t&2) for t in trees]
        independent=reference(p,groups,teeth)
        assert glue(L,R,trees,p,cap,True)==independent
        if max(L,R)==4:counts[independent is not None]+=1
        if independent is None:return
        return independent if lineage else independent[0]
    with patch.object(ordered_ports,'glue',checked):
        for axis in (1,2):
            for d,phase in ((0,None),(-4,-4),(5,4)):
                ordered_ports.relation(axis,7,cap=4,phase=phase,offset=d,ends=True,exact=True)
    assert min(counts)>0
    print('distinct catalogue glues using a fourth port:',counts[0],'rejected;',counts[1],'accepted')
if __name__=='__main__':check()
