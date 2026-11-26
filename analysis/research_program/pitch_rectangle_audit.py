"""Exact profile maxima with two fixed pitch ends and free lateral sides."""
from .collar_exchange_price import step

def audit(w,last):
    rim=sum(1<<i for i in range(0,w,3))
    def layer(states,choices):
        new={}
        for (old,p),score in states.items():
            for v in choices:
                if old>=0 and old&(v<<1|v>>1):continue
                z=step(w,old,p,v)
                if z is None:continue
                key=v,z[0];new[key]=max(new.get(key,0),score+v.bit_count())
        return new
    d=layer({(-1,tuple(range(w))):0},[rim])
    for h in range(2,last+1):
        m=max(layer(d,[rim]).values())
        assert m==h*rim.bit_count()
        if h<last:d=layer(d,range(1<<w))
    step.cache_clear()
    print('free-sided rectangle width',w,'heights 2 through',last,'match stripe count')

if __name__=='__main__':
    audit(4,14);audit(7,12)
