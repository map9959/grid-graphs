"""Forward-partition replay of opposite-half forest window certificates."""
from .coupled_mask_grid import encode
from .synchronous_grid import solve,unpack
from . import fan_speed_cover,rooted_window_speed

def native(g,P,W,H,gaps,rf,south=False,*,sealed=(),sides=3):
    assert not gaps and (not sealed or set(sealed)==set(range(W)))
    opt=[f'--height={H}',f'--sides={sides}',f'--root-from={rf}']
    if not south:opt.append('--open-south')
    if sealed:opt.append('--sealed-north')
    z=solve(encode(W,P.items,g),opt)
    if not z:return False
    ds,grid=z;ids=[P.intern(frozenset(map(unpack,d))) for d in ds];g[:]=[ids[i] for i in grid]
    return True

def main():
    from unittest.mock import patch
    with patch.object(rooted_window_speed,'prune',native),patch.object(fan_speed_cover,'prune',native):
        rooted_window_speed.audit();fan_speed_cover.audit()
if __name__=='__main__':main()
