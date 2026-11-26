"""Additional finite tests for 665 after the synchronized front and two-gap cover."""
from .coupled_mask_grid import instance
from .coupled_mask_check import check
from .coupled_mask_audit import execute
from .zipper_rails import build,verify
from .tile_case_ledger import check_types

def main():
    n=665;k=(n-2)//3;check_types(n)
    ranges=[(25,109,203),(110,163,203),(164,219,218)]
    assert [q for l,h,_ in ranges for q in range(l,h+1)]==list(range(25,k-1))
    for l,h,x in ranges:
        data=instance(1,k,(l,h))
        assert execute(data)==f'EMPTY h=3 pass=0 horizontal=false start={x}'
        assert check(1,k,(l,h),data=data)
    U=3*k*k+7*k-(k-5)//7
    tree=verify(build(n));assert tree==(U-1,n*n-2,2,n*n-1,U-1)
    print('physical rail replay',tree,'P(665,665) =',U-1)
if __name__=='__main__':main()
