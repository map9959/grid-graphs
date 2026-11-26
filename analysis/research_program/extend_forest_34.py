"""Extend the rail-and-cap witness at a seam between two empty bulk columns."""
from .verify_forest_34 import rows34,verify


def extend(rows):
    n=len(rows)
    assert rows[2]==rows[3] and rows[2]=='#..'*((n-1)//3)+'#'
    tall=rows[:3]+[rows[2]]*3+rows[3:]
    # Insert a rail with an empty column on either side. The old seam
    # between columns 1 and 2 crosses only the two full boundary rows.
    for i,row in enumerate(tall):
        assert row[1:5]==('####' if i in (0,n+2) else '..#.' if 2<=i<=n-1 else '....')
    return [row[:2]+row[2:5]+row[2:] for row in tall]


if __name__=='__main__':
    import sys
    side=int(sys.argv[1]) if len(sys.argv)>1 else 37
    assert side>=34 and side%3==1
    rows=rows34()
    for n in range(34,side+1,3):
        if n>34:rows=extend(rows)
        score,edges,comp,tree,full=verify(rows)
        k=(n-1)//3
        assert score==3*k*k+5*k+2
        print(f'side {n}: selected {score}, acyclic forced edges {edges}, '
              f'components {comp}, tree edges {tree}, full-degree vertices {full}')
