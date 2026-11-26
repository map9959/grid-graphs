"""Side-34 comb with an irregular bottom cap; no solver dependencies."""
from .extend_forest_28 import verify


def rows34():
    n=34
    cap=[(0,3,6,9,15,18,21,27,30,33),
         (0,3,6,11,13,23,25,30,33),
         (0,3,8,11,16,17,18,19,20,25,28,33),
         (0,5,8,11,14,22,25,28,31)]
    marks=[range(n),()]+[range(0,n,3)]*26+cap+[(),range(n)]
    return [''.join('#' if j in row else '.' for j in range(n)) for row in marks]


if __name__=='__main__':
    s,e,c,t,f=verify(rows34())
    assert s==f==420
    print(f'side 34: {s} selected; {e} acyclic forced edges; {c} components; '
          f'{t} spanning-tree edges; {f} full-degree vertices')
