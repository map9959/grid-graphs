"""Classify the cost of an inward perimeter arrow on every odd tight side."""
from itertools import product
from .defect_window import table
from .odd_frames import PAT, frame


def verify(n=119):
    typ, _, star = table(n)
    # Rotate/reflect a tested side to the north; its inward port is south.
    ds = (0, 1, 2)
    costs = [set() for _ in range(n)]
    tangent = set()
    for left, right in product(range(len(PAT)), repeat=2):
        marks = frame(n, (left, right, 0, 0))
        for j in range(1, n-1):
            # Row one is empty except possibly its two boundary endpoints.
            bits = (marks[0,j] + 2*marks[0,j+1] + 4*marks[1,j]
                    + 8*marks[0,j-1])
            costs[j].add(star(typ(0,0,j), ds, 1, False, False)[bits])
            tangent.update(star(typ(0,0,j), ds, out, False, False)[bits]
                           for out in (0,2))
    # The central interval contains every periodic bulk phase. Its
    # endpoint exceptions are at fixed distances from the corners.
    assert all(costs[j] == {72} for j in range(4, n-4))
    assert min(set.union(*costs[1:-1])) == 72
    assert tangent & set(range(73)) == {0}
    assert all(star(typ(0,0,0), (0,1), out, out==-1, True)[bits] == 0
               for out in (-1,0,1) for bits in (3,5))
    print('inward charges, distances 1,2,3:', *(sorted(costs[j]) for j in (1,2,3)))
    print('distances >=4 on both ends: [72]; minimum inward charge: 72')
    print('perimeter inward arrows = g-1; sole defect for g=2 is the exit')
    print('admissible tangent and corner charges: [0]; g=1 has no perimeter star defect')


if __name__ == '__main__':
    verify()
