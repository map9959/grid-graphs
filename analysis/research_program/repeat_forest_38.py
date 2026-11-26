"""Test literal duplication of three consecutive rows and three columns."""
from .extend_forest_23 import old,verify


def duplicate(rows,i,j):
    tall=rows[:i]+rows[i:i+3]+rows[i:]
    return [s[:j]+s[j:j+3]+s[j:] for s in tall]


def run():
    rows=old(38)
    best=0
    for i in range(36):
        for j in range(36):
            trial=duplicate(rows,i,j)
            count=sum(s.count('#') for s in trial)
            if count<=best:continue
            try:verify(trial)
            except AssertionError:continue
            best=count;seam=i,j
    assert best==596
    print('best of 1296 literal block duplications:',best,'seam',seam)
    for _ in range(6):
        s,e,c,t,f=verify(rows)
        print(f'side {len(rows)}: selected {s}, forced edges {e}, components {c}, tree edges {t}, full degree {f}')
        rows=duplicate(rows,*seam)


if __name__=='__main__':run()
