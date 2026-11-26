"""Verify the saved side-23 construction independently of SAT and the LP."""
from pathlib import Path
from .extend_forest_28 import verify


if __name__=='__main__':
    rows=Path(__file__).with_name('forest_23.txt').read_text().splitlines()
    assert len(rows)==23 and all(len(r)==23 and set(r)<={'.','#'} for r in rows)
    s,e,c,t,f=verify(rows)
    assert s==f==196
    print(f'side 23: {s} selected, {e} acyclic forced edges, {c} components, '
          f'{t} spanning-tree edges, {f} full-degree vertices')
