"""Suggest small affine strip descriptors. Lean proves each descriptor for all u."""
from collections import defaultdict
from pathlib import Path


def descriptors(base):
    data = iter((Path(__file__).resolve().parents[2] / 'lean/GridGraphs/NoPitch/Data' /
                 f'chart{base}.v32').read_bytes())

    def uint():
        v = shift = 0
        while True:
            t = next(data)-48
            v += (t%32) << shift
            if t < 32:
                return v
            shift += 5

    def sint():
        z = uint()
        return z//2 if not z%2 else -(z//2+1)

    _, nr, nc = uint(), uint(), uint()
    rows = [(uint(),uint(),sint(),sint(),sint(),sint()) for _ in range(nr)]
    norm = {i:set() for i,r in enumerate(rows) if i and r[3]}
    for _ in range(nc):
        key, units, fixed, obj, length = uint(),uint(),uint(),sint(),uint()
        i = 0
        for _ in range(length):
            i += uint()
            sint()
            if i in norm:
                p = key//8//(32**5 if key%8 < 2 else 512)
                norm[i].add((key%8 >= 2, p//32**3,p//32**2%32,p//32%32,p%32))

    def shape(n,h,pat):
        def ax(z):
            return z if z<h else 2*h+3+z-n if n-h<=z else h+(z-h)%3
        def clip(z):
            return 9+max(-9,min(9,z))
        fibre = defaultdict(list)
        for x in range(n):
            for y in range(n):
                if (ax(x),ax(y),clip(x-y),clip(x+y+1-n)) == pat:
                    fibre[x].append(y)
        xs = sorted(fibre)
        assert xs == list(range(xs[0],xs[-1]+1,3))
        for ys in fibre.values():
            assert ys == list(range(ys[0],ys[-1]+1,3))
        return xs[0],fibre[xs[0]][0],len(xs),len(fibre[xs[0]]),\
            (fibre[xs[1]][0]-fibre[xs[0]][0],len(fibre[xs[1]])-len(fibre[xs[0]])) if len(xs)>1 else (0,0)

    result = []
    for i, cells in norm.items():
        (patch,*pat), = cells
        n,h = (base-2,7) if patch else (base,8)
        x,y,H,W,_ = shape(n,h,tuple(pat))
        X,Y,hh,ww,(sy,sw) = shape(n+6,h,tuple(pat))
        result.append((n,h,pat,[x,X-x,y,Y-y,sy,H,hh-H,W,ww-W,sw],rows[i][3:]))
    return result


def main():
    dest = Path(__file__).resolve().parents[2] / 'lean/GridGraphs/NoPitch/TailRows'
    for base in (58,61):
        ds = descriptors(base)
        def vect(xs,op,cl):
            return op+','.join(map(str,xs))+cl
        lines=['import GridGraphs.NoPitch.TailRows.NormShape','',
               'namespace GridGraphs.NoPitch.TailRows', 'open Keys GridGraphs.NoPitch.Dual',
               f'def buckets{base} : Array NormShape := #[']
        for n,h,p,s,poly in ds:
            lines.append(f'  ⟨{n},{h},'+vect(p,'[',']')+','+vect(s,'⟨','⟩')+','+vect(poly,'⟨','⟩')+'⟩,')
        lines[-1]=lines[-1][:-1]+']'
        for j in range(len(ds)):
            lines += [f'private theorem valid_{base}_{j} : (buckets{base}[{j}]!).Valid := by',
                      f'  dsimp [buckets{base},NormShape.Valid]; verify_strip']
        lines += ['', f'theorem shapes{base} (j : Fin {len(ds)}) : (buckets{base}[j.val]!).Valid := by',
                  '  fin_cases j', '  exacts ['+','.join(f'valid_{base}_{j}' for j in range(len(ds)))+']','',
                  'end GridGraphs.NoPitch.TailRows','']
        (dest/f'Buckets{base}.lean').write_text('\n'.join(lines))


if __name__ == '__main__':
    main()
