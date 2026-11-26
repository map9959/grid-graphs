"""Symbolic non-backtracking turns of the forced zipper graph.

Only the square parameter t and two site coordinates are live between passes.
libisl operates on sets of integer points, including the unbounded parameter.
With no arguments this verifies the fourteen progressions in the classification.
There is no interpolation, sampling of t, or stored lattice-point dataset.

Layer zero is the set of directed forced edges. To get the next layer,
propagate the previous layer backwards around one perpendicular turn and
arbitrarily far backwards along a straight forced segment. Check both local
implications again using only single-grid-step shifts. An unreachable bounded
face would have a nonreversing directed boundary, necessarily turning again
within n steps; equivalently use Turn.routes_of_layers in LowerTurnLayers.lean.
"""
import ctypes as C
import re


lib = C.CDLL("libisl.so.23")


def fn(name, inputs, out=C.c_void_p):
    call = getattr(lib, "isl_" + name)
    call.argtypes = inputs
    call.restype = out
    return call


P, S = C.c_void_p, C.c_char_p
ctx = fn("ctx_alloc", [])()


class Poly:
    def __init__(self, kind, p):
        if not p:
            raise ValueError(kind)
        self.kind, self.p = kind, p

    def __del__(self):
        if hasattr(self, "p"):
            fn(self.kind + "_free", [P])(self.p)

    def copy(self):
        return fn(self.kind + "_copy", [P])(self.p)

    def op(self, name, *others, kind=None):
        return Poly(kind or self.kind, fn(self.kind + "_" + name, [P]*(len(others)+1))(
            self.copy(), *(a.copy() for a in others)))

    def clean(self):
        return self.op("compute_divs").op("coalesce")

    def empty(self):
        result = fn(self.kind + "_is_empty", [P], C.c_int)(self.p)
        if result < 0:
            raise ValueError("ISL emptiness test failed")
        return result == 1

    def __str__(self):
        ptr = fn(self.kind + "_to_str", [P])(self.p)
        text = C.string_at(ptr).decode()
        free = C.CDLL(None).free
        free.argtypes = [P]
        free(ptr)
        return text


def poly(s, kind="set"):
    s = re.sub(r"(\d)(?=\(|floor)",r"\1*",s)
    return Poly(kind, fn(kind+"_read_from_str", [P,S])(ctx, s.encode()))


def mask(base):
    n = f"({base}+42t)"
    f = f"({(base-2)//6}+7t)"
    even = base % 6 == 2
    phase = base % 42
    alt = phase == 14
    extra = 1 if phase in (38,29) else 2 if phase == 5 else 0
    st = f"({2 if alt else 3+extra}+{f})"
    size = f"({n}-5-{st})"
    band = f"floor((i-{st})/7)"
    bphase = f"((i-{st}) mod 7)"
    l = f"(3{f}-3{band})"
    final = l.replace("i-",f"{n}-5-")

    def regular(l):
        return f"((j<={l} and j mod 3=0) or (j>={l}+4 and j mod 3=1))"

    complete = f"(7({band}+1)<={size})"
    def band_rows(l,right):
        delpt = f"(j={l}{'+4' if right else ''})"
        addpt = f"(j={l}{'+5' if right else '-1'})"
        return f"""({st}<=i<{n}-5 and (
       ({regular(l)} and not ({complete} and {bphase}>=5 and {delpt})) or
       ({bphase}=2 and j={l}+2) or
       ({complete} and (({bphase}=5 and j={l}+2) or ({bphase}=6 and {addpt})))
       ))"""
    mid = band_rows(l,False)
    if alt:
        mid = (f"((i-{st}) mod 14<7 and {band_rows('3('+f+'-1)',True)}) or "
               f"((i-{st}) mod 14>=7 and {band_rows('3'+f,False)})")
        final = f"(3({f}-1)+3((1+t) mod 2))"
        top = f"""(i=0 and (j>=3 or j=0)) or (i=1 and j=0) or
         (2<=i<{st} and (j=0 or (j<3(i-2) and j mod 3=0) or
          (3(i-2)+2<=j<{n}-5-3(i-2) and j mod 3=2) or
          (j>={n}-1-3(i-2) and j mod 3=1)))"""
        cap = f"""({n}-5<=i<{n}-2 and ((j<={final} and j mod 3=0) or j={n}-1 or
          (i={n}-5 and j={final}+2) or (i={n}-4 and {final}+5<=j<{n}-2) or
          (i={n}-3 and j={final}+3))) or (i={n}-2 and j=0) or (i={n}-1 and j!=1)"""
    else:
        top = f"""(i=0 and (j<{n}-3 or j={n}-1)) or (i=1 and j={n}-1) or
          (i=2 and (j mod 3=2 or j={n}-1)) or
          (3<=i<3+{f} and ((j<=3(i-3) and j mod 3=0) or
           (j>={n}-1-3(i-3) and j mod 3=1) or
           (3(i-3)+5<=j<{n}-5-3(i-3) and j mod 3=2))) or
          (3+{f}<=i<{st} and {regular('3'+f)})"""
        if even or phase in (5,11,29):
            stop = '3'+f if even else f"({12 if phase==29 else 9}+6t)"
            top = f"""((({top}) and not ((i=0 and j=1) or
              (i>=2 and 3(i-2)<{stop} and j=3(i-2)+2))) or
              (i=1 and j=0) or (i>=2 and 3(i-2)<={stop} and j=3(i-2)))"""
        cap = f"""({n}-5<=i<{n}-2 and ((j<={final}-6 and j mod 3=0) or
          (j>={final}+4 and j mod 3=1) or (i={n}-5 and j={final}+2) or
          (i={n}-4 and {final}-4<=j<{final}) or (i={n}-3 and j={final}+1)))
          or i={n}-1"""
    return f"({top} or {mid} or {cap})"


DIRS = [(0,1),(1,0),(0,-1),(-1,0)]
BASES = (23,35,38,41,44,47,50,53,56,59,62,68,71,74)


def shift(d):
    di,dj = DIRS[d]
    return poly(f"[t] -> {{ [i,j] -> [i+({di}),j+({dj})] }}","map")


def runs(base):
    n = f"({base}+42t)"
    board = f"t>=0 and 0<=i<{n} and 0<=j<{n}"
    pref = "[t] -> { [i,j] : "
    M = poly(pref+board+" and "+mask(base)+"}").clean()
    result = []
    for d,(di,dj) in enumerate(DIRS):
        step = shift(d)
        edge = M.op("union",M.op("apply", step.op("reverse"))).clean()
        edge = edge.op("intersect",poly(pref+board+
          f" and 0<=i+({di})<{n} and 0<=j+({dj})<{n}"+"}")).clean()
        cond = "u=i" if not di else "v=j"
        axis,end,sign = ("i","u",di) if di else ("j","v",dj)
        def ahead(weak):
            comp = ("<=" if weak else "<") if sign>0 else (">=" if weak else ">")
            return poly(f"[t] -> {{ [i,j] -> [u,v] : {cond} and {axis}{comp}{end} }}","map")
        seg = ahead(False).op("intersect_domain",poly(pref+board+"}"))
        seg = seg.op("intersect_range",poly(pref+board+"}"))
        bad = ahead(True).op("intersect_range",edge.op("complement")).op("apply_range",ahead(False))
        along = seg.op("subtract",bad).clean()
        result.append((edge,along))
    return result


def turns(base):
    """Verify the sufficient rank inequalities without trusting segment
    computation: straight continuation within a layer and both turns from
    the preceding layer. Outside the board no edge is permitted."""
    assert base in BASES
    edges = runs(base)
    possible = [e for e,_ in edges]
    for s in range(1,32):
        prev = possible
        possible = []
        for d,(_,along) in enumerate(edges):
            ends = prev[(d+1)%4].op("union",prev[(d+3)%4])
            possible.append(ends.op("apply",along.op("reverse")).clean())
        for d,(forced,_) in enumerate(edges):
            assert possible[d].op("subtract",prev[d]).empty()
            for e in (d,(d+1)%4,(d+3)%4):
                # If v->v+d is forced and v+d can continue from direction e,
                # then v must be in this layer. This is a one-step check.
                nxt = possible[e] if e==d else prev[e]
                required = nxt.op("apply",shift(d).op("reverse")).op("intersect",forced)
                assert required.op("subtract",possible[d]).empty()
        if all(p.empty() for p in possible):
            print(f"n={base}+42t: no directed forced path with {s} turns",flush=True)
            return s
    raise ValueError("no bound")


if __name__ == "__main__":
    import sys
    for b in list(map(int,sys.argv[1:])) or BASES:
        turns(b)
