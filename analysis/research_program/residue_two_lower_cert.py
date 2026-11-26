"""Emit compact, untrusted region expressions for the Lean turn checker.

Each region is a polynomial-sized Boolean combination of affine inequalities,
congruences and constant-divisor quotients, not a list of grid sites.
"""
import ctypes as C
import json
import re
from pathlib import Path
from .residue_two_lower_turns import poly, runs, fn, P, S, BASES


def emit(s):
    if s.empty():return "F"
    p=fn("set_move_dims",[P,C.c_int,C.c_uint,C.c_int,C.c_uint,C.c_uint])(s.copy(),1,1,3,0,2)
    params=fn("set_params",[P])(p)
    build=fn("ast_build_from_context",[P])(poly("[t,i,j]->{:}").copy())
    expr=fn("ast_build_expr_from_set",[P,P])(build,params)
    raw=fn("ast_expr_to_str",[P],P)(expr)
    ast=json.loads(re.sub(r"\b([a-z][a-z0-9_]*|[A-Z])\b",r'"\1"',C.string_at(raw).decode()))
    C.CDLL(None).free(C.c_void_p(raw))
    fn("ast_expr_free",[P])(expr)
    fn("ast_build_free",[P])(build)
    def enc(a):
        if "val" in a:return str(a["val"])
        if "id" in a:return a["id"]
        op=a["op"];args=list(map(enc,a["args"]))
        token={"and":"&","and_then":"&","or":"|","or_else":"|","eq":"=","ge":"G",
            "le":"L","lt":"l","gt":"g","mul":"*","minus":"~","add":"+","sub":"-",
            "pdiv_r":"%","zdiv_r":"%","pdiv_q":"/","fdiv_q":"/","div":"/"}[op]
        return " ".join(args+[token])
    text=enc(ast)
    return "T" if text=="1" else "F" if text=="0" else text


def generate(base):
    edges=runs(base)
    prev=[e for e,_ in edges]
    directory=Path(__file__).resolve().parents[2]/"lean/GridGraphs/Constructions/ResidueTwo/LowerTurnData"
    directory.mkdir(exist_ok=True)
    lines=[]
    for _ in range(20):
        if all(p.empty() for p in prev):break
        # Test a layer only on forced edges. Gisting removes invariant
        # grid-boundary or modular conditions shared by all its members.
        first = not lines
        lines.extend(emit(p if first or base==56 else p.op("gist",e).clean()) for p,(e,_) in zip(prev,edges))
        prev=[prev[(d+1)%4].op("union",prev[(d+3)%4]).op("apply",along.op("reverse")).clean()
              for d,(_,along) in enumerate(edges)]
    else:raise ValueError("empty layer not found")
    (directory/f"base{base}.turns").write_text("\n".join(lines)+"\n")
    print(base,len(lines),sum(map(len,lines)),flush=True)


if __name__=="__main__":
    import sys
    for b in list(map(int,sys.argv[1:])) or BASES:
        assert b in BASES
        generate(b)
