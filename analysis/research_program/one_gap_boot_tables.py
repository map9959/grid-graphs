"""Generate the small zero-patch / zero-star catalogue for the north seed.
All masks and views are checked again in Lean; no solver trace is used.
"""
from pathlib import Path
from .defect_window import table

def main():
    typ,patch,star=table(35); words=[]; ids=[]
    for a in range(1,9):
        for b in [*range(1,9),*range(27,32)]:
            ts=[star(typ(0,a+1,b+1),tuple(range(4)),o,o==-1,False) for o in (-1,0,1,2,3)]
            def cross(m):return (m>>4&1)+2*(m>>5&1)+4*(m>>7&1)+8*(m>>3&1)+16*(m>>1&1)
            w=sum(1<<m for m,z in enumerate(patch(typ(1,a,b))) if z==0 and any(t[cross(m)]==0 for t in ts))
            if w not in words:words.append(w)
            ids.append(words.index(w))
    path=Path(__file__).resolve().parents[2]/'lean/GridGraphs/ResidueTwoUpper/OneGap/FanBootData.lean'
    path.write_text('''import GridGraphs.ResidueTwoUpper.OneGap.FanSlabChart
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab
private def words : Array Nat := #[\n'''+',\n'.join(map(hex,words))+''']
private def ids : Array Nat := #[\n'''+',\n'.join(','.join(map(str,ids[r:r+13])) for r in range(0,104,13))+''']
def accepts (r c m : Nat) := words[ids[13*r+c]!]!.testBit m
def rowTag (r : Nat) := if r<5 then r else 5+(r+1)%3
private def entry (w : View) (r t : Nat) (m : Fin 512) :=
  let a := L7.view w 33 (r+1:Nat) (small t)
  !maskOK m || accepts r t (encode m w) || twoOrbitPatch 35 a m != 0 ||
    (List.range 5).all fun o => !starOK 35 (a+(1,1)) (bit m 4) (PatchFilter.cnb m) o ||
      twoOrbitStar 35 (a+(1,1)) (bit m 4) (PatchFilter.cnb m) o != 0
theorem entry_ok : ∀ (w : View) (r : Fin 8) (c : Fin 13) (m : Fin 512), entry w r c m := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
''')
if __name__=='__main__':main()
