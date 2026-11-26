"""Generate the 9x9 corner types. cap_entry rechecks every mask in Lean."""
from pathlib import Path
from .defect_window import table


def main():
    typ, patch, star = table(35)
    words, ids = [], []
    for r in range(9):
        for c in range(9):
            stars = [star(typ(0, r+1, c+1), (0, 1, 2, 3), o, o == -1, False)
                     for o in (-1, 0, 1, 2, 3)]
            def cross(m):
                return (m>>4&1) + sum((m>>v&1) << (d+1) for d,v in enumerate((5,7,3,1)))
            allowed = sum(1 << m for m,z in enumerate(patch(typ(1,r,c)))
                          if z == 0 and any(s[cross(m)] == 0 for s in stars))
            if allowed not in words:
                words.append(allowed)
            ids.append(words.index(allowed))
    path = Path(__file__).resolve().parents[2]/'lean/GridGraphs/ResidueTwoUpper/OneGap/FanSouthData.lean'
    path.write_text('''import GridGraphs.ResidueTwoUpper.OneGap.FanBootGeo
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.South
open L7 FanSlab ResidueZero Stencil
private def words : Array Nat := #[\n''' + ',\n'.join(map(hex,words)) + ''']
private def ids : Array Nat := #[\n''' + ',\n'.join(','.join(map(str,ids[i:i+9])) for i in range(0,81,9)) + ''']
def adm (r c m : Nat) := words[ids[9*r+c]!]!.testBit m
def tag (r : Nat) := if r<6 then r else 6+r%3
private def entry (w : View) (r c m : Nat) := let p := L7.view w 33 r c
  !maskOK m || adm r c (encode (Fin.ofNat 512 m) w) || twoOrbitPatch 35 p m != 0 ||
    (List.range 5).all fun o => !starOK 35 (p+(1,1)) (bit m 4) (PatchFilter.cnb m) o ||
      twoOrbitStar 35 (p+(1,1)) (bit m 4) (PatchFilter.cnb m) o != 0
theorem cap_entry : ∀ (w : View) (r c : Fin 9) (m : Fin 512), entry w r c m := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.South
''')

if __name__ == '__main__':
    main()
