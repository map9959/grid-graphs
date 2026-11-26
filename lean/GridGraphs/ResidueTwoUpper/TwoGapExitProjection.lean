import GridGraphs.ResidueTwoUpper.TwoGapExitReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open Catalogue ResidueZero

def tile (s : Field) (i j : Int) := packed9 fun b =>
  s.mark (shiftAt i j ((b.val%3:Nat),(b.val/3:Nat)))

/-- The overlap used by `permits` identifies actual physical sites even
when the stamps on the two plaquettes come from a collapsed row. -/
theorem four_tiles (s : Field) (i j : Int) (t : Fin 4) :
    four (pull s i j) t=tile s (i+(t.val/2:Nat)) (j+(t.val%2:Nat)) := by
  unfold four tile
  congr 1
  funext b
  apply congrArg s.mark
  ext <;> simp [shiftAt,site] <;> ring

def stripWord (s : Field) (q j : Int) : Word :=
  (tile s (q-1) j,tile s q j,tile s (q+1) j)
def band (v : Fin 4 → Nat) : Band := (v 0,v 1,v 2,v 3)

theorem permits_iff (s : Field) (q j : Int) (tab : List Band) :
    permits tab (stripWord s q j) (stripWord s q (j+1)) ↔
    band (four (pull s (q-1) j)) ∈ tab ∧ band (four (pull s q j)) ∈ tab := by
  simp [permits,stripWord,band,four_tiles]

theorem exit_columns {a b p : Int} (ha : 0≤a) (hb : 0≤b)
    (left : 0<a → 12≤p) (right : 0<b → p≤12) :
    shortCol a b (p+a-1)=p-1 ∧ shortCol a b (p+a)=p := by
  unfold shortCol fold; split_ifs <;> omega

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
