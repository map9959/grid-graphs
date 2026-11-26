import GridGraphs.ResidueTwoUpper.OneGap.TwoAncestry

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.TwoAncestry.BulkExample
open SouthCap SouthCap.Strip.GridScan

-- The seam advances three columns every four rows. This is a field
-- of masks, not a scored square with a physical parent and rim.
private def pair : Fin 4 → Nat × Nat
  | 0 => (16,129)
  | 1 => (128,9)
  | 2 => (288,2)
  | 3 => (258,16)
private def offset : Fin 4 → Int
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
private def lane (p : Fin 4) (z : Int) :=
  if z<offset p then 292 else if z=offset p then (pair p).1
  else if z=offset p+1 then (pair p).2 else 73
def wave (r : Nat) (c : Int) := lane ⟨r%4,by omega⟩ (c-3*((r/4:Nat):Int))
private def quad (p : Fin 4) (z : Int) : Word :=
  let p' : Fin 4 := ⟨(p.val+1)%4,by omega⟩
  let d : Int := if p.val=3 then 3 else 0
  (lane p z,lane p (z+1),lane p' (z-d),lane p' (z+1-d))
private theorem checked : ∀ p : Fin 4, ∀ i : Fin 12, quad p (i.val-3:Int)∈bankWords 6 6 := by native_decide

private theorem allQuad (p : Fin 4) (z : Int) : quad p z ∈ bankWords 6 6 := by
  have bounds : ∀ ph : Fin 4, 0≤offset ph ∧ offset ph≤2 := by decide
  have west (ph : Fin 4) (v : Int) (h : v<0) : lane ph v=292 := if_pos (lt_of_lt_of_le h (bounds ph).1)
  have east (ph : Fin 4) (v : Int) (h : 3<v) : lane ph v=73 := by
    have B := bounds ph
    simp [lane,show ¬v<offset ph by omega,show ¬v=offset ph by omega,show ¬v=offset ph+1 by omega]
  by_cases lo : z < -3
  · have E : quad p z=quad p (-3) := by
      unfold quad; split_ifs <;> simp (disch := omega) only [west]
    rw [E]; exact checked p 0
  by_cases hi : 8<z
  · have E : quad p z=quad p 8 := by
      unfold quad; split_ifs <;> simp (disch := omega) only [east]
    rw [E]; exact checked p 11
  simpa only [show ((z+3).toNat:Int)-3=z by omega] using checked p ⟨(z+3).toNat,by omega⟩

theorem bulk_compatible (r : Nat) (c : Int) :
    (wave r c,wave r (c+1),wave (r+1) c,wave (r+1) (c+1))∈bankWords 6 6 := by
  let z := c-3*((r/4:Nat):Int)
  let p : Fin 4 := ⟨r%4,by omega⟩
  have wordEq : (wave r c,wave r (c+1),wave (r+1) c,wave (r+1) (c+1))=quad p z := by
    simp only [wave,quad,p,z]
    congr 1
    congr 1
    · congr 1; omega
    · congr 1 <;> congr 1 <;> first | omega | (apply Fin.ext; dsimp; omega)
  rw [wordEq]
  exact allQuad p z

/-- Row zero supplies the two-column guard. Row three has a plain
front from column four and row four breaks exactly there. -/
theorem leading_example :
    (∀ c : Int, 2 ≤ c → wave 0 c=73) ∧ (∀ c : Int, 4 ≤ c → wave 3 c=73) ∧
    (wave 1 1,wave 1 2,wave 1 3)=(128,9,73) ∧
    (wave 2 2,wave 3 2)=(2,258) ∧ (wave 3 4,wave 4 4)=(73,129) := by
  refine ⟨?_,?_,by decide⟩ <;> intro c l <;> simp [wave,lane,offset] <;> split_ifs <;> omega

theorem wave_straight (r : Nat) (c : Int) : wave r c∈Port.shapes := by
  have both : ∀ p : Fin 4, (pair p).1∈Port.shapes ∧ (pair p).2∈Port.shapes := by decide
  unfold wave lane
  split_ifs <;> first | decide | exact (both _).1 | exact (both _).2
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.TwoAncestry.BulkExample
