import GridGraphs.ResidueTwoUpper.TwoGapFrontierLink

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph

def retained (i : Fin 10) : Fin 19 := ⟨if i.val<9 then 10+i.val else 9,by split_ifs <;> omega⟩
def live (p : Array Nat) := ((List.range 9).map (fun i => p[10+i]!)) ++ [p[9]!]

private theorem live_fn (p : Array Nat) :
    live p=List.ofFn (fun i : Fin 10 => p[(retained i).val]!) := by
  simp only [live,show List.range 9=[0,1,2,3,4,5,6,7,8] by decide]
  rfl

def finishRow (p t : Array Nat) (m : Nat) : Option Frontier := do
  let keep := live p
  for i in [:9] do
    if t[p[i]!]! = 2 && !keep.contains p[i]! then return ← none
  return ⟨m,(keep.map keep.idxOf).toArray,(keep.map (fun c => t[c]!)).toArray⟩

/-- Every represented marked component either has an access flag or
touches the newest row/root. This is a statement about graph reachability. -/
def Escape (H : SimpleGraph V) (port : Fin 19 → V) (event : Fin 2 → V → Prop) : Prop :=
  ∀ (j : Fin 9) x, H.Reachable (port ⟨j.val,by omega⟩) x →
    event 1 x → hits H (event 0) x ∨ ∃ i : Fin 10, H.Reachable x (port (retained i))

theorem retire_survives {H : SimpleGraph V} {port : Fin 19 → V}
    {event : Fin 2 → V → Prop} {p t : Array Nat} (m : Nat)
    (model : Models H port event p t) (esc : Escape H port event) :
    ∃ s, finishRow p t m=some s ∧ s.last=m ∧ Models H (port ∘ retained) event s.parts s.tags := by
  let L := live p
  have len : L.length=10 := by simp [L,live]
  have item (i : Fin 10) : L[i.val]! = p[(retained i).val]! := by fin_cases i <;> rfl
  have mem (i : Fin 10) : p[(retained i).val]! ∈ L := by
    rw [←item,getElem!_pos L i.val (by rw [len]; exact i.isLt)]
    exact List.getElem_mem ..
  have ok (i : Nat) (hi : i<9) : ¬(t[p[i]!]! = 2 ∧ p[i]!∉L) := by
    rintro ⟨tag,dead⟩
    let x : Fin 19 := ⟨i,by omega⟩
    have one := (model.tags x 1).mp (by change (t[p[i]!]!).testBit 1=true; rw [tag]; decide)
    obtain ⟨y,reach,mark⟩ := one
    rcases esc ⟨i,hi⟩ y reach mark with ⟨v,via,hit⟩|⟨j,r⟩
    · have z := (model.tags x 0).mpr ⟨v,reach.trans via,hit⟩
      change (t[p[i]!]!).testBit 0=true at z; rw [tag] at z; contradiction
    · exact dead (((model.parts x (retained j)).mpr (reach.trans r)).symm ▸ mem j)
  let s : Frontier := ⟨m,(L.map L.idxOf).toArray,(L.map (fun c => t[c]!)).toArray⟩
  refine ⟨s,?_,rfl,?_⟩
  · unfold finishRow
    have guard (i : Nat) (h : i∈List.range 9) :
        ((decide (t[p[i]!]! = 2)) && !(live p).contains p[i]!)=false := by
      apply Bool.eq_false_iff.mpr; simpa [L] using ok i (List.mem_range.mp h)
    have C (i : Fin 9) := guard i (List.mem_range.mpr i.isLt)
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    rw [show List.range' 0 ([:9] : Std.Legacy.Range).size=[0,1,2,3,4,5,6,7,8] by decide]
    have ck (i : Nat) (h : i<9) := guard i (List.mem_range.mpr h)
    simp only [List.forIn_cons,List.forIn_nil,ck _ (by decide : 0<9),ck _ (by decide : 1<9),
      ck _ (by decide : 2<9),ck _ (by decide : 3<9),ck _ (by decide : 4<9),ck _ (by decide : 5<9),
      ck _ (by decide : 6<9),ck _ (by decide : 7<9),ck _ (by decide : 8<9),Bool.false_eq_true,if_false,
      pure_bind]; rfl
  · have sp (i : Fin 10) : s.parts[i.val]! = L.idxOf (p[(retained i).val]!) := by
      have hi : i.val<L.length := by rw [len]; exact i.isLt
      simp [s,getElem!_pos,hi,←item,getElem!_pos L i.val hi]
    have st (i : Fin 10) : s.tags[s.parts[i.val]!]! = t[p[(retained i).val]!]! := by
      rw [sp]; have lt := List.idxOf_lt_length_of_mem (mem i)
      simp [s,getElem!_pos,lt,List.getElem_idxOf]
    refine ⟨by simp [s,len],by simp [s,len],?_,?_,?_⟩
    · intro i; rw [sp,←len]; exact List.idxOf_lt_length_of_mem (mem i)
    · intro i j; rw [sp,sp,List.idxOf_inj (mem i)]; exact model.parts _ _
    · intro i d; rw [st]; exact model.tags _ _

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
