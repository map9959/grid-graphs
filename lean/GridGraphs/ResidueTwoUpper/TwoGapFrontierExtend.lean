import GridGraphs.ResidueTwoUpper.TwoGapFrontierRetire

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph

def extendP (p : Array Nat) := p ++ ((List.range 9).map (·+10)).toArray
def flag (m i : Nat) := (if m.testBit i then 2 else 0) + (if i=0 ∨ i=8 then 1 else 0)
def extendT (t : Array Nat) (m : Nat) := t ++ ((List.range 9).map (flag m)).toArray
def oldSlot (i : Fin 10) : Fin 19 := ⟨i,by omega⟩
def newSlot (i : Fin 9) : Fin 19 := ⟨10+i.val,by omega⟩

private theorem cases19 (i : Fin 19) : (∃ j, i=oldSlot j) ∨ ∃ j, i=newSlot j := by
  by_cases h : i.val<10
  · exact .inl ⟨⟨_,h⟩,rfl⟩
  · exact .inr ⟨⟨i.val-10,by omega⟩,Fin.ext (by dsimp [newSlot]; omega)⟩

theorem extend_models {H : SimpleGraph V} {port : Fin 19 → V} {ev : Fin 2 → V → Prop}
    {p t : Array Nat} {m : Nat} (model : Models H (port ∘ oldSlot) ev p t)
    (distinct : Function.Injective port) (fresh : ∀ i y, ¬H.Adj (port (newSlot i)) y)
    (events : ∀ i (d : Fin 2), (flag m i.val).testBit d ↔ ev d (port (newSlot i))) :
    Models H port ev (extendP p) (extendT t m) := by
  have lp := model.lenP
  have lt := model.lenT
  have ep : (extendP p).size=19 := by simp [extendP,lp]
  have et : (extendT t m).size=19 := by simp [extendT,lt]
  have po (i : Fin 10) : (extendP p)[(oldSlot i).val]! = p[i.val]! := by
    have hi : i.val<p.size := by omega
    rw [getElem!_pos _ _ (by rw [ep]; exact (oldSlot i).isLt)]
    simp [extendP,oldSlot,getElem!_pos,Array.getElem_append,hi]
  have pn (i : Fin 9) : (extendP p)[(newSlot i).val]! = 10+i.val := by
    rw [getElem!_pos _ _ (by rw [ep]; exact (newSlot i).isLt)]
    simp [extendP,newSlot,Array.getElem_append,lp,Nat.add_comm]
  have to' (i : Fin 10) : (extendT t m)[p[i.val]!]! = t[p[i.val]!]! := by
    have h := model.small i
    have hi : p[i.val]!<t.size := by omega
    rw [getElem!_pos _ _ (by rw [et]; omega)]
    simp [extendT,getElem!_pos,Array.getElem_append,hi]
  have tn (i : Fin 9) : (extendT t m)[10+i.val]! = flag m i.val := by
    rw [getElem!_pos _ _ (by rw [et]; omega)]
    simp [extendT,getElem!_pos,Array.getElem_append,lt]
  have iso {x y : V} (h : ∀ z, ¬H.Adj x z) (c : H.Reachable x y) : x=y := by
    obtain ⟨w⟩ := c; cases w with | nil => rfl | cons e _ => exact (h _ e).elim
  have no (i : Fin 9) (j : Fin 10) : ¬H.Reachable (port (newSlot i)) (port (oldSlot j)) := by
    intro c
    have h := congrArg Fin.val (distinct (iso (fresh i) c))
    change 10+i.val=j.val at h; omega
  refine ⟨by simp [extendP,lp],by simp [extendT,lt],?_,?_,?_⟩
  · intro i; rcases cases19 i with ⟨j,rfl⟩|⟨j,rfl⟩
    · rw [po]; exact (model.small j).trans (by decide)
    · rw [pn]; omega
  · intro i j; rcases cases19 i with ⟨i,rfl⟩|⟨i,rfl⟩ <;> rcases cases19 j with ⟨j,rfl⟩|⟨j,rfl⟩
    · rw [po,po]; exact model.parts _ _
    · rw [po,pn]; exact iff_of_false (by have := model.small i; omega) (fun h => no j i h.symm)
    · rw [pn,po]; exact iff_of_false (by have := model.small j; omega) (no i j)
    · rw [pn,pn]; constructor
      · intro eq; have e : i=j := Fin.ext (by omega); subst j; rfl
      · intro h; exact congrArg Fin.val (distinct (iso (fresh i) h))
  · intro i d; rcases cases19 i with ⟨j,rfl⟩|⟨j,rfl⟩
    · rw [po,to']; exact model.tags _ _
    · rw [pn,tn,events]; exact ⟨fun h => ⟨_,.rfl,h⟩,fun ⟨_,r,h⟩ => (iso (fresh j) r) ▸ h⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
