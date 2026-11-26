import GridGraphs.ResidueZero.PhysicalStar

namespace GridGraphs.ResidueZero
open Finset

def turnOut (g o : Nat) := if o==4 then 4 else turn g o

private theorem edge_finite : ∀ (f b : Fin 2) (d : Fin 2) (o o' : Fin 5),
    (0 < f.val+b.val → (o.val=d.val ↔ o'.val≠d.val+2)) →
    ∀ g : Fin 8, edgeEvent f b (turnOut g o) (turn g d) =
      edgeEvent b f (turnOut g o') (turn g (d+2)) := by native_decide

private theorem out_eq_iff {n} (v w p : GridVertex n n) (d : Fin 4)
    (next : shift (coord v) d=coord w)
    (adj : p≠v → (gridGraph n n).Adj v p) : outDir v p=d ↔ p=w := by
  constructor
  · intro ho
    have ne : p≠v := by
      rintro rfl
      simp [outDir] at ho
      have := d.isLt; omega
    exact coord_injective ((shift_out (adj ne)).symm.trans (ho ▸ next))
  · rintro rfl
    unfold outDir
    fin_cases d <;> simp only [coord,shift,Prod.ext_iff] at next <;>
      split_ifs <;> simp_all only [Fin.ext_iff,Fin.lt_def,Prod.ext_iff,Fin.val_zero] <;> omega

private theorem reverse {p q : Pos} (d : Fin 2) (h : shift p d=q) :
    shift q (d.val+2)=p := by
  subst q; fin_cases d <;> simp [shift]

/-- Opposite endpoints of a forced edge give the same labelled, oriented
edge event. No price is charged for a missing edge orientation. -/
theorem physical_edge_key {n : Nat} (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) (v w : GridVertex n n)
    (d : Fin 2) (grid : (gridGraph n n).Adj v w) (next : shift (coord v) d=coord w) (g : Fin 8) :
    let f := (decide (v∈F)).toNat
    let b := (decide (w∈F)).toNat
    edgeEvent f b (turnOut g (outDir v (P v))) (turn g d) =
    edgeEvent b f (turnOut g (outDir w (P w))) (turn g (d+2)) := by
  dsimp only
  refine edge_finite ⟨_,by cases decide (v∈F) <;> decide⟩ ⟨_,by cases decide (w∈F) <;> decide⟩ d
    ⟨_,outDir_lt ..⟩ ⟨_,outDir_lt ..⟩ ?_ g
  intro h
  have f : v∈F ∨ w∈F := by
    by_cases hv : v∈F <;> by_cases hw : w∈F <;> simp_all
  have a := out_eq_iff v w (P v) ⟨d,by have := d.isLt; omega⟩ next (fun h => (step _ h).1)
  have b := out_eq_iff w v (P w) ⟨d+2,by have := d.isLt; omega⟩ (reverse d next) (fun h => (step _ h).1)
  exact a.trans ((covers v w ⟨grid,f⟩).trans b.not.symm)

end GridGraphs.ResidueZero
