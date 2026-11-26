import GridGraphs.ResidueTwoUpper.OneGap.SouthCapClauses

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open Std.Sat ResidueZero Stencil

abbrev Cube (n : Nat) := List (Fin n × Bool)

/-- A cube is checked against all completions of just the input bits
of the price table (at most nine), not assignments of the whole halo.
`admit` contains non-price filters in that same table. -/
def badCube {n : Nat} (cube : Cube n) (admit : (Fin n → Bool) → Bool)
    (price : (Fin n → Bool) → Int) : Bool :=
  decide (∀ a : Fin n → Bool, (∀ z ∈ cube, a z.1=z.2) →
    admit a=true → price a≠0)

def cubeLits {V : Type} {n : Nat} (wire : Fin n → Wire V) (cube : Cube n) :
    CNF.Clause (Wire V) := cube.map fun (i,b) => (wire i,b)

theorem finite_price_row {V : Type} {n : Nat} (W : WindowField V)
    (wire : Fin n → Wire V) (guard : CNF.Clause (Wire V)) (cube : Cube n)
    (admit : (Fin n → Bool) → Bool) (price : (Fin n → Bool) → Int)
    (checked : badCube cube admit price)
    (clean : guard.eval (value W)≠true →
      admit (value W ∘ wire)=true ∧ price (value W ∘ wire)=0) :
    (priceRow guard (cubeLits wire cube)).eval (value W)=true := by
  apply (eval_priceRow_iff ..).mpr
  by_cases g : guard.eval (value W)=true
  · exact Or.inl g
  · right
    intro all
    have eqs : ∀ z∈cube, (value W ∘ wire) z.1=z.2 := by
      intro z hz
      exact all _ _ (List.mem_map.mpr ⟨z,hz,rfl⟩)
    have nonzero := of_decide_eq_true checked (value W ∘ wire) eqs (clean g).1
    exact nonzero (clean g).2

def mask9 (a : Fin 9 → Bool) : Nat :=
  ((List.finRange 9).map fun i => (a i).toNat <<< i.val).sum

def patchPrice (pos : Pos) (a : Fin 9 → Bool) := twoOrbitPatch 119 pos (mask9 a)

def starPrice (pos : Pos) (out : Nat) (a : Fin 5 → Bool) :=
  twoOrbitStar 119 pos (a 0).toNat (code fun i : Fin 4 => a i.succ) out

/-- Patch clauses have no outgoing-arrow guard. Each checked cube
excludes every physically admissible completion with patch price zero. -/
theorem atlas_patch_clause {V : Type} (W : WindowField V) (slots : Fin 9 → V)
    (pos : Pos) (cube : Cube 9)
    (checked : badCube cube (fun a => maskOK (mask9 a)) (patchPrice pos))
    (ok : maskOK (mask9 fun i => W.mark (slots i)))
    (zero : twoOrbitPatch 119 pos (mask9 fun i => W.mark (slots i))=0) :
    (priceRow [] (cubeLits (Wire.mark ∘ slots) cube)).eval (value W)=true := by
  exact finite_price_row W _ [] cube _ _ checked (fun _ => ⟨ok,zero⟩)

/-- Star clauses use the four compass-neighbour bits (blank slots can
be supplied by the finite producer as fixed false) and the centre bit.
The guard singles out the priced outgoing-arrow choice. -/
theorem atlas_star_clause {V : Type} (W : WindowField V) (sample : Fin 5 → Wire V)
    (pos : Pos) (out : Nat) (guard : CNF.Clause (Wire V)) (cube : Cube 5)
    (checked : badCube cube
      (fun a => starOK 119 pos (a 0).toNat (code fun i : Fin 4 => a i.succ) out)
      (starPrice pos out))
    (clean : guard.eval (value W)≠true →
      starOK 119 pos (value W (sample 0)).toNat
        (code fun i : Fin 4 => value W (sample i.succ)) out ∧
      twoOrbitStar 119 pos (value W (sample 0)).toNat
        (code fun i : Fin 4 => value W (sample i.succ)) out=0) :
    (priceRow guard (cubeLits sample cube)).eval (value W)=true :=
  finite_price_row W sample guard cube _ _ checked clean

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
