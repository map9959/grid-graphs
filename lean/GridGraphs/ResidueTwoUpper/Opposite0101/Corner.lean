import GridGraphs.ResidueTwoUpper.Opposite0101.Strip

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero

def crossRow (xs : List Nat) (r : Nat) :=
  ((List.range 7).map (fun j => bit xs[j]! r <<< j)).sum
def cornerOK (xs : List Nat) : Bool :=
  ((states false 5).contains (entry xs[5]! xs[6]!)) &&
  ((states true 5).contains (entry (crossRow xs 5) (crossRow xs 6)))

/-- The last two columns of each arm are compared on *one* corner square.
The recursion has depth seven, independent of the width parameter. -/
def search : Nat → List Nat → Bool
  | 0,xs => cornerOK xs
  | fuel+1,xs =>
    let j := xs.length
    (List.range 128).any fun c => colOK false j c &&
      (j==0 || localOK false (j-1) (if j=1 then 0 else xs[j-2]!) xs[j-1]! c) &&
      search fuel (xs++[c])

theorem no_corner : search 7 []=false := by native_decide

def frontCols (s : Nat → Nat) (j : Nat) := (List.range j).map s
theorem prefix_at (s : Nat → Nat) {j i : Nat} (hi : i<j) : (frontCols s j)[i]! = s i := by
  simp [frontCols,List.getElem!_eq_getElem?_getD,hi]

theorem no_strips {u a b} (north : StripOK false u a) (west : StripOK true u b)
    (common : ∀ r : Fin 7, crossRow (frontCols a 7) r=b r) : False := by
  have last : cornerOK (frontCols a 7) := by
    have A := suffix_mem north 5 le_rfl (by omega)
    have B := suffix_mem west 5 le_rfl (by omega)
    have h5 : crossRow (frontCols a 7) 5=b 5 := common 5
    have h6 : crossRow (frontCols a 7) 6=b 6 := common 6
    simpa [cornerOK,prefix_at a (by decide : 5<7),prefix_at a (by decide : 6<7),
      show idx u 5=5 by simp [idx],h5,h6] using (show _ ∧ _ from ⟨A,B⟩)
  have go (d j : Nat) (hj : j+d=7) : search d (frontCols a j)=true := by
    induction d generalizing j with
    | zero => simpa [search,show j=7 by omega] using last
    | succ d ih =>
      have recurse := ih (j+1) (by omega)
      have col := north.column j (by omega)
      rw [show idx u j=j by simp [idx,show j<15 by omega]] at col
      simp only [search,List.any_eq_true,List.mem_range,Bool.and_eq_true]
      refine ⟨a j,north.small j,⟨?_,?_⟩,?_⟩
      · simpa [frontCols] using col
      · by_cases z : j=0
        · simp [z,frontCols]
        · have J : (frontCols a j).length=j := by simp [frontCols]
          have step := north.step (j-1) (by omega)
          rw [show idx u (j-1)=j-1 by simp [idx,show j-1<15 by omega]] at step
          simp only [J,Bool.or_eq_true]; right
          rw [prefix_at a (by omega)]
          by_cases o : j=1
          · subst j; simpa [frontCols,show 1≠35+42*u by omega] using step
          · rw [if_neg o,prefix_at a (by omega)]
            simpa only [if_neg (by omega : ¬j-1=0),if_neg (by omega : ¬j-1+1=35+42*u),
              show j-1+1=j by omega,if_neg (by omega : ¬j=35+42*u),Nat.sub_sub] using step
      · simpa [frontCols,List.range_succ] using recurse
  have positive := go 7 0 rfl
  simp [frontCols,no_corner] at positive

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
