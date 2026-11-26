import GridGraphs.ResidueTwoUpper.PeriodThree
import GridGraphs.ResidueTwoUpper.Location
import GridGraphs.ResidueTwoUpper.Patch
import GridGraphs.NoPitch.ColumnProjection

/-! Actual nine-bit physical patch occurrences have decoded columns at
every tail width, including fixed loci of the grid symmetries. -/
namespace GridGraphs.ResidueTwoUpper.PatchColumns
open NoPitch.Dual NoPitch.Keys Location Patch

def rotate (m : Fin 512) (g : Fin 8) : Nat :=
  (List.range 9).foldl (fun a i =>
    let p := small 3 (invers g) (Fin.ofNat 3 (i/3),Fin.ofNat 3 i)
    a + (bit m p).toNat * 2^i) 0

def key (s i j : Nat) (m : Fin 512) :=
  2*(minimum fun g =>
    let p := transform g s i j
    (Location.axis s 5 p.1*16+Location.axis s 5 p.2)*512+rotate m g)+1

def baseCoverage (D : Chart) :=
  let idx := index D
  decide (∀ i j : Fin 18, ∀ m : Fin 512, allowed m →
    (locate D idx (key 18 i j m)).isSome)

theorem base_checked : baseCoverage periodThree := by native_decide

theorem key_reduce {i j t : Nat} (hi : i<18+3*t) (hj : j<18+3*t) (m : Fin 512) :
    key (18+3*t) i j m = key 18 (rep (18+3*t) 5 i) (rep (18+3*t) 5 j) m := by
  have m₁ := fine_matches (d:=5) (t:=t) hi
  have m₂ := fine_matches (d:=5) (t:=t) hj
  have r₁ := reflected_fine_matches (d:=5) (t:=t) hi
  have r₂ := reflected_fine_matches (d:=5) (t:=t) hj
  have bj : rep (18+3*t) 5 j <18 := rep_valid (d:=5) (t:=t) hj
  have rev : 17+3*t-(17+3*t-j)=j := by omega
  have rev' : 17-(17-rep (18+3*t) 5 j)=rep (18+3*t) 5 j := by omega
  norm_num at r₁ r₂
  apply congrArg (fun z : Nat => 2*z+1)
  apply congrArg minimum
  funext g
  fin_cases g <;> simp [transform] <;>
    simp_all only [Nat.reduceMul,Nat.reduceAdd]

theorem physical_patch_found {t a b : Nat} (ha : a<18+3*t) (hb : b<18+3*t)
    (F : Finset (GridVertex (20+3*t) (20+3*t)))
    (h : (forcedEdgeGraph (gridGraph (20+3*t) (20+3*t)) (↑F : Set _)).IsAcyclic) :
    (locate periodThree (index periodThree) (key (18+3*t) a b
      (patchMask (a:=a) (b:=b) (by omega) (by omega) F))).isSome := by
  let m := patchMask (a:=a) (b:=b) (by omega) (by omega) F
  have good : allowed m := physical_allowed _ _ F h
  rw [key_reduce ha hb]
  have covers (i j : Fin 18) (z : Fin 512) (hz : allowed z) :
      (locate periodThree (index periodThree) (key 18 i j z)).isSome := by
    have hc := base_checked
    unfold baseCoverage at hc
    exact (of_decide_eq_true hc) i j z hz
  exact covers ⟨_,rep_valid (d:=5) (t:=t) ha⟩ ⟨_,rep_valid (d:=5) (t:=t) hb⟩ m good

end GridGraphs.ResidueTwoUpper.PatchColumns
