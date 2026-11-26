import GridGraphs.ResidueZero.LocationTransport
import GridGraphs.ResidueZero.Replay
import GridGraphs.ResidueZero.Budget
import GridGraphs.ResidueZero.PhysicalPatch
import GridGraphs.Results.ExactSquareFormula

namespace GridGraphs.ResidueZero
open Finset

private theorem fromStar {n : Nat} (checked : starCheck n) {p : Pos} (hp : inside n p)
    {f nb o : Nat} (hf : f<2) (hn : nb<16) (ho : o<5) (ok : starOK n p f nb o) :
    0 ≤ orbitStar n p f nb o := by
  simp [starCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) f (by omega) nb (by omega) o (by omega)
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

private theorem fromPatch {n : Nat} (checked : patchCheck n) {p : Pos} (hp : inside (n-2:Nat) p)
    {m : Nat} (hm : m<512) (ok : maskOK m) : 0 ≤ orbitPatch n p m := by
  simp [patchCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) m hm
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

private theorem rep_inside {b j : Int} (hb : 19≤b) (hj : 0≤j) {p : Pos} (h : inside (b+3*j) p) :
    inside b (representative b j p) := by
  simp [inside] at h
  have hr := rep_bounds hb hj (i:=p.1) (by omega) (by omega)
  have hc := rep_bounds hb hj (i:=p.2) (by omega) (by omega)
  have ok {q : Pos} (a : 0≤q.1) (b' : q.1<b) (c : 0≤q.2) (d : q.2<b) :
      inside b q := by simp [inside,a,b',c,d]
  exact ok hr.1 hr.2 hc.1 hc.2

theorem star_nonneg {k : Nat} (hk : 4≤k) {p : Pos} (hp : inside (3*k:Nat) p)
    {f nb o : Nat} (hf : f<2) (hn : nb<16) (ho : o<5) (ok : starOK (3*k:Nat) p f nb o) :
    0 ≤ orbitStar (3*k:Nat) p f nb o := by
  have checks := starChecks
  simp only [Bool.and_eq_true] at checks
  by_cases h : k<7
  · interval_cases k
    · exact fromStar (n:=12) checks.1.1.1 hp hf hn ho ok
    · exact fromStar (n:=15) checks.1.1.2 hp hf hn ho ok
    · exact fromStar (n:=18) checks.1.2 hp hf hn ho ok
  · let j := k-7
    have en : ((3*k:Nat):Int)=21+3*(j:Int) := by dsimp [j]; omega
    rw [en,orbitStar_transport]
    rw [en,starOK_transport] at ok
    rw [en] at hp
    exact fromStar (n:=21) checks.2 (rep_inside (by decide) (by positivity) hp) hf hn ho ok

theorem patch_nonneg {k : Nat} (hk : 4≤k) {p : Pos} (hp : inside (3*k-2:Nat) p)
    {m : Nat} (hm : m<512) (ok : maskOK m) : 0 ≤ orbitPatch (3*k:Nat) p m := by
  have checks := patchChecks
  simp only [Bool.and_eq_true] at checks
  by_cases h : k<7
  · interval_cases k
    · exact fromPatch (n:=12) checks.1.1.1 hp hm ok
    · exact fromPatch (n:=15) checks.1.1.2 hp hm ok
    · exact fromPatch (n:=18) checks.1.2 hp hm ok
  · let j := k-7
    have en : ((3*k:Nat):Int)=21+3*(j:Int) := by dsimp [j]; omega
    have ep : ((3*k-2:Nat):Int)=19+3*(j:Int) := by dsimp [j]; omega
    rw [en,orbitPatch_transport]
    rw [ep] at hp
    exact fromPatch (n:=21) checks.2 (rep_inside (by decide) (by positivity) hp) hm ok

theorem physicalPatch_nonneg {k : Nat} (hk : 4≤k) (F : Finset (GridVertex (3*k) (3*k)))
    (acy : (forcedEdgeGraph (gridGraph (3*k) (3*k)) (↑F : Set _)).IsAcyclic)
    (r c : Nat) (hr : r+3≤3*k) (hc : c+3≤3*k) :
    0 ≤ orbitPatch (3*k:Nat) (r,c) (physicalMask F r c hr hc) :=
  patch_nonneg hk (by simp [inside]; omega) (Fin.isLt _) (physical_mask_ok F acy r c hr hc)

theorem budget_eq_score {k : Nat} (hk : 4≤k) :
    normBudget (3*k) = scale*(squareScore (3*k):Int) := by
  by_cases h : k<7
  · have ⟨a,b,c⟩ := smallBudgets
    interval_cases k
    · exact a
    · exact b
    · exact c
  · let j := k-7
    have eq : 3*k=21+3*j := by dsimp [j]; omega
    rw [eq,budget_width,←eq,squareScore_three_mul,Nat.cast_sub (by nlinarith : 2≤3*k^2+3*k)]
    push_cast
    have : (k:Int)=7+j := by dsimp [j]; omega
    rw [this]; ring

end GridGraphs.ResidueZero
