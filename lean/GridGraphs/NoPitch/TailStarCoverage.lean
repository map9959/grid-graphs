import GridGraphs.NoPitch.TailCoverageGeometry
import GridGraphs.Tests.PhysicalColumnReplay

namespace GridGraphs.NoPitch.TailCoverage
open PitchCut Keys GridGraphs.NoPitch.Dual

private def step (d plus minus : Nat) : Int :=
  if d=plus then 1 else if d=minus then -1 else 0

private theorem step_bound (d p m) : -1 ≤ step d p m ∧ step d p m ≤ 1 := by
  unfold step
  by_cases h : d=p
  · rw [if_pos h]; decide
  · rw [if_neg h]; split <;> decide

private theorem Axis.inside {l m z t} (h : Axis l m z t) (v : Int)
    (hv : -1≤v ∧ v≤1) :
    (0≤(z:Int)+v ∧ ((z:Int)+v).toNat<l+1) ↔
    (0≤(t:Int)+v ∧ ((t:Int)+v).toNat < m+1) := by
  rcases h with ⟨_,_,_,h₁,h₂⟩
  unfold Sat at h₁ h₂
  omega

private theorem probe_eq {k t : Nat} {x : Site k} {y : Site t}
    (h : Match (3*k) (3*t) x.1.val x.2.val y.1.val y.2.val) (d : Nat) :
    (probe x d).isSome = (probe y d).isSome := by
  have u := h.row.inside _ (step_bound d 1 3)
  have v := h.col.inside _ (step_bound d 0 2)
  unfold step at u v
  unfold probe
  simp only [dite_eq_ite,apply_dite Option.isSome,Option.isSome_some,Option.isSome_none]
  simp only [N] at *
  grind only

private theorem probe_coords {k} {x a : Site k} {d : Nat} (hit : probe x d=some a) :
    (a.1.val:Int)=x.1.val+step d 1 3 ∧ (a.2.val:Int)=x.2.val+step d 0 2 := by
  unfold probe at hit
  simp only [Option.dite_none_right_eq_some,Option.some.injEq] at hit
  obtain ⟨ok,rfl⟩ := hit
  simp only [step,Int.toNat_of_nonneg ok.1,Int.toNat_of_nonneg ok.2.1,and_self]

private theorem diag_probe {k t} {x : Site k} {y : Site t} {d e : Nat}
    {a b : Site k} {c f : Site t}
    (ha : probe x d=some a) (hb : probe x e=some b)
    (hc : probe y d=some c) (hf : probe y e=some f) : diagonal a b=diagonal c f := by
  have := probe_coords ha; have := probe_coords hb
  have := probe_coords hc; have := probe_coords hf
  simp only [diagonal,decide_eq_decide]; omega

private theorem allowed_move {k t} {x : Site k} {y : Site t}
    (h : Match (3*k) (3*t) x.1.val x.2.val y.1.val y.2.val) {bits}
    (good : allowed x bits) : allowed y bits := by
  intro d e hd he
  have g := good d e hd he
  have i := probe_eq h d; have j := probe_eq h e
  cases hc : probe y d with
  | none => rfl
  | some c =>
    cases hf : probe y e with
    | none => rfl
    | some f =>
      cases ha : probe x d with
      | none => simp [ha,hc] at i
      | some a =>
        cases hb : probe x e with
        | none => simp [hb,hf] at j
        | some b => simpa [ha,hb,diag_probe ha hb hc hf,hc,hf] using g

set_option maxHeartbeats 400000 in
/-- Coverage at a tail width implies coverage six columns later. -/
theorem covers_step {D : Chart} {k} (hk : 19≤k) (base : covers D k) :
    covers D (k+2) := by
  unfold covers
  dsimp only
  rw [decide_eq_true_eq]
  intro x bits good o inside
  obtain ⟨a,b,h⟩ := representative (m:=3*k) (by omega)
    (i:=x.1.val) (j:=x.2.val) (by have := x.1.isLt; unfold N at this; omega)
    (by have := x.2.isLt; unfold N at this; omega)
  let y : Site k := (⟨a,by have := h.row.dst; unfold N; omega⟩,
    ⟨b,by have := h.col.dst; unfold N; omega⟩)
  have w : 3*(k+2)=3*k+6 := by omega
  have hm : Match (3*(k+2)) (3*k) x.1.val x.2.val y.1.val y.2.val := by
    change Match (3*(k+2)) (3*k) _ _ a b
    rw [w]; exact h
  have hit := of_decide_eq_true base y bits (allowed_move hm good) o
    (fun d hd => (probe_eq hm d).symm.trans (inside d hd))
  have eq : starCode (N (k+2)) x.1.val x.2.val (sampled x bits) o =
      starCode (N k) y.1.val y.2.val (sampled y bits) o := by
    unfold starCode
    congr 1; funext g
    simp only [hm.view w g,sampled,probe_eq hm,N]
  exact (congrArg (fun z => (locate D (index D) (8*z+1)).isSome) eq).trans hit

def tailChart (k : Nat) := if k%2=1 then chart58 else chart61

theorem covers_tail {k} (hk : 19≤k) : covers (tailChart k) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k≤20
    · interval_cases k
      · exact (Bool.and_eq_true_iff.mp column58).2
      · exact (Bool.and_eq_true_iff.mp column61).2
    · have h₂ : k-2+2=k := by omega
      have r := covers_step (k:=k-2) (by omega) (ih (k-2) (by omega) (by omega))
      simpa [h₂,tailChart,show (k-2)%2=k%2 by omega] using r

theorem occupied_tail {k} (hk : 19≤k) (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (out : Site k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (probe x d.val).isSome)
    (x : Site k) (hx : x∈F) :
    (locate (tailChart k) (index (tailChart k)) (star F out x)).isSome :=
  occupied_covered (covers_tail hk) F acy out inside x hx

theorem objective_tail {k} (hk : 19≤k) (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (out : Site k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (probe x d.val).isSome) :
    score (tailChart k) (physicalVector (tailChart k) F out)=8*(F.card:Int) := by
  apply vector_objective _ _ (covers_tail hk) F acy out inside
  · unfold tailChart; split
    · exact (Bool.and_eq_true_iff.mp column58).1
    · exact (Bool.and_eq_true_iff.mp column61).1
  · unfold tailChart; split
    · exact (Bool.and_eq_true_iff.mp (dictionaries .n58)).2
    · exact (Bool.and_eq_true_iff.mp (dictionaries .n61)).2

end GridGraphs.NoPitch.TailCoverage
