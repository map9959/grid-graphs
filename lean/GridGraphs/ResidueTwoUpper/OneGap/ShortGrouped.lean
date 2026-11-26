import GridGraphs.ResidueTwoUpper.OneGap.ShortKernelProof

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7

/-- Union the seeds across several indices *at each physical origin*.
This can weaken a test, but never deletes the actual common isolate. -/
@[noinline] def pooled (n lo hi : Nat) (w : View) (base : Board) : Board :=
  build (n-2) fun r c =>
    let t := unview w (n-2) r c
    let xs := atRC base r c
    let exempt := t.1=1 ∧ t.2%6=4 ∧ 1+3*lo≤t.2 ∧ t.2≤1+3*hi
    let core := if exempt then
      ((List.range 512).filter fun m => encode (Fin.ofNat 512 m) w==64).map (·,4) else []
    let other := if t.1=1 ∧ t.2%3=1 then xs.filter fun z =>
      (t.2<1+3*hi && bitCenter z.1) ||
      (1+3*lo<t.2 && encode (Fin.ofNat 512 z.1) w==72)
    else xs
    core++other
where bitCenter (m : Nat) := ResidueZero.bit m 4==1

theorem pool_sound {s n q lo hi w base M} (sz : n-2=s) (odd : q%2=1) (low : lo≤q) (high : q≤hi)
    (h : Kept s M (planted n q w base)) : Kept s M (pooled n lo hi w base) := by
  subst s; intro r hr c hc
  have mem := h r hr c hc
  unfold planted at mem; rw [at_build hr hc] at mem
  unfold pooled; rw [at_build hr hc,List.mem_append]
  generalize eq : unview w (n-2) r c=t at mem ⊢
  by_cases paid : t=(1,1+3*q)
  · rw [if_pos paid] at mem
    have xy := eq.trans paid
    rw [paid]; left
    have phase : (1+3*q)%6=4 := by omega
    simp only [List.mem_map,List.mem_filter,List.mem_range] at mem
    obtain ⟨m,⟨hm,ok⟩,em⟩ := mem
    unfold seedOK at ok
    rw [xy] at ok
    dsimp only at ok ⊢
    have pin : encode (Fin.ofNat 512 m) w==64 := by
      simpa only [show (1+3*q)%3=1 by omega,eq_self,true_and,if_true,lt_irrefl,if_false] using ok
    have yes : (1:Nat)=1 ∧ (1+3*q)%6=4 ∧ 1+3*lo≤1+3*q ∧ 1+3*q≤1+3*hi := by omega
    rw [if_pos yes]
    exact List.mem_map.mpr ⟨m,List.mem_filter.mpr ⟨List.mem_range.mpr hm,pin⟩,em⟩
  · rw [if_neg paid] at mem
    obtain ⟨allowed,seed⟩ := List.mem_filter.mp mem
    right; by_cases al : t.1=1 ∧ t.2%3=1
    swap
    · simpa only [if_neg al] using allowed
    rw [if_pos al]; apply List.mem_filter.mpr; refine ⟨allowed,?_⟩
    unfold seedOK at seed; rw [eq] at seed
    rcases t with ⟨a,b⟩; dsimp only at al seed ⊢; rw [if_pos al] at seed
    by_cases west : b<1+3*q
    · rw [if_pos west] at seed
      simp [show b<1+3*hi by omega,pooled.bitCenter,seed]
    · have ne : b≠1+3*q := fun h => paid (Prod.ext al.1 h)
      rw [if_neg west,if_neg ne] at seed
      exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr ⟨decide_eq_true (by omega),seed⟩))

@[noinline] def groupTest (s n lo hi : Nat) (w : View) (base : Board) :=
  Kernel.run s 8 (Kernel.prune s 18 (pooled n lo hi w base))

theorem group_excludes (u q lo hi : Nat) (w : View)
    (ok : groupTest (33+42*u) (35+42*u) lo hi w (cached u chart))
    {F : Finset (GridVertex (35+42*u) (35+42*u))} {P} (S : Seed F P w q)
    (acy : (ResidueZero.Bonds F).IsAcyclic) (low : lo≤q) (high : q≤hi) : False := by
  have e := actual_agree F P S.step S.owners
  have B := pool_sound rfl S.odd low high (kept_physical S acy)
  rw [show 35+42*u-2=33+42*u by omega] at B e
  unfold groupTest at ok
  rw [cached_eq] at ok
  exact kernel_excludes ok e B
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
