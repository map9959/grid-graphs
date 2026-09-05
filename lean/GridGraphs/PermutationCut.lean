import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Finite permutation cuts

An orbit of a finite permutation that enters a finite set must leave it again.
This elementary cut-balance fact will identify the two orientations of every
bridge in the contour permutation of an embedded tree.
-/

namespace GridGraphs

open Finset

/-- If `enter` crosses from outside `S` to inside and `leave` is the unique
point crossing from inside to outside, then both points lie in the same orbit
of a finite permutation. -/
theorem Equiv.Perm.sameCycle_of_unique_leave
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {enter leave : α}
    (henterOut : enter ∉ S) (henterIn : f enter ∈ S)
    (hleaveUnique : ∀ x, x ∈ S → f x ∉ S → x = leave) :
    f.SameCycle enter leave := by
  classical
  let C : Finset α := Finset.univ.filter fun x => f.SameCycle enter x
  have henterC : enter ∈ C := by
    simp [C, Equiv.Perm.SameCycle.refl]
  have hC_apply (x : α) : x ∈ C ↔ f x ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Equiv.Perm.sameCycle_apply_right.symm
  have hexit : ∃ x ∈ C, x ∈ S ∧ f x ∉ S := by
    by_contra hnone
    push_neg at hnone
    let A := C ∩ S
    have hmap : A.image f ⊆ A := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hxA, rfl⟩ := hy
      have hxC : x ∈ C := (Finset.mem_inter.mp hxA).1
      have hxS : x ∈ S := (Finset.mem_inter.mp hxA).2
      have hfxS : f x ∈ S := hnone x hxC hxS
      exact Finset.mem_inter.mpr ⟨(hC_apply x).mp hxC, hfxS⟩
    have hcard : (A.image f).card = A.card :=
      Finset.card_image_iff.mpr (fun _ _ _ _ h => f.injective h)
    have hmapEq : A.image f = A :=
      Finset.eq_of_subset_of_card_le hmap (by omega)
    have hfenterC : f enter ∈ C := (hC_apply enter).mp henterC
    have hfenterA : f enter ∈ A := Finset.mem_inter.mpr ⟨hfenterC, henterIn⟩
    rw [← hmapEq, Finset.mem_image] at hfenterA
    obtain ⟨x, hxA, hx⟩ := hfenterA
    have hxeq : x = enter := f.injective hx
    subst x
    exact henterOut (Finset.mem_inter.mp hxA).2
  obtain ⟨x, hxC, hxS, hfxS⟩ := hexit
  have hxleave := hleaveUnique x hxS hfxS
  subst x
  exact (Finset.mem_filter.mp hxC).2

/-! ## Finite forward intervals -/

/-- Least nonnegative forward exponent from `start` to `finish` in one orbit. -/
noncomputable def permForwardDistance
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish) : Nat :=
  Nat.find hsame.exists_pow_eq'

theorem permForwardDistance_spec
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish) :
    (f ^ permForwardDistance f start finish hsame) start = finish :=
  (Nat.find_spec hsame.exists_pow_eq').2

theorem permForwardDistance_lt_orderOf
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish) :
    permForwardDistance f start finish hsame < orderOf f :=
  (Nat.find_spec hsame.exists_pow_eq').1

/-- Forward distances between two distinct points in a nontrivial cycle fill
the whole cycle. -/
theorem permForwardDistance_add_reverse_eq_orderOf
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hforward : f.SameCycle start finish)
    (hbackward : f.SameCycle finish start)
    (hf : f.IsCycle) (hmove : f start ≠ start) (hne : start ≠ finish) :
    permForwardDistance f start finish hforward +
        permForwardDistance f finish start hbackward = orderOf f := by
  let d := permForwardDistance f start finish hforward
  let e := permForwardDistance f finish start hbackward
  have hdpos : 0 < d := by
    by_contra h
    have hd : d = 0 := Nat.eq_zero_of_not_pos h
    have hspec := permForwardDistance_spec f start finish hforward
    simp [d, hd] at hspec
    exact hne hspec
  have hfix : (f ^ (d + e)) start = start := by
    rw [show d + e = e + d by omega, pow_add, Equiv.Perm.mul_apply,
      permForwardDistance_spec f start finish hforward,
      permForwardDistance_spec f finish start hbackward]
  have hpow : f ^ (d + e) = 1 :=
    (hf.pow_eq_one_iff' hmove).2 (by simpa using hfix)
  have hlower : orderOf f ≤ d + e :=
    Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)
  have heupper : e ≤ orderOf f - d := by
    apply Nat.find_min'
    constructor
    · have hdlt := permForwardDistance_lt_orderOf f start finish hforward
      omega
    · have hfinish : finish = (f ^ d) start :=
        (permForwardDistance_spec f start finish hforward).symm
      rw [hfinish, ← Equiv.Perm.mul_apply, ← pow_add]
      rw [show orderOf f - d + d = orderOf f by
        exact Nat.sub_add_cancel
          (Nat.le_of_lt (permForwardDistance_lt_orderOf f start finish hforward))]
      simp
  have hupper : d + e ≤ orderOf f := by
    have hdle := Nat.le_of_lt
      (permForwardDistance_lt_orderOf f start finish hforward)
    omega
  omega

/-- Finite open forward interval between two elements in one permutation orbit. -/
noncomputable def permOpenForwardInterval
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish) : Finset α :=
  @Finset.filter α (fun x => ∃ k,
    0 < k ∧ k < permForwardDistance f start finish hsame ∧ (f ^ k) start = x)
    (Classical.decPred _) Finset.univ

/-- Finite forward segment after `start`, including `finish`. -/
noncomputable def permClosedForwardInterval
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish) : Finset α :=
  @Finset.filter α (fun x => ∃ k,
    0 < k ∧ k ≤ permForwardDistance f start finish hsame ∧ (f ^ k) start = x)
    (Classical.decPred _) Finset.univ

@[simp] theorem mem_permOpenForwardInterval_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish x : α)
    (hsame : f.SameCycle start finish) :
    x ∈ permOpenForwardInterval f start finish hsame ↔
      ∃ k, 0 < k ∧ k < permForwardDistance f start finish hsame ∧
        (f ^ k) start = x := by
  simp [permOpenForwardInterval]

@[simp] theorem mem_permClosedForwardInterval_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish x : α)
    (hsame : f.SameCycle start finish) :
    x ∈ permClosedForwardInterval f start finish hsame ↔
      ∃ k, 0 < k ∧ k ≤ permForwardDistance f start finish hsame ∧
        (f ^ k) start = x := by
  simp [permClosedForwardInterval]

/-! ## A single-entry, single-exit cut -/

/-- After crossing the unique entry of a permutation cut, every iterate through
the unique exit remains in the cut. -/
theorem Equiv.Perm.pow_mem_of_pos_le_permForwardDistance_of_unique_exit
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {entry exit : α}
    (hsame : f.SameCycle entry exit)
    (hentryIn : f entry ∈ S)
    (hexit : ∀ x, x ∈ S → (f x ∉ S ↔ x = exit))
    {k : Nat} (hkpos : 0 < k)
    (hkle : k ≤ permForwardDistance f entry exit hsame) :
    (f ^ k) entry ∈ S := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hkzero : k = 0
      · subst k
        simpa using hentryIn
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
        have hklt : k < permForwardDistance f entry exit hsame := by omega
        have hprev : (f ^ k) entry ∈ S := ih hkpos (by omega)
        rw [pow_succ', Equiv.Perm.mul_apply]
        by_contra hnext
        have hprevExit : (f ^ k) entry = exit :=
          (hexit ((f ^ k) entry) hprev).mp hnext
        have hdistance_le : permForwardDistance f entry exit hsame ≤ k := by
          apply Nat.find_min'
          exact ⟨Nat.lt_trans hklt
            (permForwardDistance_lt_orderOf f entry exit hsame), hprevExit⟩
        omega

/-- After crossing the unique exit of a permutation cut, every iterate through
the next entry remains outside the cut. -/
theorem Equiv.Perm.pow_notMem_of_pos_le_permForwardDistance_of_unique_entry
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {exit entry : α}
    (hsame : f.SameCycle exit entry)
    (hexitOut : f exit ∉ S)
    (hentry : ∀ x, x ∉ S → (f x ∈ S ↔ x = entry))
    {k : Nat} (hkpos : 0 < k)
    (hkle : k ≤ permForwardDistance f exit entry hsame) :
    (f ^ k) exit ∉ S := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hkzero : k = 0
      · subst k
        simpa using hexitOut
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
        have hklt : k < permForwardDistance f exit entry hsame := by omega
        have hprev : (f ^ k) exit ∉ S := ih hkpos (by omega)
        rw [pow_succ', Equiv.Perm.mul_apply]
        intro hnext
        have hprevEntry : (f ^ k) exit = entry :=
          (hentry ((f ^ k) exit) hprev).mp hnext
        have hdistance_le : permForwardDistance f exit entry hsame ≤ k := by
          apply Nat.find_min'
          exact ⟨Nat.lt_trans hklt
            (permForwardDistance_lt_orderOf f exit entry hsame), hprevEntry⟩
        omega

/-- The open forward interval from the unique entry to the unique exit lies in
the cut. -/
theorem Equiv.Perm.permOpenForwardInterval_subset_of_unique_exit
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {entry exit : α}
    (hsame : f.SameCycle entry exit)
    (hentryIn : f entry ∈ S)
    (hexit : ∀ x, x ∈ S → (f x ∉ S ↔ x = exit)) :
    permOpenForwardInterval f entry exit hsame ⊆ S := by
  intro x hx
  obtain ⟨k, hkpos, hklt, rfl⟩ :=
    (mem_permOpenForwardInterval_iff f entry exit x hsame).mp hx
  exact Equiv.Perm.pow_mem_of_pos_le_permForwardDistance_of_unique_exit
    f S hsame hentryIn hexit hkpos (Nat.le_of_lt hklt)

/-- The complementary open forward interval from the unique exit to the next
entry lies outside the cut. -/
theorem Equiv.Perm.disjoint_permOpenForwardInterval_of_unique_entry
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {exit entry : α}
    (hsame : f.SameCycle exit entry)
    (hexitOut : f exit ∉ S)
    (hentry : ∀ x, x ∉ S → (f x ∈ S ↔ x = entry)) :
    Disjoint (permOpenForwardInterval f exit entry hsame) S := by
  rw [Finset.disjoint_left]
  intro x hxInterval hxS
  obtain ⟨k, hkpos, hklt, rfl⟩ :=
    (mem_permOpenForwardInterval_iff f exit entry x hsame).mp hxInterval
  exact (Equiv.Perm.pow_notMem_of_pos_le_permForwardDistance_of_unique_entry
    f S hsame hexitOut hentry hkpos (Nat.le_of_lt hklt)) hxS

/-- In a one-cycle permutation cut, every point of the cut occurs after the
unique entry and no later than the unique exit. -/
theorem Equiv.Perm.mem_closedForwardInterval_of_unique_entry_exit
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {entry exit : α}
    (hf : f.IsCycle) (hall : ∀ x, f.SameCycle entry x)
    (hentryOut : entry ∉ S) (hentryIn : f entry ∈ S)
    (hexit : ∀ x, x ∈ S → (f x ∉ S ↔ x = exit))
    (hentry : ∀ x, x ∉ S → (f x ∈ S ↔ x = entry))
    {x : α} (hx : x ∈ S) :
    x ∈ permClosedForwardInterval f entry exit (hall exit) := by
  have hmove : f entry ≠ entry := by
    intro h
    exact hentryOut (h ▸ hentryIn)
  have hexitMem : exit ∈ S := by
    by_contra hexitOut
    have hclosed : ∀ y, y ∈ S → f y ∈ S := by
      intro y hy
      by_contra hfy
      have hyExit := (hexit y hy).mp hfy
      exact hexitOut (hyExit ▸ hy)
    let A := S.image f
    have hAS : A ⊆ S := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact hclosed z hz
    have hcard : A.card = S.card :=
      Finset.card_image_iff.mpr (fun _ _ _ _ h => f.injective h)
    have hEq : A = S := Finset.eq_of_subset_of_card_le hAS (by omega)
    have hfentry : f entry ∈ A := hEq ▸ hentryIn
    obtain ⟨z, hz, hzentry⟩ := Finset.mem_image.mp hfentry
    exact hentryOut (f.injective hzentry ▸ hz)
  have hne : entry ≠ exit := fun h => hentryOut (h ▸ hexitMem)
  let hforward := hall exit
  let hbackward := hforward.symm
  let d := permForwardDistance f entry exit hforward
  let e := permForwardDistance f exit entry hbackward
  have hsum : d + e = orderOf f :=
    permForwardDistance_add_reverse_eq_orderOf f entry exit hforward hbackward
      hf hmove hne
  obtain ⟨k, hklt, hk⟩ := (hall x).exists_pow_eq'
  have hkpos : 0 < k := by
    by_contra hknot
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hknot
    subst k
    simp at hk
    exact hentryOut (hk ▸ hx)
  rw [mem_permClosedForwardInterval_iff]
  refine ⟨k, hkpos, ?_, hk⟩
  by_contra hnot
  have hdk : d < k := by omega
  let j := k - d
  have hjpos : 0 < j := by omega
  have hjle : j ≤ e := by
    have hklt' : k < orderOf f := by simpa using hklt
    omega
  have hjpow : (f ^ j) exit = x := by
    rw [show exit = (f ^ d) entry by
      exact (permForwardDistance_spec f entry exit hforward).symm]
    rw [← Equiv.Perm.mul_apply, ← pow_add]
    have hjd : j + d = k := by
      simp [j, Nat.sub_add_cancel (Nat.le_of_lt hdk)]
    simpa [hjd] using hk
  have hjOut := Equiv.Perm.pow_notMem_of_pos_le_permForwardDistance_of_unique_entry
    f S hbackward (by
      simpa [permForwardDistance_spec f entry exit hforward] using
        (hexit exit hexitMem).2 rfl) hentry hjpos hjle
  exact hjOut (hjpow ▸ hx)

/-- Exact set form of the one-cycle permutation-cut characterization. -/
theorem Equiv.Perm.eq_closedForwardInterval_of_unique_entry_exit
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {entry exit : α}
    (hf : f.IsCycle) (hall : ∀ x, f.SameCycle entry x)
    (hentryOut : entry ∉ S) (hentryIn : f entry ∈ S)
    (hexit : ∀ x, x ∈ S → (f x ∉ S ↔ x = exit))
    (hentry : ∀ x, x ∉ S → (f x ∈ S ↔ x = entry)) :
    S = permClosedForwardInterval f entry exit (hall exit) := by
  apply Finset.Subset.antisymm
  · intro x hx
    exact Equiv.Perm.mem_closedForwardInterval_of_unique_entry_exit f S hf hall
      hentryOut hentryIn hexit hentry hx
  · intro x hx
    obtain ⟨k, hkpos, hkle, rfl⟩ :=
      (mem_permClosedForwardInterval_iff f entry exit x (hall exit)).mp hx
    exact Equiv.Perm.pow_mem_of_pos_le_permForwardDistance_of_unique_exit
      f S (hall exit) hentryIn hexit hkpos hkle

end GridGraphs
