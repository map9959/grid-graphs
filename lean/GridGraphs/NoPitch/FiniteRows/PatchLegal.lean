import GridGraphs.NoPitch.TailRows.PatchTransport

namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset TailRows Wired
variable {k : Nat}

theorem legal_small {k} (F : Finset (Site k)) (hk : 7≤k) (acy : (Budget.G F).IsAcyclic)
    (p : PatchPos k) : legal (patchMask F p) := by
  let place (v : V) : Site k := (Fin.ofNat (N k) (p.1.val+(cell v).1.val),Fin.ofNat (N k) (p.2.val+(cell v).2.val))
  have encode : ∀ x y : V, cell x=cell y → x=y := by decide +kernel
  have same (a : Fin (N k-2)) (b c : Fin 4)
      (eq : (a.val+b.val)%(N k)=(a.val+c.val)%(N k)) : b=c := by
    have := a.isLt; have := b.isLt; have := c.isLt
    have red (x : Fin 4) : (a.val+x.val)%(N k)=if a.val+x.val<N k then a.val+x.val else 0 := by
      have := x.isLt; unfold N at *; split
      · exact Nat.mod_eq_of_lt ‹_›
      · rw [show a.val+x.val=3*k+1 by omega,Nat.mod_self]
    rw [red,red] at eq; apply Fin.ext; unfold N at *; split_ifs at eq <;> omega
  have inj : Function.Injective place := by
    intro x y eq
    have r := congrArg (fun z : Site k => z.1.val) eq
    have c := congrArg (fun z : Site k => z.2.val) eq
    exact encode _ _ (Prod.ext (same _ _ _ r) (same _ _ _ c))
  have localGeo : ∀ e∈edges, e.1<e.2 ∧ (gridGraph 4 4).Adj (cell e.1) (cell e.2) ∧
      inside e.1 ∧ inside e.2 := by decide +kernel
  have nd : edges.Nodup := by decide +kernel
  apply fresh_of_forest _ inj (Budget.G F) acy _ (nd.filter _) _ ⊥ bot_le
  · intro x y h; have eq : x=y := by simpa [initial] using h
    rw [eq]
  · intro e he
    obtain ⟨me,m⟩ := List.mem_filter.mp he
    obtain ⟨ord,a,hu,hv⟩ := localGeo _ me
    have bounds (v : V) (h : inside v) := Bool.and_eq_true_iff.mp h
    have ru := bounds _ hu; have rv := bounds _ hv
    simp only [decide_eq_true_eq] at ru rv
    have br := p.1.isLt; have bc := p.2.isLt
    refine ⟨ord,⟨?_,?_⟩,by simp⟩
    · change adjacent _ _ _ _ at a ⊢
      simp only [adjacent,place,Fin.ext_iff,Fin.val_ofNat] at a ⊢
      simp (disch := omega) only [Nat.mod_eq_of_lt]; omega
    · simp only [Bool.or_eq_true,patchMask,quad,Fin.val_ofNat] at m
      simp (disch := omega) only [Nat.mod_eq_of_lt] at m
      exact m.imp of_decide_eq_true of_decide_eq_true


end GridGraphs.NoPitch.FiniteRows
