import GridGraphs.NoPitch.TailRows.StarTransport

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget Finset LocalBoard19 Wired
variable {k : Nat}

def patchCenter (p : PatchPos k) : Site k :=
  (⟨p.1.val+1,by have := p.1.isLt; omega⟩,⟨p.2.val+1,by have := p.2.isLt; omega⟩)
def patchFine (p : PatchPos k) (g : Fin 8) :=
  let q := transform g (N k-2) p.1.val p.2.val
  fine (N k-2) 7 q.1 q.2
def innerLabel (p : List Nat) := [p[0]!-1,p[1]!-1,p[2]!,p[3]!]

theorem patch_type (p : PatchPos k) (g : Fin 8) :
    patchFine p g=innerLabel (fine (N k) 8 (turn g (patchCenter p)).1.val (turn g (patchCenter p)).2.val) := by
  have hr := p.1.isLt; have hc := p.2.isLt
  have nk : N k=3*k+1 := rfl
  have ax (z : Nat) (hz : z<N k-2) : axis (N k-2) 7 z=axis (N k) 8 (z+1)-1 := by
    unfold axis; split_ifs <;> omega
  let y := transform g (N k-2) p.1.val p.2.val
  have move : ((turn g (patchCenter p)).1.val,(turn g (patchCenter p)).2.val)=(y.1+1,y.2+1) := by
    rw [turn_values]; fin_cases g <;> simp [y,transform,patchCenter] <;> omega
  have by₁ : y.1<N k-2 ∧ y.2<N k-2 := by fin_cases g <;> simp [y,transform] <;> omega
  change fine (N k-2) 7 y.1 y.2=_
  have e₁ := congrArg Prod.fst move; have e₂ := congrArg Prod.snd move
  change (turn g (patchCenter p)).1.val=y.1+1 at e₁
  change (turn g (patchCenter p)).2.val=y.2+1 at e₂
  rw [e₁,e₂]
  simp [innerLabel,fine,ax _ by₁.1,ax _ by₁.2]
  apply congrArg clip; omega

theorem patch_rep (hk : 19≤k) (p : PatchPos k) :
    ∃ q : PatchPos (if k%2=1 then 19 else 20), ∀ g, patchFine p g=patchFine q g := by
  let b := if k%2=1 then 19 else 20
  obtain ⟨y,ty⟩ := type_rep hk (patchCenter p)
  have fv (g : Fin 8) : fine (N k) 8 (turn g (patchCenter p)).1.val (turn g (patchCenter p)).2.val=
      fine (N b) 8 (turn g y).1.val (turn g y).2.val := congrFun (congrArg (fun t => t.2.1) ty) g
  have zero {t} (x : Site t) : turn 0 x=x := by
    have h := turn_values 0 x
    apply Prod.ext <;> apply Fin.ext <;> simp [transform,Prod.ext_iff] at h <;> tauto
  have h := fv 0; rw [zero,zero] at h
  simp only [fine,List.cons.injEq] at h
  have inner (z : Nat) (hz : z<N k-2) (w : Fin (N b)) (eq : axis (N k) 8 (z+1)=axis (N b) 8 w.val) :
      0<w.val ∧ w.val<N b-1 := by
    have hb : 19≤b := by unfold b; split <;> omega
    have := w.isLt; unfold axis N at *; split_ifs at eq <;> omega
  have r := inner _ p.1.isLt _ h.1; have c := inner _ p.2.isLt _ h.2.1
  let q : PatchPos b := (⟨y.1.val-1,by omega⟩,⟨y.2.val-1,by omega⟩)
  have eq : patchCenter q=y := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [q,patchCenter] <;> omega
  exact ⟨q,fun g => by rw [patch_type,patch_type,eq,fv]⟩

theorem legal_patch {k} (F : Finset (Site k)) (hk : 19≤k) (acy : (Budget.G F).IsAcyclic)
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

end GridGraphs.NoPitch.TailRows
