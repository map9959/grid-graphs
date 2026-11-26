import GridGraphs.ResidueTwoUpper.TwoGapFrontierPins

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil BoundarySix.Connected Catalogue Words

/-- Closed cropped rectangle up through the last processed row. -/
def prefixBox {u} (l t : Nat) (v : Board u) :=
  1≤v.1.val ∧ v.1.val≤t ∧ l≤v.2.val ∧ v.2.val≤l+8

def prefixGraph {u} (F : Finset (Board u)) (l t : Nat) : SimpleGraph (Board u) :=
  crop (crop (Bonds F) IsGridBoundary) (fun x => ¬prefixBox l t x)

def exposed {u} (l t : Nat) (v : Board u) :=
  v.1.val=t ∨ v.2.val=l ∨ v.2.val=l+8

private theorem extend_box {u} {F : Finset (Board u)} {a b : Board u} {l t}
    (e : (crop (Bonds F) IsGridBoundary).Adj a b) (inside : prefixBox l t a)
    (closed : ¬exposed l t a) : prefixBox l t b := by
  have h := e.1.1
  change adjacent _ _ _ _ at h
  have inner := e.2.2
  unfold IsGridBoundary at inner; unfold prefixBox exposed at *
  simp only [adjacent,Fin.ext_iff] at h
  omega

private theorem guard_anchor {u d} (F : Finset (Board u)) {P} (C : North.Chart F P d)
    {l t : Nat} (lo : 3≤l) (hi : l+8+3≤high u)
    {a : Board u} (inA : prefixBox l t a) (anch : anchor IsGridBoundary P a) :
    (a.1.val=1 ∧ a.2.val≠d) ∨ a.1.val=high u-1 := by
  have ne : P a≠a := fun h => anch.1 (h ▸ anch.2)
  have adj := (C.step a ne).1
  change adjacent _ _ _ _ at adj
  have bd := anch.2; have na := anch.1
  unfold IsGridBoundary at na bd
  unfold prefixBox at inA
  simp only [adjacent,Fin.ext_iff] at adj
  have A := a.1.isLt; have R := (P a).1.isLt
  change a.1.val<35+42*u at A
  change (P a).1.val<35+42*u at R
  change _=0 ∨ _+1=35+42*u ∨ _=0 ∨ _+1=35+42*u at bd
  change ¬(_=0 ∨ _+1=35+42*u ∨ _=0 ∨ _+1=35+42*u) at na
  dsimp [high] at hi ⊢
  by_cases top : a.1.val=1
  · left; refine ⟨top,?_⟩
    intro col
    have rc : North.rc (P a)=(0,d) := by apply Prod.ext <;> dsimp [North.rc] <;> omega
    have par := C.perimeter (P a) anch.2
    rw [rc] at par
    have ord := C.ordinary.1
    have back : P (P a)=a := North.rc_inj (par.trans (by
      simp [North.parent,North.rc,top,col,show d≠0 by omega,show d≠1 by omega]))
    exact (C.arrows a (P a) (C.step a ne)).mp rfl back
  · right; omega

private theorem blank_depth_one {u} (F : Finset (Board u))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    {v : Board u} (cl : 2≤v.2.val) (cr : v.2.val+2≤high u)
    (row : v.1.val=1 ∨ v.1.val=high u-1) : v∉F := by
  have marks := chart_marks F acy score canon v 0 false
  apply of_decide_eq_false; apply marks
  have h := v.1.isLt; have k := v.2.isLt
  dsimp [high] at cr row
  unfold rimDatum; dsimp only
  have hk : 3*(11+14*(u:Int))+1=34+42*u := by ring
  rw [hk]
  unfold clip
  rcases row with r|r <;> rw [r] <;> push_cast <;> (repeat' split_ifs) <;>
    first | rfl | omega

/-- No marked component in a cropped prefix can vanish without either
a left/right leak, a live vertex in the last row, or one of the *actual*
depth-two pins. This is the geometric content of the retirement test. -/
theorem physical_frontier_escape {u d} (F : Finset (Board u)) {P} (C : North.Chart F P d)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    (l t : Nat) (lo : 3≤l) (hi : l+8+3≤high u)
    {x : Board u} (mx : x∈F) (ix : prefixBox l t x) (nx : ¬IsGridBoundary x) :
    ∃ y, (prefixGraph F l t).Reachable x y ∧ (exposed l t y ∨ y∈pinSet F d) := by
  classical
  by_contra! bad
  have fix : P (nw u)=nw u := North.rc_inj (C.perimeter _ (Or.inl rfl))
  obtain ⟨a,ha,r⟩ := reaches_anchor C.arrows fix (show IsGridBoundary (nw u) from Or.inl rfl)
    (all_marks_reachable u F acy score x mx) nx
  let R := (prefixGraph F l t).Reachable x
  have follow {b c} (w : (crop (Bonds F) IsGridBoundary).Walk b c) :
      R b ∧ prefixBox l t b → R c ∧ prefixBox l t c := by
    induction w with
    | nil => exact id
    | @cons v z e h tail ih =>
      rintro ⟨rv,iv⟩
      have iz := extend_box h iv (fun ex => (bad v rv).1 ex)
      exact ih ⟨rv.trans (show (prefixGraph F l t).Adj v z from ⟨h,not_not_intro iv,not_not_intro iz⟩).reachable,iz⟩
  have ⟨ra,ia⟩ := follow r.symm.some ⟨.rfl,ix⟩
  have row := guard_anchor F C lo hi ia ha
  have blank : a∉F := blank_depth_one F acy score canon (by unfold prefixBox at ia; omega)
    (by unfold prefixBox at ia; omega) (row.imp And.left id)
  have ne : a≠x := fun e => blank (e ▸ mx)
  have first {b c : Board u} (w : (crop (Bonds F) IsGridBoundary).Walk b c) (ne : b≠c) :
      ∃ z, (crop (Bonds F) IsGridBoundary).Adj b z := by
    cases w with | nil => contradiction | cons h _ => exact ⟨_,h⟩
  obtain ⟨z,edge⟩ := first r.some ne
  have mz : z∈F := edge.1.2.resolve_left blank
  have ⟨rz,iz⟩ := follow (.cons edge .nil) ⟨ra,ia⟩
  apply (bad z rz).2
  have adj := edge.1.1; change adjacent _ _ _ _ at adj
  simp only [adjacent,Fin.ext_iff] at adj
  have nz := edge.2.2
  change ¬(_=0 ∨ _+1=35+42*u ∨ _=0 ∨ _+1=35+42*u) at nz
  have mrow : ¬(z.1.val=1 ∨ z.1.val=high u-1) := fun h =>
    blank_depth_one F acy score canon (by unfold prefixBox at iz; omega)
      (by unfold prefixBox at iz; omega) h mz
  apply mem_filter.mpr
  unfold prefixBox at ia iz; dsimp [high] at row mrow hi ⊢
  have Z := z.1.isLt; change z.1.val<35+42*u at Z
  exact ⟨mz,by omega,by omega,by omega⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
