import GridGraphs.ResidueTwoUpper.TwoGapExitProjection
import GridGraphs.ResidueTwoUpper.TwoGapRootForest

/-! The automaton attaches its synthetic root at depth **two**. The
physical anchors in `unique_anchor` are the adjacent depth-one sites.
Sliding pins along those pendant edges preserves the forest. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil BoundarySix.Connected Catalogue Words

abbrev Size (u : Nat) := 35+42*u
abbrev Board (u : Nat) := GridVertex (Size u) (Size u)
def high (u : Nat) := 34+42*u
def point (u r c : Nat) (hr : r<Size u) (hc : c<Size u) : Board u := (⟨r,hr⟩,⟨c,hc⟩)

private theorem root_near {u d} {F : Finset (Board u)} {P} (C : North.Chart F P d)
    (c : Fin (Size u)) (hc : 3≤c.val ∧ c.val+3≤high u) (south : Bool)
    (north : south=false → c.val≠d) :
    let edgeRow := if south then high u else 0
    let row1 := if south then high u-1 else 1
    let row2 := if south then high u-2 else 2
    let v (r : Nat) (h : r<Size u) : Board u := (⟨r,h⟩,c)
    let a := v row1 (by cases south <;> simp [row1,high,Size] <;> omega)
    let b := v edgeRow (by cases south <;> simp [edgeRow,high,Size] <;> omega)
    let z := v row2 (by cases south <;> simp [row2,high,Size] <;> omega)
    b∈F → z∈F → P a=b ∧ P z=a := by
  dsimp only
  intro mb mz
  let h := high u
  let x (r : Nat) (hr : r<Size u) : Board u := (⟨r,hr⟩,c)
  let b := x (if south then h else 0) (by cases south <;> dsimp [h,high,Size] <;> omega)
  let a := x (if south then h-1 else 1) (by cases south <;> dsimp [h,high,Size] <;> omega)
  let z := x (if south then h-2 else 2) (by cases south <;> dsimp [h,high,Size] <;> omega)
  change P a=b ∧ P z=a
  have bd : IsGridBoundary b := by cases south <;> simp [IsGridBoundary,b,x,h,Size,high] <;> omega
  have par := C.perimeter b bd
  have ba : P b≠a := by
    intro eq; rw [eq] at par
    cases south <;> simp [North.rc,North.parent,b,a,x,h,high] at par north hc <;>
      split_ifs at par <;> simp_all [high,Prod.mk.injEq] <;> omega
  have ab : (Bonds F).Adj a b := by
    refine ⟨Or.inr ⟨rfl,?_⟩,Or.inr mb⟩
    cases south <;> simp [a,b,x,h,high] <;> omega
  have za : (Bonds F).Adj z a := by
    refine ⟨Or.inr ⟨rfl,?_⟩,Or.inl mz⟩
    cases south <;> simp [a,z,x,h,high] <;> omega
  have A := (C.arrows _ _ ab).mpr ba
  refine ⟨A,(C.arrows _ _ za).mpr ?_⟩
  rw [A]; intro eq
  have e := congrArg (fun v : Board u => v.1.val) eq
  cases south <;> simp [b,z,x,h,high] at e <;> omega

def pinSet {u} (F : Finset (Board u)) (d : Nat) := F.filter fun v =>
  3≤v.2.val ∧ v.2.val+3≤high u ∧
    ((v.1.val=2 ∧ v.2.val≠d) ∨ v.1.val=high u-2)

private def anchorOf {u} (z : Board u) : Board u :=
  (⟨if z.1.val=2 then 1 else high u-1,by unfold high Size; split_ifs <;> omega⟩,z.2)

private theorem pin_embeds {u d} (F : Finset (Board u)) {P}
    (C : North.Chart F P d) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    {z} (hz : z∈pinSet F d) :
    anchor IsGridBoundary P (anchorOf z) ∧
    (crop (Bonds F) IsGridBoundary).Adj z (anchorOf z) := by
  obtain ⟨mz,cl,cr,side⟩ := mem_filter.mp hz
  change (z.1.val=2 ∧ z.2.val≠d) ∨ z.1.val=34+42*u-2 at side
  change z.2.val+3≤34+42*u at cr
  let s := decide (z.1.val≠2)
  let b : Board u := (⟨if s then high u else 0,by dsimp [s,high,Size]; split_ifs <;> omega⟩,z.2)
  have bd : IsGridBoundary b := by unfold IsGridBoundary; dsimp [b,high,Size]; split_ifs <;> omega
  have mb : b∈F := (North.marked_iff F acy score canon _ bd).mpr (by
    unfold North.hole North.rc; dsimp [b,high]; split_ifs <;> omega)
  have zrow : (if s then high u-2 else 2)=z.1.val := by
    by_cases h : z.1.val=2 <;> simp [s,h,high] <;> omega
  have loc : (⟨if s then high u-2 else 2,by rw [zrow]; exact z.1.isLt⟩,z.2)=z :=
    Prod.ext (Fin.ext zrow) rfl
  have near := root_near C z.2 ⟨cl,cr⟩ s (by dsimp [s,high] at *; simp; omega)
  dsimp only at near
  have A := (near mb (by rw [loc]; exact mz)).1
  have same : (if s then high u-1 else 1)=(if z.1.val=2 then 1 else high u-1) := by
    by_cases e : z.1.val=2 <;> simp [e,s]
  have e : P (anchorOf z)=b := by convert A using 2 <;> simp [anchorOf,b,same]
  have nz : ¬IsGridBoundary z := by
    change ¬(z.1.val=0 ∨ z.1.val+1=35+42*u ∨ z.2.val=0 ∨ z.2.val+1=35+42*u); omega
  have na : ¬IsGridBoundary (anchorOf z) := by
    rw [North.rim_iff]
    have ne : z.2≠0 := by intro eq; rw [eq] at cl; change 3≤0 at cl; omega
    by_cases h : z.1.val=2 <;> simp [North.rim,North.rc,anchorOf,h,Size,high,ne] <;> omega
  refine ⟨⟨na,e ▸ bd⟩,⟨⟨Or.inr ⟨rfl,?_⟩,Or.inl mz⟩,nz,na⟩⟩
  dsimp [anchorOf,high]; split_ifs <;> dsimp [high] at * <;> omega

theorem physical_frontier_forest {u d} (F : Finset (Board u)) {P} (C : North.Chart F P d)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    (s : Finset (Board u)) (sub : s⊆pinSet F d) :
    (pinned (crop (Bonds F) IsGridBoundary) (nw u) s).IsAcyclic := by
  apply pinned_forest (acy.anti (show crop (Bonds F) IsGridBoundary ≤ Bonds F from fun _ _ e => e.1))
  · intro z hz r
    have pair := pin_embeds F C acy score canon (sub hz)
    have bd : IsGridBoundary (nw u) := Or.inl rfl
    have R := pair.2.reachable.symm.trans r
    have iso {a b : Board u} (x : IsGridBoundary a) (y : ¬IsGridBoundary b)
        (w : (crop (Bonds F) IsGridBoundary).Walk a b) : False := by
      cases w with
      | nil => exact y x
      | cons e _ => exact e.2.1 x
    exact iso bd pair.1.1 R.symm.some
  · intro z hz y hy r
    have A := pin_embeds F C acy score canon (sub hz)
    have B := pin_embeds F C acy score canon (sub hy)
    have eq := unique_anchor C.arrows A.1 B.1 (A.2.reachable.symm.trans (r.trans B.2.reachable))
    obtain ⟨_,_,_,Z⟩ := mem_filter.mp (sub hz)
    obtain ⟨_,_,_,Y⟩ := mem_filter.mp (sub hy)
    apply Prod.ext
    · apply Fin.ext
      have e := congrArg (fun v : Board u => v.1.val) eq
      dsimp [anchorOf,high] at e Z Y; split_ifs at e <;> omega
    · have E := congrArg (fun w : Board u => w.2) eq
      exact E

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
