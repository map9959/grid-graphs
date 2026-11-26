import GridGraphs.Geometry.CapColoredBill
import GridGraphs.Geometry.CapRootArrows
import GridGraphs.Geometry.Diagonal
import GridGraphs.Core.Spanning

namespace GridGraphs.CapBill
open SimpleGraph Finset

private abbrev HAdj {m n} (x y : GridVertex m n) :=
  x.1=y.1 ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val)
private abbrev VAdj {m n} (x y : GridVertex m n) :=
  x.2=y.2 ∧ (x.1.val+1=y.1.val ∨ y.1.val+1=x.1.val)

/-- Two marked neighbors in perpendicular directions close a physical
four-cycle, so every vertex has at most two marked neighbors. -/
theorem marked_neighbors_le_two {m n} (F : Finset (GridVertex m n))
    (forest : (forcedEdgeGraph (gridGraph m n) (↑F : Set _)).IsAcyclic)
    (v : GridVertex m n) : hits (gridGraph m n) F v ≤ 2 := by
  have no {x y} (hx : x∈F) (hy : y∈F) (a : HAdj x v) (b : VAdj y v) : False := by
    let w : GridVertex m n := (y.1,x.2)
    have vx : (gridGraph m n).Adj x v := Or.inl a
    have vy : (gridGraph m n).Adj y v := Or.inr b
    have yw : (gridGraph m n).Adj y w := Or.inl ⟨rfl,by rw [b.1]; exact a.2.symm⟩
    have xw : (gridGraph m n).Adj x w := Or.inr ⟨rfl,by rw [a.1]; exact b.2.symm⟩
    have neq : x.2 ≠ v.2 := by intro eq; have := a.2; simp [eq] at this
    have h := fourCycle_has_unforced_edge vx vy.symm yw xw.symm
      (fun eq => neq ((congrArg Prod.snd eq).trans b.1))
      (fun eq => neq ((congrArg Prod.snd eq).symm)) forest
    tauto
  let S := F.filter (fun w => (gridGraph m n).Adj w v)
  have mem {x} (hx : x∈S) : x∈F ∧ (HAdj x v ∨ VAdj x v) := mem_filter.mp hx
  have axis : (∀ x∈S, HAdj x v) ∨ (∀ x∈S, VAdj x v) := by
    by_cases a : ∃ x∈S, HAdj x v
    · obtain ⟨x,hx,ax⟩ := a
      exact Or.inl fun y hy => (mem hy).2.resolve_right (no (mem hx).1 (mem hy).1 ax)
    · exact Or.inr fun x hx => (mem hx).2.resolve_left (fun hh => a ⟨x,hx,hh⟩)
  suffices h : S.card ≤ (univ : Finset Bool).card by
    change (S.card : ℤ) ≤ 2
    simpa using (Int.ofNat_le.mpr h)
  rcases axis with hor|vert
  · apply card_le_card_of_injOn (fun x => decide (x.2.val<v.2.val)) (fun _ _ => mem_univ _)
    intro x hx y hy eq
    have a := hor x hx; have b := hor y hy
    exact Prod.ext (a.1.trans b.1.symm) (Fin.ext (by have := a.2; have := b.2; simp at eq; omega))
  · apply card_le_card_of_injOn (fun x => decide (x.1.val<v.1.val)) (fun _ _ => mem_univ _)
    intro x hx y hy eq
    have a := vert x hx; have b := vert y hy
    exact Prod.ext (Fin.ext (by have := a.2; have := b.2; simp at eq; omega)) (a.1.trans b.1.symm)

abbrev Cell (r h : Nat) := GridVertex (h+2) (3*r)
abbrev board (r h : Nat) := gridGraph (h+2) (3*r)
def outer (r h : Nat) : Finset (Cell r h) :=
  univ ×ˢ (univ.filter fun x : Fin (3*r) => x.val%3≠1)

private theorem outer_card (r h : Nat) : (outer r h).card = 2*r*(h+2) := by
  have cols : (univ.filter fun x : Fin (3*r) => x.val%3≠1).card = 2*r := by
    rw [card_filter,Fin.sum_univ_eq_sum_range (fun i => if i%3≠1 then 1 else 0)]
    induction r with
    | zero => simp
    | succ r ih =>
      rw [show 3*(r+1)=3*r+1+1+1 by omega,sum_range_succ,sum_range_succ,sum_range_succ,ih]
      split_ifs <;> omega
  simp [outer,cols,Nat.mul_comm]

/-- Padding conventions as properties of the marks, not identities about
the price. Top marks have their central residue; the last row is blank. -/
structure Padded {r h : Nat} (F : Finset (Cell r h)) : Prop where
  sides : ∀ v∈F, 0<v.2.val ∧ v.2.val+1<3*r
  bottom : ∀ v∈F, v.1.val+1<h+2
  top : ∀ v∈F, v.1.val=0 → v.2.val%3=1
  teeth : (F.filter fun v => v.1.val=0).card=r
  forest : (forcedEdgeGraph (board r h) (↑F : Set _)).IsAcyclic

private theorem colored_neighbors {r h} {F : Finset (Cell r h)} (pad : Padded F)
    (v : Cell r h) (hv : v ∈ F) :
    hits (board r h) (outer r h) v = if v ∈ outer r h then 3 else 2 := by
  obtain ⟨lo,hi⟩ := pad.sides v hv
  let l : Cell r h := (v.1,⟨v.2.val-1,by omega⟩)
  let rgt : Cell r h := (v.1,⟨v.2.val+1,hi⟩)
  have subset (x : Cell r h) : x ∈ ((outer r h).filter fun w => (board r h).Adj w v) ↔
      x.2.val%3≠1 ∧ (HAdj x v ∨ VAdj x v) := by simp [outer,board,gridGraph,adjacent]
  unfold hits
  by_cases center : v.2.val%3=1
  · have eq : ((outer r h).filter fun w => (board r h).Adj w v) = {l,rgt} := by
      ext x
      rw [subset]; simp only [mem_insert,mem_singleton,Prod.ext_iff,Fin.ext_iff,HAdj,VAdj,l,rgt]
      omega
    rw [eq]
    have ne : l ≠ rgt := by
      intro eq; have := congrArg (fun w : Cell r h => w.2.val) eq
      dsimp [l,rgt] at this; omega
    simp [outer,center,ne]
  · have y0 : 0<v.1.val := by by_contra! z; exact center (pad.top v hv (by omega))
    let u : Cell r h := (⟨v.1.val-1,by omega⟩,v.2)
    let d : Cell r h := (⟨v.1.val+1,pad.bottom v hv⟩,v.2)
    let side := if v.2.val%3=0 then l else rgt
    have eq : ((outer r h).filter fun w => (board r h).Adj w v) = {u,d,side} := by
      ext x
      rw [subset]; simp only [mem_insert,mem_singleton,Prod.ext_iff,Fin.ext_iff,HAdj,VAdj]
      dsimp [u,d,side,l,rgt]
      split_ifs <;> simp <;> omega
    have ne₁ : u≠d := by
      intro eq; have := congrArg (fun w : Cell r h => w.1.val) eq
      dsimp [u,d] at this; omega
    have srow : side.1=v.1 := by dsimp [side]; split_ifs <;> rfl
    have ne₂ : u≠side := by
      intro eq; have e := congrArg Prod.fst eq; rw [srow] at e
      have := congrArg Fin.val e; dsimp [u] at this; omega
    have ne₃ : d≠side := by
      intro eq; have e := congrArg Prod.fst eq; rw [srow] at e
      have := congrArg Fin.val e; dsimp [d] at this; omega
    rw [eq]; simp [outer,center,ne₁,ne₂,ne₃]

theorem physical_bill {r h : Nat} (hr : 0<r) {F : Finset (Cell r h)} (pad : Padded F)
    (j : Nat) :
    let bonus := (F.card : Int)-r*((h:ℤ)+1)
    let extras := (Fintype.card (forcedEdgeGraph (board r h) (↑F : Set _)).ConnectedComponent : Int) -
      (∑ v, iso (board r h) F v) - ((r:ℤ)-j)
    let bill := (∑ v, siteBill (board r h) F (outer r h) v)-2*r+2*extras
    4*bonus=2*r+2*j-bill := by
  apply colored_bill _ _ _ _ _ _ pad.forest (by simp [GridVertex,Nat.mul_comm]) (outer_card r h)
    (fun v _ _ => marked_neighbors_le_two F pad.forest v) (colored_neighbors pad)
  have deg (v) (hv : v∈F) : ((board r h).degree v : Int) =
      4-(if v.1.val=0 then 1 else 0) := by
    have := pad.sides v hv; have := pad.bottom v hv
    by_cases top : v.1.val=0
    · rw [if_pos top,gridGraph_degree_border (by omega) (by omega) _ (Or.inl ⟨Or.inl top,by omega⟩)]
      decide
    · rw [if_neg top,gridGraph_degree_interior (by omega) (by omega) _ (by omega) (by omega)]
      decide
  rw [sum_congr rfl deg,sum_sub_distrib,sum_boole, pad.teeth]; simp [mul_comm]

def terminalSet {r h} (F : Finset (Cell r h)) := F.filter fun v => v.1.val=0

/-- The signed bill is the sum of site charges plus two units per actual
nonterminal marked sink. The rank is the number of actual waived teeth. -/
theorem oriented_bill {r h : Nat} (hr : 0<r) {F : Finset (Cell r h)} (pad : Padded F) :
    let G := board r h
    let T := terminalSet F
    let bonus := (F.card : Int)-r*((h:ℤ)+1)
    let j := (waived G T F).card
    let bill := (∑ v, siteBill G F (outer r h) v)-2*r+2*((extraRoots G T F).card : Int)
    4*bonus=2*r+2*j-bill := by
  dsimp only
  have ex := extras_count (board r h) (terminalSet F) F (filter_subset _ _)
  rw [show (terminalSet F).card=r from pad.teeth] at ex
  simpa only [ex] using physical_bill hr pad (waived (board r h) (terminalSet F) F).card

end GridGraphs.CapBill
