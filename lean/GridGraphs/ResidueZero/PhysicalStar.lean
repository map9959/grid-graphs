import GridGraphs.ResidueZero.Stencil
import GridGraphs.Geometry.CapRootArrows
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry

namespace GridGraphs.ResidueZero
open SimpleGraph Finset

def coord {n : Nat} (v : GridVertex n n) : Pos := (v.1.val,v.2.val)

theorem coord_injective {n : Nat} : Function.Injective (coord (n:=n)) := by
  intro a b h
  simpa [coord,Prod.ext_iff,Fin.ext_iff] using h

theorem coord_inside {n : Nat} (v : GridVertex n n) : inside n (coord v) := by
  simp [coord,inside]

def marked {n : Nat} (F : Finset (GridVertex n n)) (p : Pos) : Bool :=
  decide (p ∈ F.image coord)

def code (s : Fin 4 → Bool) := (List.ofFn fun d => (s d).toNat <<< d.val).sum
private theorem code_bits : ∀ s, ∀ d : Fin 4, bit (code s) d = (s d).toNat := by native_decide
theorem code_lt : ∀ s, code s < 16 := by native_decide

def neighbours {n : Nat} (F : Finset (GridVertex n n)) (p : Pos) :=
  code fun d => marked F (shift p d)

theorem neighbours_bit {n : Nat} (F : Finset (GridVertex n n)) (p : Pos) (d : Fin 4) :
    bit (neighbours F p) d = (marked F (shift p d)).toNat := code_bits _ _

theorem marked_at {n : Nat} (F : Finset (GridVertex n n)) (v : GridVertex n n) :
    marked F (coord v) = decide (v∈F) := by
  simp [marked,Finset.mem_image,coord_injective.eq_iff]

theorem marked_inside {n : Nat} {F : Finset (GridVertex n n)} {p : Pos} (h : marked F p) :
    inside n p := by
  obtain ⟨v,_,rfl⟩ := mem_image.mp (show p∈F.image coord by simpa [marked] using h)
  exact coord_inside v

private theorem cornerBits {n : Nat} (F : Finset (GridVertex n n))
    (acy : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (p : Pos) (d : Fin 4) (h : marked F (shift p d)) :
    marked F (shift p ((d+1:Nat)%4)) = false := by
  apply Bool.eq_false_iff.mpr
  intro other
  obtain ⟨a,ha,eq₁⟩ := mem_image.mp (show _∈F.image coord by simpa [marked] using h)
  obtain ⟨b,hb,eq₂⟩ := mem_image.mp (show _∈F.image coord by simpa [marked] using other)
  apply CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy a b ha hb <;>
    fin_cases d <;> simp [coord,shift,Prod.ext_iff] at eq₁ eq₂ <;> omega

abbrev Bonds {n : Nat} (F : Finset (GridVertex n n)) :=
  forcedEdgeGraph (gridGraph n n) (↑F : Set _)

/-- Root each component, preferring the distinguished corner. Every forced
edge is oriented exactly once; the designated corner has no outgoing edge. -/
theorem parent_exists {n : Nat} (F : Finset (GridVertex n n)) (root : GridVertex n n)
    (acy : (Bonds F).IsAcyclic) : ∃ parent : GridVertex n n → GridVertex n n,
    parent root=root ∧ (∀ v, parent v≠v → (Bonds F).Adj v (parent v)) ∧
    ∀ v w, (Bonds F).Adj v w → (parent v=w ↔ parent w≠v) := by
  classical
  let R (c : (Bonds F).ConnectedComponent) :=
    if (Bonds F).connectedComponentMk root=c then root else c.out
  have sec c : (Bonds F).connectedComponentMk (R c)=c := by
    dsimp [R]; split <;> first | assumption | exact Quot.out_eq _
  let P := CapBill.parent R sec
  have step {v} (h : P v≠v) := CapBill.parent_step R sec (mt (CapBill.parent_fix R sec v).mpr h)
  refine ⟨P,(CapBill.parent_fix R sec root).mpr (by simp [CapBill.dest,R]),
    fun _ h => (step h).1,?_⟩
  intro v w e
  constructor
  · intro a b
    have x := (step (v:=v) (by simpa [a] using e.ne.symm)).2
    have y := (step (v:=w) (by simpa [b] using e.ne)).2
    change CapBill.depth R (P v)<_ at x
    change CapBill.depth R (P w)<_ at y
    rw [a] at x; rw [b] at y; omega
  · intro h
    exact (CapBill.parent_covers R sec acy e).resolve_right h

def outDir {n : Nat} (v w : GridVertex n n) : Nat :=
  if v=w then 4 else if v.2<w.2 then 0 else if v.1<w.1 then 1 else if w.2<v.2 then 2 else 3

theorem outDir_lt {n : Nat} (v w : GridVertex n n) : outDir v w < 5 := by
  unfold outDir; split_ifs <;> decide

theorem shift_out {n : Nat} {v w : GridVertex n n} (h : (gridGraph n n).Adj v w) :
    shift (coord v) (outDir v w) = coord w := by
  change adjacent _ _ _ _ at h
  simp [adjacent,Fin.ext_iff] at h
  unfold outDir
  split_ifs <;> simp_all only [coord,shift,Prod.ext_iff,Fin.ext_iff,Fin.lt_def] <;> omega

theorem starOK_physical {n : Nat} (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (v w : GridVertex n n) (step : v≠w → (Bonds F).Adj v w) :
    starOK n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v w) := by
  unfold starOK
  simp only [Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true]
  constructor
  · intro d hd
    let i : Fin 4 := ⟨d,hd⟩
    let j : Fin 4 := ⟨(d+1)%4,by omega⟩
    rw [neighbours_bit F _ i,neighbours_bit F _ j]
    cases m : marked F (shift (coord v) d) with
    | false => simp
    | true =>
      have z := cornerBits F acy (coord v) i m
      dsimp [i] at z
      simp [j,marked_inside m,z]
  · by_cases eq : v=w
    · simp [outDir,eq]
    · right
      have e := step eq
      have d : outDir v w < 4 := by unfold outDir; split_ifs <;> simp_all
      rw [neighbours_bit F _ ⟨_,d⟩,shift_out e.1,marked_at]
      simp only [coord_inside,Bool.true_and,decide_eq_true_eq]
      rcases e.2 with h|h
      · simp [show v∈F from h]
      · simp [show w∈F from h]

end GridGraphs.ResidueZero
