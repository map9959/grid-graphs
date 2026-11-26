import GridGraphs.ResidueZero.Stencil
import GridGraphs.Accounting.ForcedForestLedger

/-! A patch mask excluded by the stencil forces a physical rectangle cycle.
There are nine possible rectangles inside a 3×3 patch. -/
namespace GridGraphs.ResidueZero
open SimpleGraph

abbrev Tile := GridVertex 3 3

def tileMarks (m : Nat) : Finset Tile :=
  Finset.univ.filter fun v => bit m (3*v.1.val+v.2.val)=1
abbrev tileGraph (m : Nat) := forcedEdgeGraph (gridGraph 3 3) (↑(tileMarks m) : Set Tile)

def rectangles : Fin 9 → List Nat := ![
  [0,1,4,3], [1,2,5,4], [3,4,7,6], [4,5,8,7],
  [0,1,2,5,4,3], [3,4,5,8,7,6], [0,1,4,7,6,3], [1,2,5,8,7,4],
  [0,1,2,5,8,7,6,3]]

def rectSite (r : Fin 9) (i : Fin (rectangles r).length) : Tile :=
  let q := (rectangles r)[i.val]
  (Fin.ofNat 3 (q/3), Fin.ofNat 3 (q%3))

private theorem rectangle_check :
    ∀ m : Fin 512, maskOK m = false → ∃ r : Fin 9,
      (∀ i j, rectSite r i=rectSite r j → i=j) ∧
      (∀ i j, (cycleGraph (rectangles r).length).Adj i j →
        (tileGraph m).Adj (rectSite r i) (rectSite r j)) := by native_decide

private theorem rect_hasCycle (r : Fin 9) : ¬ (cycleGraph (rectangles r).length).IsAcyclic := by
  have bad (n : Nat) [NeZero n] (cn : (cycleGraph n).Connected)
      (edges : (cycleGraph n).edgeFinset.card = n) : ¬(cycleGraph n).IsAcyclic := by
    intro acy
    have h := (show (cycleGraph n).IsTree from ⟨cn,acy⟩).card_edgeFinset
    simp [edges] at h
  fin_cases r <;> apply bad _ cycleGraph_connected <;> native_decide

theorem maskOK_of_acyclic {m : Fin 512} (acy : (tileGraph m).IsAcyclic) : maskOK m := by
  by_contra h
  obtain ⟨r,inj,adj⟩ := rectangle_check m (Bool.eq_false_iff.mpr h)
  exact rect_hasCycle r (acy.comap ⟨rectSite r,adj _ _⟩ inj)

def place {n : Nat} (r c : Nat) (hr : r+3≤n) (hc : c+3≤n) (v : Tile) : GridVertex n n :=
  (⟨r+v.1,by have := v.1.isLt; omega⟩,⟨c+v.2,by have := v.2.isLt; omega⟩)

def physicalMask {n : Nat} (F : Finset (GridVertex n n)) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) : Fin 512 :=
  Fin.ofNat 512 ((List.range 9).foldl (fun m q =>
    if place r c hr hc (Fin.ofNat 3 (q/3),Fin.ofNat 3 (q%3)) ∈ F then m+2^q else m) 0)

private def encode (s : Finset Tile) : Fin 512 :=
  Fin.ofNat 512 ((List.range 9).foldl (fun m q =>
    if (Fin.ofNat 3 (q/3),Fin.ofNat 3 (q%3)) ∈ s then m+2^q else m) 0)

private theorem decode : ∀ s : Finset Tile, tileMarks (encode s) = s := by native_decide

theorem physicalMask_tiles {n : Nat} (F : Finset (GridVertex n n)) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) :
    tileMarks (physicalMask F r c hr hc) =
      Finset.univ.filter (fun v : Tile => place r c hr hc v ∈ F) := by
  rw [← decode (Finset.univ.filter _)]
  simp [physicalMask,encode]

theorem physical_mask_ok {n : Nat} (F : Finset (GridVertex n n))
    (acy : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) : maskOK (physicalMask F r c hr hc) := by
  let P := place r c hr hc
  let S := Finset.univ.filter fun v : Tile => P v ∈ F
  have eq : physicalMask F r c hr hc = encode S := by simp [physicalMask,encode,S,P]
  rw [eq]
  apply maskOK_of_acyclic
  unfold tileGraph
  rw [decode]
  let hom : forcedEdgeGraph (gridGraph 3 3) (↑S : Set _) →g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) := {
    toFun := P
    map_rel' := by
      rintro a b ⟨hadj,hf⟩
      constructor
      · change adjacent 3 3 a b at hadj
        change adjacent n n (place ..) (place ..)
        simpa [adjacent,place,Fin.ext_iff,Nat.add_assoc] using hadj
      · simpa [S] using hf }
  apply acy.comap hom
  intro a b h
  change place r c hr hc a = place r c hr hc b at h
  simpa [place,Prod.ext_iff,Fin.ext_iff] using h

end GridGraphs.ResidueZero
