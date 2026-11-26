import GridGraphs.ResidueZero.PhysicalPatch
import GridGraphs.Results.ExactSquareFormula

/-! Four disjoint legal patches suffice at side six. -/
namespace GridGraphs.ResidueZero
open Finset

private theorem tile_count : ∀ m : Fin 512, maskOK m → (tileMarks m).card ≤ 4 := by
  native_decide

private def block (i : Fin 4) (v : Tile) : GridVertex 6 6 :=
  place (3*(i.val/2)) (3*(i.val%2)) (by have := i.isLt; omega) (by omega) v

private theorem covered : ∀ v : GridVertex 6 6, ∃ i u, block i u=v := by native_decide

theorem physical_patch_card {n : Nat} (F : Finset (GridVertex n n))
    (acy : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) :
    (univ.filter fun v : Tile => place r c hr hc v ∈ F).card ≤ 4 := by
  have h := tile_count _ (physical_mask_ok F acy r c hr hc)
  rwa [physicalMask_tiles] at h

theorem maxPreserved_six : maxPreserved 6 6 = squareScore 6 := by
  apply le_antisymm _ (squareScore_lower_three_mul 2 (by decide))
  by_contra! h
  obtain ⟨F,hF,card⟩ := (squareMaskScore_iff_le (s:=17) (by decide : 0<6)).mpr h
  let S (i : Fin 4) := univ.filter fun u : Tile => block i u ∈ F
  have bound (i) : (S i).card ≤ 4 :=
    physical_patch_card F (mem_acyclicForcedSets.mp hF) _ _ _ _
  have sub : F ⊆ univ.biUnion (fun i => (S i).image (block i)) := by
    intro v hv
    obtain ⟨i,u,rfl⟩ := covered v
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩⟩
  have chain := (card_le_card sub).trans (card_biUnion_le)
  have total := sum_le_sum (s:=(univ : Finset (Fin 4))) (fun i _ =>
    (show ((S i).image (block i)).card ≤ (S i).card from card_image_le).trans (bound i))
  have : F.card ≤ 16 := chain.trans (by simpa using total)
  omega

end GridGraphs.ResidueZero
