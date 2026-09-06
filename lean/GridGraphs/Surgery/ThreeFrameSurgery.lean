import GridGraphs.Surgery.GridCrop
import GridGraphs.Surgery.ForcedExchange

/-!
# Repairing a three-frame crop

This file isolates the finite bookkeeping needed after cropping a forced forest.
It deliberately makes no assertion that a repair of a prescribed size exists.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {A B V : Type*}

/-- The forced vertices surviving a crop along an embedding. -/
def cropForcedSet [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) : Finset A :=
  Finset.univ.filter fun v => e v ∈ F

@[simp] theorem mem_cropForcedSet [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (v : A) :
    v ∈ cropForcedSet e F ↔ e v ∈ F := by
  simp [cropForcedSet]

@[simp] theorem coe_cropForcedSet [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) :
    (↑(cropForcedSet e F) : Set A) = e ⁻¹' (↑F : Set B) := by
  ext v
  simp

/-- Removing images of local vertices before cropping is exactly local
deletion after cropping. -/
@[simp] theorem cropForcedSet_sdiff_image
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (D : Finset A) :
    cropForcedSet e (F \ D.image e) = cropForcedSet e F \ D := by
  ext v
  simp

/-- The number of forced vertices removed by a crop. -/
def cropFrameLoss [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) : Nat :=
  F.card - (cropForcedSet e F).card

/-- A repair set contains no forced vertex already present in the crop. -/
def IsCropRepairSet [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (R : Finset A) : Prop :=
  Disjoint (cropForcedSet e F) R

/-- A repair is admissible when forcing it together with the crop is acyclic. -/
def CropRepairAdmissible [Fintype A] [DecidableEq A] [DecidableEq B]
    (G : SimpleGraph A) (e : A ↪ B) (F : Finset B) (R : Finset A) : Prop :=
  (forcedEdgeGraph G
    (↑(cropForcedSet e F ∪ R) : Set A)).IsAcyclic

/-- Frame loss after crediting the vertices inserted by a repair. -/
def netFrameLoss [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (R : Finset A) : Nat :=
  cropFrameLoss e F - R.card

/-- Frame loss after both deleting surviving forced vertices and inserting
repair vertices. -/
def deleteAddNetFrameLoss [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (D R : Finset A) : Nat :=
  cropFrameLoss e F + D.card - R.card

theorem cropForcedSet_card_le [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) :
    (cropForcedSet e F).card ≤ F.card := by
  calc
    (cropForcedSet e F).card = (Finset.image e (cropForcedSet e F)).card := by
      symm
      exact Finset.card_image_of_injective _ e.injective
    _ ≤ F.card := by
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact (mem_cropForcedSet e F u).mp hu

/-- Cardinality splits into the surviving crop and the deleted frame. -/
theorem card_eq_crop_add_frameLoss [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) :
    F.card = (cropForcedSet e F).card + cropFrameLoss e F := by
  have hle := cropForcedSet_card_le e F
  unfold cropFrameLoss
  omega

/-- Exact cardinal bookkeeping for a disjoint repair. -/
theorem card_eq_repaired_add_netFrameLoss
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (R : Finset A)
    (hR : IsCropRepairSet e F R)
    (hsize : R.card ≤ cropFrameLoss e F) :
    F.card = (cropForcedSet e F ∪ R).card + netFrameLoss e F R := by
  rw [Finset.card_union_of_disjoint hR]
  unfold netFrameLoss
  rw [card_eq_crop_add_frameLoss e F]
  omega

/-- Exact cardinal bookkeeping for a crop surgery that first de-forces `D`
and then inserts the disjoint repair set `R`. -/
theorem card_eq_deleteAdd_add_deleteAddNetFrameLoss
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (F : Finset B) (D R : Finset A)
    (hD : D ⊆ cropForcedSet e F)
    (hR : Disjoint (cropForcedSet e F \ D) R)
    (hsize : R.card ≤ cropFrameLoss e F + D.card) :
    F.card = ((cropForcedSet e F \ D) ∪ R).card +
      deleteAddNetFrameLoss e F D R := by
  rw [Finset.card_union_of_disjoint hR]
  have hcrop := card_eq_crop_add_frameLoss e F
  have hdelete := Finset.card_sdiff_add_card_eq_card hD
  unfold deleteAddNetFrameLoss
  omega

/-- An admissible delete/add crop surgery bounds the original cardinality by
the smaller-grid maximum plus its net loss. -/
theorem card_le_maxForcedAcyclic_add_deleteAddNetFrameLoss
    [DecidableEq B] {p q : Nat} (e : GridVertex p q ↪ B) (F : Finset B)
    (D R : Finset (GridVertex p q))
    (hD : D ⊆ cropForcedSet e F)
    (hR : Disjoint (cropForcedSet e F \ D) R)
    (hadm : (forcedEdgeGraph (gridGraph p q)
      (↑((cropForcedSet e F \ D) ∪ R) : Set (GridVertex p q))).IsAcyclic)
    (hsize : R.card ≤ cropFrameLoss e F + D.card) :
    F.card ≤ maxForcedAcyclic p q + deleteAddNetFrameLoss e F D R := by
  rw [card_eq_deleteAdd_add_deleteAddNetFrameLoss e F D R hD hR hsize]
  apply Nat.add_le_add_right
  apply Finset.le_sup (f := Finset.card)
  exact mem_acyclicForcedSets.mpr hadm

/-- An admissible repair bounds the original cardinality by the smaller-grid
maximum plus its net frame loss. -/
theorem card_le_maxForcedAcyclic_add_netFrameLoss
    [DecidableEq B] {p q : Nat} (e : GridVertex p q ↪ B) (F : Finset B)
    (R : Finset (GridVertex p q))
    (hR : IsCropRepairSet e F R)
    (hadm : CropRepairAdmissible (gridGraph p q) e F R)
    (hsize : R.card ≤ cropFrameLoss e F) :
    F.card ≤ maxForcedAcyclic p q + netFrameLoss e F R := by
  rw [card_eq_repaired_add_netFrameLoss e F R hR hsize]
  apply Nat.add_le_add_right _
  apply Finset.le_sup (f := Finset.card)
  exact mem_acyclicForcedSets.mpr hadm

/-- Per-instance upper-recurrence consequence of a repaired total-three crop.
No global repair-existence hypothesis is bundled into this statement. -/
theorem maxForcedAcyclic_le_of_threeSideCrop_repair
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Finset (GridVertex n n)) (R : Finset (GridVertex (n - 3) (n - 3)))
    (hmax : F.card = maxForcedAcyclic n n)
    (hR : IsCropRepairSet
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F R)
    (hadm : CropRepairAdmissible (gridGraph (n - 3) (n - 3))
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F R)
    (hsize : R.card ≤ cropFrameLoss
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F)
    {d : Nat} (hloss : netFrameLoss
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F R ≤ d) :
    maxForcedAcyclic n n ≤ maxForcedAcyclic (n - 3) (n - 3) + d := by
  rw [← hmax]
  exact (card_le_maxForcedAcyclic_add_netFrameLoss
    (threeSideCropEmbedding n top bottom left right hn hrows hcols)
    F R hR hadm hsize).trans (Nat.add_le_add_left hloss _)

/-- Per-instance upper-recurrence consequence of a total-three crop with both
deletions and insertions. -/
theorem maxForcedAcyclic_le_of_threeSideCrop_deleteAdd
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Finset (GridVertex n n))
    (D R : Finset (GridVertex (n - 3) (n - 3)))
    (hmax : F.card = maxForcedAcyclic n n)
    (hD : D ⊆ cropForcedSet
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F)
    (hR : Disjoint
      (cropForcedSet
        (threeSideCropEmbedding n top bottom left right hn hrows hcols) F \ D) R)
    (hadm : (forcedEdgeGraph (gridGraph (n - 3) (n - 3))
      (↑((cropForcedSet
          (threeSideCropEmbedding n top bottom left right hn hrows hcols) F \ D) ∪ R) :
        Set (GridVertex (n - 3) (n - 3)))).IsAcyclic)
    (hsize : R.card ≤ cropFrameLoss
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F + D.card)
    {d : Nat} (hloss : deleteAddNetFrameLoss
      (threeSideCropEmbedding n top bottom left right hn hrows hcols) F D R ≤ d) :
    maxForcedAcyclic n n ≤ maxForcedAcyclic (n - 3) (n - 3) + d := by
  rw [← hmax]
  exact (card_le_maxForcedAcyclic_add_deleteAddNetFrameLoss
    (threeSideCropEmbedding n top bottom left right hn hrows hcols)
    F D R hD hR hadm hsize).trans (Nat.add_le_add_left hloss _)

/-- The finite crop used by surgery inherits forced-edge acyclicity from the
large grid. -/
theorem threeSideCrop_forcedSet_isAcyclic
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Finset (GridVertex n n))
    (hF : (forcedEdgeGraph (gridGraph n n)
      (↑F : Set (GridVertex n n))).IsAcyclic) :
    (forcedEdgeGraph (gridGraph (n - 3) (n - 3))
      (↑(cropForcedSet
        (threeSideCropEmbedding n top bottom left right hn hrows hcols) F) :
          Set (GridVertex (n - 3) (n - 3)))).IsAcyclic := by
  rw [coe_cropForcedSet]
  exact forcedEdgeGraph_threeSideCrop_isAcyclic
    n top bottom left right hn hrows hcols (↑F : Set (GridVertex n n)) hF

/-- The attachment condition appearing when one forced vertex is inserted. -/
def ForcedInsertionCondition [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Prop :=
  ∀ ⦃v⦄, v ∈ ({u} ∪ (G.neighborSet u \ F) : Set V) →
    ∀ ⦃w⦄, w ∈ ({u} ∪ (G.neighborSet u \ F) : Set V) →
      v ≠ w → ¬(forcedEdgeGraph G F).Reachable v w

/-- Successive one-vertex attachment conditions along an ordering. -/
def SequentiallyInsertable [Fintype V]
    (G : SimpleGraph V) : Set V → List V → Prop
  | _, [] => True
  | F, u :: us =>
      ForcedInsertionCondition G F u ∧ SequentiallyInsertable G (insert u F) us

/-- A no-duplicate ordering disjoint from an acyclic initial forced set is
admissible exactly when all one-vertex attachment tests pass in sequence. -/
theorem forcedEdgeGraph_union_list_isAcyclic_iff_sequentiallyInsertable
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Set V) (l : List V) (hl : l.Nodup)
    (hdisj : ∀ u ∈ l, u ∉ F)
    (hF : (forcedEdgeGraph G F).IsAcyclic) :
    (forcedEdgeGraph G (F ∪ (↑l.toFinset : Set V))).IsAcyclic ↔
      SequentiallyInsertable G F l := by
  classical
  induction l generalizing F with
  | nil => simp [SequentiallyInsertable, hF]
  | cons u us ih =>
      have huF : u ∉ F := hdisj u (by simp)
      have huus : u ∉ us := List.nodup_cons.mp hl |>.1
      have hus : us.Nodup := List.nodup_cons.mp hl |>.2
      have hdisj' : ∀ v ∈ us, v ∉ insert u F := by
        intro v hv hmem
        rcases hmem with rfl | hvF
        · exact huus hv
        · exact hdisj v (by simp [hv]) hvF
      have hInsert : (forcedEdgeGraph G (insert u F)).IsAcyclic ↔
          ForcedInsertionCondition G F u := by
        exact forcedEdgeGraph_insert_isAcyclic_iff huF hF
      have hsets : F ∪ (↑(u :: us).toFinset : Set V) =
          insert u F ∪ (↑us.toFinset : Set V) := by
        ext v
        simp [or_left_comm, or_comm]
      rw [hsets]
      constructor
      · intro hall
        have hins : (forcedEdgeGraph G (insert u F)).IsAcyclic := by
          apply hall.anti
          intro v w hvw
          refine ⟨hvw.1, ?_⟩
          rcases hvw.2 with hv | hw
          · exact Or.inl (Or.inl hv)
          · exact Or.inr (Or.inl hw)
        exact ⟨hInsert.mp hins,
          (ih (insert u F) hus hdisj' hins).mp hall⟩
      · rintro ⟨hcond, hseq⟩
        have hins := hInsert.mpr hcond
        exact (ih (insert u F) hus hdisj' hins).mpr hseq

/-- Sequential characterization for an ordering of a crop repair set. -/
theorem cropRepairAdmissible_iff_sequentiallyInsertable
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (G : SimpleGraph A) [DecidableRel G.Adj] (e : A ↪ B) (F : Finset B)
    (R : Finset A) (l : List A) (hl : l.Nodup) (hlR : l.toFinset = R)
    (hR : IsCropRepairSet e F R)
    (hcrop : (forcedEdgeGraph G
      (↑(cropForcedSet e F) : Set A)).IsAcyclic) :
    CropRepairAdmissible G e F R ↔
      SequentiallyInsertable G (↑(cropForcedSet e F) : Set A) l := by
  classical
  have hdisj : ∀ u ∈ l, u ∉ (↑(cropForcedSet e F) : Set A) := by
    intro u hu huCrop
    exact Finset.disjoint_left.mp hR huCrop (by simpa [← hlR] using hu)
  simpa [CropRepairAdmissible, hlR] using
    forcedEdgeGraph_union_list_isAcyclic_iff_sequentiallyInsertable
      G (↑(cropForcedSet e F) : Set A) l hl hdisj hcrop

end GridGraphs
