import GridGraphs.BundleCycleDefect
import GridGraphs.RootedForestCuts

/-!
# Cutting repeated teeth from a forced bundle

For every noncentral forced component met by the new star, retain one
attachment.  Every other attachment is separated from its retained root by
de-forcing the first forced vertex on the unique forest path to that root.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*}

/-- A bounded deletion that makes the star at `u` insertable, together with
one physical tooth edge for every unit of bundle cycle defect. -/
structure BundleToothCertificate [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) where
  deletion : Finset V
  deletion_subset : (↑deletion : Set V) ⊆ F
  deletion_disjoint_owner : Disjoint (↑deletion : Set V) (G.neighborSet u)
  deletion_card_le : deletion.card ≤ bundleCycleDefect G F u
  insertion : ForcedInsertionCondition G (F \ (↑deletion : Set V)) u
  terminals : Finset V
  terminals_card : terminals.card = bundleCycleDefect G F u
  endpoint : V → V
  terminal_adj_owner : ∀ x ∈ terminals, G.Adj u x
  terminal_outside_forced : ∀ x ∈ terminals, x ∉ F
  terminal_adj_endpoint : ∀ x ∈ terminals, G.Adj x (endpoint x)
  endpoint_mem_deletion : ∀ x ∈ terminals, endpoint x ∈ deletion
  deletion_covered_by_endpoints :
    ∀ d ∈ deletion, ∃ x ∈ terminals, endpoint x = d
  endpoint_mem_forced : ∀ x ∈ terminals, endpoint x ∈ F

section Representatives

variable [Fintype V]

private noncomputable def attachmentRepresentative
    (G : SimpleGraph V) (F : Set V) (u : V)
    (c : (forcedEdgeGraph G F).ConnectedComponent) : V := by
  classical
  by_cases h : ∃ v ∈ starAttachmentLeaves G F u,
      forcedComponentLabel G F v = c
  · exact h.choose
  · exact u

private theorem attachmentRepresentative_spec
    (G : SimpleGraph V) (F : Set V) (u : V)
    {c : (forcedEdgeGraph G F).ConnectedComponent}
    (hc : c ∈ starAttachmentComponents G F u) :
    attachmentRepresentative G F u c ∈ starAttachmentLeaves G F u ∧
      forcedComponentLabel G F (attachmentRepresentative G F u c) = c := by
  classical
  unfold starAttachmentComponents at hc
  obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp hc
  unfold attachmentRepresentative
  split_ifs with h
  · exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  · exact (h ⟨v, hv, hvc⟩).elim

private noncomputable def retainedAttachments
    (G : SimpleGraph V) (F : Set V) (u : V) : Finset V := by
  classical
  exact (noncentralStarAttachmentComponents G F u).image
    (attachmentRepresentative G F u)

private theorem mem_retainedAttachments_iff
    (G : SimpleGraph V) (F : Set V) (u v : V) :
    v ∈ retainedAttachments G F u ↔
      v ∈ starAttachmentLeaves G F u ∧
      forcedComponentLabel G F v ≠ forcedComponentLabel G F u ∧
      v = attachmentRepresentative G F u (forcedComponentLabel G F v) := by
  classical
  constructor
  · intro hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    have hcI := Finset.mem_of_mem_erase hc
    have hs := attachmentRepresentative_spec G F u hcI
    refine ⟨hs.1, ?_, ?_⟩
    · rw [hs.2]
      exact Finset.ne_of_mem_erase hc
    · rw [hs.2]
  · rintro ⟨hvS, hvcenter, hvrep⟩
    apply Finset.mem_image.mpr
    refine ⟨forcedComponentLabel G F v, ?_, hvrep.symm⟩
    apply Finset.mem_erase.mpr
    refine ⟨hvcenter, ?_⟩
    unfold starAttachmentComponents
    exact Finset.mem_image.mpr ⟨v, hvS, rfl⟩

private theorem retainedAttachments_subset
    (G : SimpleGraph V) (F : Set V) (u : V) :
    retainedAttachments G F u ⊆ starAttachmentLeaves G F u := by
  intro v hv
  exact (mem_retainedAttachments_iff G F u v).mp hv |>.1

private theorem retainedAttachments_card
    (G : SimpleGraph V) (F : Set V) (u : V) :
    (retainedAttachments G F u).card = starAttachmentGraphicRank G F u := by
  classical
  unfold retainedAttachments starAttachmentGraphicRank
  rw [Finset.card_image_iff.mpr]
  intro c hc d hd hrep
  have hcI := Finset.mem_of_mem_erase hc
  have hdI := Finset.mem_of_mem_erase hd
  have hcs := (attachmentRepresentative_spec G F u hcI).2
  have hds := (attachmentRepresentative_spec G F u hdI).2
  rw [← hcs, hrep, hds]

private noncomputable def cutAttachments
    (G : SimpleGraph V) (F : Set V) (u : V) : Finset V := by
  classical
  exact starAttachmentLeaves G F u \ retainedAttachments G F u

private theorem cutAttachments_card
    (G : SimpleGraph V) (F : Set V) (u : V) :
    (cutAttachments G F u).card = bundleCycleDefect G F u := by
  classical
  unfold cutAttachments bundleCycleDefect
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr (retainedAttachments_subset G F u),
    retainedAttachments_card]

private noncomputable def attachmentRoot
    (G : SimpleGraph V) (F : Set V) (u x : V) : V := by
  classical
  exact if forcedComponentLabel G F x = forcedComponentLabel G F u then u
    else attachmentRepresentative G F u (forcedComponentLabel G F x)

private theorem attachmentRoot_label {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ starAttachmentLeaves G F u) :
    forcedComponentLabel G F (attachmentRoot G F u x) =
      forcedComponentLabel G F x := by
  classical
  unfold attachmentRoot
  split_ifs with h
  · exact h.symm
  · apply (attachmentRepresentative_spec G F u ?_).2
    unfold starAttachmentComponents
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

private theorem attachmentRoot_eq_or_mem_retained
    {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ starAttachmentLeaves G F u) :
    attachmentRoot G F u x = u ∨
      attachmentRoot G F u x ∈ retainedAttachments G F u := by
  classical
  unfold attachmentRoot
  split_ifs with h
  · exact Or.inl rfl
  · apply Or.inr
    apply (mem_retainedAttachments_iff G F u _).mpr
    have hs := attachmentRepresentative_spec G F u (by
      unfold starAttachmentComponents
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    exact ⟨hs.1, by simpa [hs.2] using h, by simp [hs.2]⟩

private theorem cutAttachment_ne_root
    {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ cutAttachments G F u) : x ≠ attachmentRoot G F u x := by
  classical
  have hxS : x ∈ starAttachmentLeaves G F u := Finset.mem_sdiff.mp hx |>.1
  have hxR : x ∉ retainedAttachments G F u := Finset.mem_sdiff.mp hx |>.2
  intro heq
  rcases attachmentRoot_eq_or_mem_retained hxS with hr | hr
  · have hxu : x = u := heq.trans hr
    exact (mem_starAttachmentLeaves G F u x).mp hxS |>.1.ne hxu.symm
  · exact hxR (heq ▸ hr)

private noncomputable def cutPath
    (G : SimpleGraph V) (F : Set V) (u x : V)
    (hx : x ∈ cutAttachments G F u) :
    (forcedEdgeGraph G F).Walk x (attachmentRoot G F u x) := by
  classical
  have hxS : x ∈ starAttachmentLeaves G F u := Finset.mem_sdiff.mp hx |>.1
  exact (Classical.choice (SimpleGraph.ConnectedComponent.exact
    (attachmentRoot_label hxS).symm)).toPath.val

private theorem cutPath_isPath {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ cutAttachments G F u) :
    (cutPath G F u x hx).IsPath := by
  classical
  unfold cutPath
  exact (Classical.choice (SimpleGraph.ConnectedComponent.exact
    (attachmentRoot_label (Finset.mem_sdiff.mp hx |>.1)).symm)).toPath.property

private theorem cutPath_not_nil {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ cutAttachments G F u) : ¬(cutPath G F u x hx).Nil :=
  Walk.not_nil_of_ne (cutAttachment_ne_root hx)

private noncomputable def cutEndpoint
    (G : SimpleGraph V) (F : Set V) (u x : V) : V := by
  classical
  by_cases hx : x ∈ cutAttachments G F u
  · exact (cutPath G F u x hx).snd
  · exact x

private theorem cutEndpoint_eq_snd {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ cutAttachments G F u) :
    cutEndpoint G F u x = (cutPath G F u x hx).snd := by
  classical
  unfold cutEndpoint
  simp only [hx, ↓reduceDIte]

private theorem cutEndpoint_mem_forced {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : x ∈ cutAttachments G F u) : cutEndpoint G F u x ∈ F := by
  classical
  have hxS := Finset.mem_sdiff.mp hx |>.1
  have hxnotF := (mem_starAttachmentLeaves G F u x).mp hxS |>.2
  have hadj := (cutPath G F u x hx).adj_snd (cutPath_not_nil hx)
  rw [cutEndpoint_eq_snd hx]
  rcases hadj.2 with hxF | hdF
  · exact (hxnotF hxF).elim
  · exact hdF

private theorem cutEndpoint_not_neighbor {G : SimpleGraph V} {F : Set V} {u x : V}
    (htriangle : G.CliqueFree 3) (hx : x ∈ cutAttachments G F u) :
    cutEndpoint G F u x ∉ G.neighborSet u := by
  classical
  intro hud
  have hxS := Finset.mem_sdiff.mp hx |>.1
  have hux := (mem_starAttachmentLeaves G F u x).mp hxS |>.1
  have hxd : G.Adj x (cutEndpoint G F u x) :=
    cutEndpoint_eq_snd hx ▸ (forcedEdgeGraph_le G F)
      ((cutPath G F u x hx).adj_snd (cutPath_not_nil hx))
  exact htriangle {u, x, cutEndpoint G F u x}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨hux, hud, hxd⟩)

private noncomputable def bundleToothDeletion
    (G : SimpleGraph V) (F : Set V) (u : V) : Finset V := by
  classical
  exact (cutAttachments G F u).image (cutEndpoint G F u)

private def IsBundleAttachment
    (G : SimpleGraph V) (F : Set V) (u x : V) : Prop :=
  x = u ∨ x ∈ starAttachmentLeaves G F u

private theorem attachmentRoot_eq_self_of_not_cut
    {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : IsBundleAttachment G F u x)
    (hcut : x ∉ cutAttachments G F u) : attachmentRoot G F u x = x := by
  classical
  rcases hx with rfl | hxS
  · simp [attachmentRoot]
  · have hxR : x ∈ retainedAttachments G F u := by
      by_contra hxnotR
      exact hcut (Finset.mem_sdiff.mpr ⟨hxS, hxnotR⟩)
    have hr := (mem_retainedAttachments_iff G F u x).mp hxR
    unfold attachmentRoot
    rw [if_neg hr.2.1]
    exact hr.2.2.symm

private def nilToEqualVertex {G : SimpleGraph V} {x r : V} (h : r = x) :
    G.Walk x r :=
  (Walk.nil : G.Walk x x).copy rfl h.symm

omit [Fintype V] in
private theorem nilToEqualVertex_isPath {G : SimpleGraph V} {x r : V}
    (h : r = x) : (nilToEqualVertex (G := G) h).IsPath := by
  simp [nilToEqualVertex]

omit [Fintype V] in
private theorem nilToEqualVertex_nil {G : SimpleGraph V} {x r : V}
    (h : r = x) : (nilToEqualVertex (G := G) h).Nil := by
  subst r
  exact Walk.nil_nil

private noncomputable def bundleAttachmentPath
    (G : SimpleGraph V) (F : Set V) (u x : V)
    (hx : IsBundleAttachment G F u x) :
    (forcedEdgeGraph G F).Walk x (attachmentRoot G F u x) := by
  classical
  by_cases hcut : x ∈ cutAttachments G F u
  · exact cutPath G F u x hcut
  · exact nilToEqualVertex (attachmentRoot_eq_self_of_not_cut hx hcut)

private theorem bundleAttachmentPath_isPath
    {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : IsBundleAttachment G F u x) :
    (bundleAttachmentPath G F u x hx).IsPath := by
  classical
  unfold bundleAttachmentPath
  split_ifs with hcut
  · exact cutPath_isPath hcut
  · exact nilToEqualVertex_isPath _

private theorem bundleAttachmentPath_first_not_adj
    {G : SimpleGraph V} {F : Set V} {u x : V}
    (hx : IsBundleAttachment G F u x) :
    ¬(bundleAttachmentPath G F u x hx).Nil →
      ¬(forcedEdgeGraph G (F \ (↑(bundleToothDeletion G F u) : Set V))).Adj
        x (bundleAttachmentPath G F u x hx).snd := by
  classical
  intro hnil
  unfold bundleAttachmentPath at hnil ⊢
  split_ifs with hcut
  · apply not_forcedEdgeGraph_diff_adj_of_not_mem_of_mem G
    · rcases hx with rfl | hxS
      · exact fun huF => (mem_starAttachmentLeaves G F x x).mp
          (Finset.mem_sdiff.mp hcut).1 |>.2 huF
      · exact (mem_starAttachmentLeaves G F u x).mp hxS |>.2
    · exact Finset.mem_image.mpr
        ⟨x, hcut, cutEndpoint_eq_snd hcut⟩
  · exfalso
    apply hnil
    simpa only [dif_neg hcut] using
      (nilToEqualVertex_nil (G := forcedEdgeGraph G F)
        (attachmentRoot_eq_self_of_not_cut hx hcut))

private theorem attachmentRoot_eq_of_label_eq
    {G : SimpleGraph V} {F : Set V} {u x y : V}
    (hxy : forcedComponentLabel G F x = forcedComponentLabel G F y) :
    attachmentRoot G F u x = attachmentRoot G F u y := by
  classical
  unfold attachmentRoot
  rw [hxy]

private theorem not_reachable_after_bundleToothDeletion
    {G : SimpleGraph V} {F : Set V} {u x y : V}
    (hF : (forcedEdgeGraph G F).IsAcyclic)
    (hx : IsBundleAttachment G F u x)
    (hy : IsBundleAttachment G F u y) (hxy : x ≠ y) :
    ¬(forcedEdgeGraph G (F \ (↑(bundleToothDeletion G F u) : Set V))).Reachable
      x y := by
  classical
  let H := forcedEdgeGraph G F
  let K := forcedEdgeGraph G (F \ (↑(bundleToothDeletion G F u) : Set V))
  have hKH : K ≤ H := forcedEdgeGraph_diff_le G F _
  by_cases hlabel : forcedComponentLabel G F x = forcedComponentLabel G F y
  · let px := bundleAttachmentPath G F u x hx
    let py0 := bundleAttachmentPath G F u y hy
    have hroot := attachmentRoot_eq_of_label_eq (u := u) hlabel
    let py : H.Walk y (attachmentRoot G F u x) := py0.copy rfl hroot.symm
    apply hF.not_reachable_of_firstEdge_not_adj hKH px
      (bundleAttachmentPath_isPath hx) py
    · simpa [py, py0] using bundleAttachmentPath_isPath hy
    · exact hxy
    · exact bundleAttachmentPath_first_not_adj hx
    · simpa [py, py0] using bundleAttachmentPath_first_not_adj hy
  · intro hreach
    apply hlabel
    apply SimpleGraph.ConnectedComponent.sound
    exact hreach.mono hKH

private theorem bundleToothDeletion_subset
    (G : SimpleGraph V) (F : Set V) (u : V) :
    (↑(bundleToothDeletion G F u) : Set V) ⊆ F := by
  classical
  intro d hd
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
  exact cutEndpoint_mem_forced hx

private theorem bundleToothDeletion_disjoint_neighborSet
    (G : SimpleGraph V) (F : Set V) (u : V) (htriangle : G.CliqueFree 3) :
    Disjoint (↑(bundleToothDeletion G F u) : Set V) (G.neighborSet u) := by
  classical
  rw [Set.disjoint_left]
  intro d hdD hdN
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hdD
  exact cutEndpoint_not_neighbor htriangle hx hdN

private theorem bundleToothDeletion_card_le_defect
    (G : SimpleGraph V) (F : Set V) (u : V) :
    (bundleToothDeletion G F u).card ≤ bundleCycleDefect G F u := by
  classical
  exact (Finset.card_image_le.trans_eq (cutAttachments_card G F u))

private theorem isBundleAttachment_of_postDeletion
    {G : SimpleGraph V} {F : Set V} {u x : V}
    (hdisj : Disjoint (↑(bundleToothDeletion G F u) : Set V) (G.neighborSet u))
    (hx : x ∈ ({u} ∪
      (G.neighborSet u \ (F \ (↑(bundleToothDeletion G F u) : Set V))) : Set V)) :
    IsBundleAttachment G F u x := by
  classical
  rcases hx with hx | hx
  · exact Or.inl hx
  · apply Or.inr
    apply (mem_starAttachmentLeaves G F u x).mpr
    refine ⟨hx.1, ?_⟩
    intro hxF
    have hxnotD : x ∉ (↑(bundleToothDeletion G F u) : Set V) := by
      intro hxD
      exact Set.disjoint_left.mp hdisj hxD hx.1
    exact hx.2 ⟨hxF, hxnotD⟩

/-- Triangle-freeness and acyclicity supply a bounded tooth deletion, with one
owner-labelled physical tooth edge witnessing every defect unit. -/
theorem exists_bundleToothCertificate
    (G : SimpleGraph V)
    (htriangle : G.CliqueFree 3)
    (F : Set V) (u : V)
    (hF : (forcedEdgeGraph G F).IsAcyclic) :
    Nonempty (BundleToothCertificate G F u) := by
  classical
  let D := bundleToothDeletion G F u
  have hsub := bundleToothDeletion_subset G F u
  have hdisj := bundleToothDeletion_disjoint_neighborSet G F u htriangle
  refine ⟨{
    deletion := D
    deletion_subset := hsub
    deletion_disjoint_owner := hdisj
    deletion_card_le := bundleToothDeletion_card_le_defect G F u
    insertion := ?_
    terminals := cutAttachments G F u
    terminals_card := cutAttachments_card G F u
    endpoint := cutEndpoint G F u
    terminal_adj_owner := ?_
    terminal_outside_forced := ?_
    terminal_adj_endpoint := ?_
    endpoint_mem_deletion := ?_
    deletion_covered_by_endpoints := ?_
    endpoint_mem_forced := ?_
  }⟩
  · intro x hx y hy hxy
    apply not_reachable_after_bundleToothDeletion hF
    · exact isBundleAttachment_of_postDeletion hdisj hx
    · exact isBundleAttachment_of_postDeletion hdisj hy
    · exact hxy
  · intro x hx
    exact (mem_starAttachmentLeaves G F u x).mp (Finset.mem_sdiff.mp hx).1 |>.1
  · intro x hx
    exact (mem_starAttachmentLeaves G F u x).mp (Finset.mem_sdiff.mp hx).1 |>.2
  · intro x hx
    exact cutEndpoint_eq_snd hx ▸ (forcedEdgeGraph_le G F)
      ((cutPath G F u x hx).adj_snd (cutPath_not_nil hx))
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro d hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx, hxd⟩
  · intro x hx
    exact cutEndpoint_mem_forced hx

/-- In a triangle-free graph, de-forcing at most one forced endpoint per bundle
defect unit makes the complete star bundle insertable. -/
theorem exists_deletion_for_forcedInsertionCondition
    (G : SimpleGraph V)
    (htriangle : G.CliqueFree 3)
    (F : Set V) (u : V)
    (hF : (forcedEdgeGraph G F).IsAcyclic) :
    ∃ D : Finset V,
      (↑D : Set V) ⊆ F ∧
      Disjoint (↑D : Set V) (G.neighborSet u) ∧
      D.card ≤ bundleCycleDefect G F u ∧
      ForcedInsertionCondition G (F \ (↑D : Set V)) u := by
  let c := (exists_bundleToothCertificate G htriangle F u hF).some
  exact ⟨c.deletion, c.deletion_subset, c.deletion_disjoint_owner,
    c.deletion_card_le, c.insertion⟩

/-- A genuine new owner can be inserted acyclically after the bounded tooth
deletion supplied by `exists_deletion_for_forcedInsertionCondition`. -/
theorem exists_deletion_for_forcedEdgeGraph_insert_isAcyclic
    (G : SimpleGraph V)
    (htriangle : G.CliqueFree 3)
    (F : Set V) (u : V)
    (hu : u ∉ F)
    (hF : (forcedEdgeGraph G F).IsAcyclic) :
    ∃ D : Finset V,
      (↑D : Set V) ⊆ F ∧
      Disjoint (↑D : Set V) (G.neighborSet u) ∧
      D.card ≤ bundleCycleDefect G F u ∧
      (forcedEdgeGraph G (insert u (F \ (↑D : Set V)))).IsAcyclic := by
  classical
  obtain ⟨D, hDF, hDN, hcard, hins⟩ :=
    exists_deletion_for_forcedInsertionCondition G htriangle F u hF
  refine ⟨D, hDF, hDN, hcard, ?_⟩
  have hu' : u ∉ F \ (↑D : Set V) := fun huF => hu huF.1
  have hdiff := forcedEdgeGraph_diff_isAcyclic G hF (↑D : Set V)
  exact (forcedEdgeGraph_insert_isAcyclic_iff hu' hdiff).mpr hins

end Representatives

end GridGraphs
