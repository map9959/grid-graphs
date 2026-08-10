import GridGraphs.ForestLedger

/-!
# Labelled component quotients

Finite families of extra edges are represented by three-edge paths with two
label-specific internal vertices.  This representation is deliberate: unlike
a `SimpleGraph` edge set, it retains parallel labels, and a labelled loop is a
triangle rather than being silently discarded.
-/

namespace SimpleGraph

open Finset

variable {V E : Type*}

/-- Vertices used to retain the identity of every extra edge. -/
abbrev LabelledExtensionVertex (V E : Type*) := V ⊕ (E × Bool)

/-- The three edges representing one physical labelled edge. -/
def labelledPath (ends : E → V × V) (e : E) :
    SimpleGraph (LabelledExtensionVertex V E) :=
  fromEdgeSet {s(Sum.inl (ends e).1, Sum.inr (e, false))} ⊔
    fromEdgeSet {s(Sum.inr (e, false), Sum.inr (e, true))} ⊔
      fromEdgeSet {s(Sum.inr (e, true), Sum.inl (ends e).2)}

/-- Add a finite set of labelled physical edges to `H`.

Each physical edge is subdivided twice.  Consequently labels are retained when
several edges have the same endpoints, and an edge whose endpoints coincide is
retained as a triangle. -/
def labelledExtension (H : SimpleGraph V) (ends : E → V × V) (S : Finset E) :
    SimpleGraph (LabelledExtensionVertex V E) :=
  H.map ⟨Sum.inl, Sum.inl_injective⟩ ⊔ S.sup (labelledPath ends)

/-- The component endpoints of a labelled physical edge. -/
def componentEnds (H : SimpleGraph V) (ends : E → V × V) (e : E) :
    H.ConnectedComponent × H.ConnectedComponent :=
  (H.connectedComponentMk (ends e).1, H.connectedComponentMk (ends e).2)

/-- The labelled component quotient.  It has one vertex for every component of
`H`, and retains each physical label by subdividing its quotient edge twice. -/
def labelledComponentQuotient (H : SimpleGraph V) (ends : E → V × V) (S : Finset E) :
    SimpleGraph (LabelledExtensionVertex H.ConnectedComponent E) :=
  labelledExtension ⊥ (componentEnds H ends) S

/-- The literal, order-independent edge-independence condition.

The first clause rejects physical loops.  The second says that, after erasing
the particular label `e`, its endpoint components are not joined by the other
labels.  In particular, two parallel labels are both visible and violate the
predicate. -/
def LabelledEdgeIndependent [DecidableEq E]
    (H : SimpleGraph V) (ends : E → V × V) (S : Finset E) : Prop :=
  ∀ e ∈ S,
    (componentEnds H ends e).1 ≠ (componentEnds H ends e).2 ∧
      ¬(labelledComponentQuotient H ends (S.erase e)).Reachable
        (Sum.inl (componentEnds H ends e).1) (Sum.inl (componentEnds H ends e).2)

/-- Order-independent forest predicate for a labelled component quotient.

Because labels are represented by disjoint internal vertices, this uses the
ordinary `SimpleGraph.IsAcyclic` API without identifying parallel labels or
discarding physical loops. -/
def LabelledQuotientForest
    (H : SimpleGraph V) (ends : E → V × V) (S : Finset E) : Prop :=
  (labelledComponentQuotient H ends S).IsAcyclic

@[simp] theorem labelledExtension_empty (H : SimpleGraph V) (ends : E → V × V) :
    labelledExtension H ends ∅ = H.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  simp [labelledExtension]

@[simp] theorem labelledComponentQuotient_empty (H : SimpleGraph V)
    (ends : E → V × V) : labelledComponentQuotient H ends ∅ = ⊥ := by
  ext x y
  simp [labelledComponentQuotient, SimpleGraph.map_adj]

theorem labelledExtension_mono {H K : SimpleGraph V} {S T : Finset E}
    (hHK : H ≤ K) (hST : S ⊆ T) :
    labelledExtension H ends S ≤ labelledExtension K ends T := by
  apply sup_le_sup
  · exact SimpleGraph.map_monotone _ hHK
  · exact Finset.sup_mono hST

theorem labelledComponentQuotient_mono {S T : Finset E} (hST : S ⊆ T) :
    labelledComponentQuotient H ends S ≤ labelledComponentQuotient H ends T :=
  labelledExtension_mono le_rfl hST

private def addEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∨
    (((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ x ≠ y)
  symm := by
    rintro x y (h | ⟨h, hxy⟩)
    · exact Or.inl (G.symm h)
    · exact Or.inr ⟨h.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩), hxy.symm⟩
  loopless x := by simp

private lemma addEdge_adj {G : SimpleGraph V} {u v x y : V} :
    (addEdge G u v).Adj x y ↔ G.Adj x y ∨
      (((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ x ≠ y) := Iff.rfl

private lemma delete_addEdge {G : SimpleGraph V} {u v : V}
    (huv : u ≠ v) (hnew : ¬G.Adj u v) :
    addEdge G u v \ fromEdgeSet {s(u, v)} = G := by
  ext x y
  simp only [sdiff_adj, addEdge_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hG | ⟨_, _⟩, hnot⟩
    · exact hG
    · exfalso
      apply hnot
      rcases ‹(x = u ∧ y = v) ∨ (x = v ∧ y = u)› with h | h
      · exact ⟨Or.inl h, h.1 ▸ h.2 ▸ huv⟩
      · exact ⟨Or.inr h, h.1 ▸ h.2 ▸ huv.symm⟩
  · intro hG
    refine ⟨Or.inl hG, ?_⟩
    rintro ⟨h | h, _⟩
    · exact hnew (h.1 ▸ h.2 ▸ hG)
    · exact hnew (G.symm (h.1 ▸ h.2 ▸ hG))

private theorem isAcyclic_addEdge_iff {G : SimpleGraph V} {u v : V}
    (hG : G.IsAcyclic) (huv : u ≠ v) (hnew : ¬G.Adj u v) :
    (addEdge G u v).IsAcyclic ↔ ¬G.Reachable u v := by
  let K := addEdge G u v
  have hdel : K \ fromEdgeSet {s(u, v)} = G := delete_addEdge huv hnew
  constructor
  · intro hK huvReach
    obtain ⟨x, c, hc, _⟩ :=
      (adj_and_reachable_delete_edges_iff_exists_cycle (G := K) (v := u) (w := v)).mp
        ⟨by exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩, by simpa [hdel]⟩
    exact hK c hc
  · intro hnreach x c hc
    by_cases he : s(u, v) ∈ c.edges
    · have hreach :=
        (adj_and_reachable_delete_edges_iff_exists_cycle (G := K) (v := u) (w := v)).mpr
          ⟨x, c, hc, he⟩ |>.2
      exact hnreach (by simpa [hdel] using hreach)
    · have hedges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e hec
        have heK := c.edges_subset_edgeSet hec
        induction e using Sym2.ind with
        | _ a b =>
          change K.Adj a b at heK
          rcases heK with heG | ⟨hab, _⟩
          · exact heG
          · apply (he ?_).elim
            rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hec
            · simpa [Sym2.eq_swap] using hec
      exact hG (c.transfer G hedges) (hc.transfer hedges)

private lemma reachable_eq_of_isolated {G : SimpleGraph V} {p x : V}
    (hp : ∀ y, ¬G.Adj p y) (h : G.Reachable x p) : x = p := by
  by_contra hxp
  have hmem : p ∈ G.support := mem_support_of_reachable (Ne.symm hxp) h.symm
  obtain ⟨y, hpy⟩ := (mem_support G).mp hmem
  exact hp y hpy

private lemma reachable_addEdge_isolated {G : SimpleGraph V} {a p x y : V}
    (hap : a ≠ p) (hp : ∀ z, ¬G.Adj p z) (hxp : x ≠ p) :
    (addEdge G a p).Reachable x y ↔
      G.Reachable x y ∨ (G.Reachable x a ∧ y = p) := by
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl (Reachable.refl _)
    | @tail z y h hadj ih =>
        rcases ih with hz | ⟨hxa, rfl⟩
        · rcases hadj with hadj | ⟨hadj, hzy⟩
          · exact Or.inl (hz.trans hadj.reachable)
          · rcases hadj with ⟨hza, hyp⟩ | ⟨hzp, hya⟩
            · subst z; subst y; exact Or.inr ⟨hz, rfl⟩
            · subst z
              exact (hxp (reachable_eq_of_isolated hp hz)).elim
        · rcases hadj with hadj | ⟨hadj, hpy⟩
          · exact (hp _ hadj).elim
          · rcases hadj with ⟨hpa, hy⟩ | ⟨_, hy⟩
            · exact (hap hpa.symm).elim
            · subst y; exact Or.inl hxa
  · rintro (h | ⟨h, hy⟩)
    · exact h.mono (show G ≤ addEdge G a p from fun _ _ hadj => Or.inl hadj)
    · subst y
      exact (h.mono (show G ≤ addEdge G a p from fun _ _ hadj => Or.inl hadj)).trans
        (show (addEdge G a p).Adj a p from Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hap⟩).reachable

private lemma labelledExtension_insert [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E} {e : E} (he : e ∉ S) :
    labelledExtension H ends (insert e S) =
      addEdge
        (addEdge
          (addEdge (labelledExtension H ends S)
            (Sum.inl (ends e).1) (Sum.inr (e, false)))
          (Sum.inr (e, false)) (Sum.inr (e, true)))
        (Sum.inr (e, true)) (Sum.inl (ends e).2) := by
  ext x y
  simp only [labelledExtension, sup_adj, sup_insert, labelledPath, addEdge_adj,
    fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  aesop

private lemma labelledExtension_isolated [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E} {e : E} (he : e ∉ S) (b : Bool) (x) :
    ¬(labelledExtension H ends S).Adj (Sum.inr (e, b)) x := by
  intro hadj
  rw [labelledExtension, sup_adj] at hadj
  rcases hadj with hadj | hadj
  · rcases hadj with ⟨u, v, _, hu, _⟩
    exact Sum.noConfusion hu.symm
  · have hs : ∀ (T : Finset E), e ∉ T →
        ¬(T.sup (labelledPath ends)).Adj (Sum.inr (e, b)) x := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | @insert f T hf ih =>
          intro heT h
          rw [sup_insert, sup_adj] at h
          rcases h with h | h
          · simp only [labelledPath, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
              Sym2.eq_iff] at h
            have hef : e ≠ f := by
              intro hef
              apply heT
              simp [hef]
            aesop
          · exact ih (fun he' => heT (mem_insert_of_mem he')) h
    exact hs S he hadj

private theorem labelledExtension_insert_isAcyclic_iff [DecidableEq E]
    {H : SimpleGraph V} {ends : E → V × V} {S : Finset E} {e : E}
    (he : e ∉ S) :
    (labelledExtension H ends (insert e S)).IsAcyclic ↔
      (labelledExtension H ends S).IsAcyclic ∧
        ¬(labelledExtension H ends S).Reachable
          (Sum.inl (ends e).1) (Sum.inl (ends e).2) := by
  classical
  let G := labelledExtension H ends S
  let a : LabelledExtensionVertex V E := Sum.inl (ends e).1
  let p : LabelledExtensionVertex V E := Sum.inr (e, false)
  let q : LabelledExtensionVertex V E := Sum.inr (e, true)
  let b : LabelledExtensionVertex V E := Sum.inl (ends e).2
  have hap : a ≠ p := by simp [a, p]
  have hp : ∀ x, ¬G.Adj p x := fun x => labelledExtension_isolated he false x
  have haq : a ≠ q := by simp [a, q]
  have hpq : p ≠ q := by simp [p, q]
  have hq : ∀ x, ¬G.Adj q x := fun x => labelledExtension_isolated he true x
  have hpa : ¬G.Adj a p := fun h => hp a (G.symm h)
  have hG1q : ∀ x, ¬(addEdge G a p).Adj q x := by
    intro x h
    rcases h with h | ⟨h, _⟩
    · exact hq x h
    · rcases h with ⟨hqa, _⟩ | ⟨hqp, _⟩
      · exact haq hqa.symm
      · exact hpq hqp.symm
  rw [labelledExtension_insert he]
  constructor
  · intro hAll
    have hG2 : (addEdge (addEdge G a p) p q).IsAcyclic :=
      hAll.anti (by intro x y h; exact Or.inl h)
    have hG1 : (addEdge G a p).IsAcyclic :=
      hG2.anti (by intro x y h; exact Or.inl h)
    have hG : G.IsAcyclic := hG1.anti (by intro x y h; exact Or.inl h)
    refine ⟨hG, ?_⟩
    have hnqb : ¬(addEdge (addEdge G a p) p q).Reachable q b :=
      (isAcyclic_addEdge_iff hG2 (by simp [q, b]) (by
        intro h
        rcases h with h | ⟨h, _⟩
        · exact hG1q b h
        · simp [p, q, b] at h)).mp hAll
    intro hab
    apply hnqb
    have hapReach : (addEdge G a p).Reachable p b := by
      have hpaReach : (addEdge G a p).Reachable p a :=
        (show (addEdge G a p).Adj p a from
          Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hap.symm⟩).reachable
      exact hpaReach.trans (hab.mono (by intro _ _ h; exact Or.inl h))
    exact (show (addEdge (addEdge G a p) p q).Adj q p from
      Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hpq.symm⟩).reachable.trans
        (hapReach.mono (by intro _ _ h; exact Or.inl h))
  · rintro ⟨hG, hnab⟩
    have hnGp : ¬G.Reachable a p := fun h => hap (reachable_eq_of_isolated hp h)
    have hG1 : (addEdge G a p).IsAcyclic :=
      (isAcyclic_addEdge_iff hG hap hpa).mpr hnGp
    have hnG1q : ¬(addEdge G a p).Reachable p q := fun h =>
      hpq (reachable_eq_of_isolated hG1q h)
    have hG2 : (addEdge (addEdge G a p) p q).IsAcyclic :=
      (isAcyclic_addEdge_iff hG1 hpq (fun h => hG1q p h.symm)).mpr hnG1q
    apply (isAcyclic_addEdge_iff hG2 (by simp [q, b]) (by
      intro h
      rcases h with h | ⟨h, _⟩
      · exact hG1q b h
      · simp [p, q, b] at h)).mpr
    intro hqb
    have hbq := hqb.symm
    have hbne : b ≠ q := by simp [b, q]
    rcases (reachable_addEdge_isolated hpq hG1q hbne).mp hbq with hbq | ⟨hbp, _⟩
    · exact hbne (reachable_eq_of_isolated hG1q hbq)
    · have hbnep : b ≠ p := by simp [b, p]
      rcases (reachable_addEdge_isolated hap hp hbnep).mp hbp with hbp | ⟨hba, _⟩
      · exact hbnep (reachable_eq_of_isolated hp hbp)
      · exact hnab hba.symm

private theorem labelledExtension_bot_isAcyclic_iff [DecidableEq E]
    (ends : E → V × V) (S : Finset E) :
    (labelledExtension (⊥ : SimpleGraph V) ends S).IsAcyclic ↔
      ∀ e ∈ S, ¬(labelledExtension (⊥ : SimpleGraph V) ends (S.erase e)).Reachable
        (Sum.inl (ends e).1) (Sum.inl (ends e).2) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hbot : labelledExtension (⊥ : SimpleGraph V) ends ∅ = ⊥ := by
        ext x y
        simp [labelledExtension, SimpleGraph.map_adj]
      simp [hbot]
  | @insert e S he ih =>
      constructor
      · intro hAll f hf
        have hfne : f ∉ (insert e S).erase f := not_mem_erase f _
        have hins : insert f ((insert e S).erase f) = insert e S :=
          insert_erase hf
        have hAll' :
            (labelledExtension (⊥ : SimpleGraph V) ends
              (insert f ((insert e S).erase f))).IsAcyclic := by
          rw [hins]
          exact hAll
        have h := (labelledExtension_insert_isAcyclic_iff
          (H := (⊥ : SimpleGraph V)) (ends := ends) hfne).mp hAll'
        exact h.2
      · intro hInd
        have heInd : ¬(labelledExtension (⊥ : SimpleGraph V) ends S).Reachable
            (Sum.inl (ends e).1) (Sum.inl (ends e).2) := by
          simpa [erase_insert he] using hInd e (mem_insert_self e S)
        have hOldInd : ∀ f ∈ S,
            ¬(labelledExtension (⊥ : SimpleGraph V) ends (S.erase f)).Reachable
              (Sum.inl (ends f).1) (Sum.inl (ends f).2) := by
          intro f hf hreach
          have hfe : f ≠ e := by
            intro hfe
            subst f
            exact he hf
          apply hInd f (mem_insert_of_mem hf)
          apply hreach.mono
          apply labelledExtension_mono le_rfl
          intro x hx
          simp only [mem_erase] at hx ⊢
          exact ⟨hx.1, mem_insert_of_mem hx.2⟩
        exact (labelledExtension_insert_isAcyclic_iff
          (H := (⊥ : SimpleGraph V)) (ends := ends) he).mpr ⟨ih.mpr hOldInd, heInd⟩

/-- The erase-one-label condition is exactly acyclicity of the label-retaining
component quotient.  The theorem is independent of any enumeration of `S`. -/
theorem labelledEdgeIndependent_iff_labelledQuotientForest [DecidableEq E]
    (H : SimpleGraph V) (ends : E → V × V) (S : Finset E) :
    LabelledEdgeIndependent H ends S ↔ LabelledQuotientForest H ends S := by
  classical
  rw [LabelledQuotientForest, labelledComponentQuotient,
    labelledExtension_bot_isAcyclic_iff]
  constructor
  · intro h e he
    exact (h e he).2
  · intro h e he
    refine ⟨?_, h e he⟩
    intro hsame
    apply h e he
    rw [hsame]

/-- Acyclicity form of `labelledEdgeIndependent_iff_labelledQuotientForest`. -/
theorem labelledComponentQuotient_isAcyclic_iff
    [DecidableEq E] (H : SimpleGraph V) (ends : E → V × V) (S : Finset E) :
    (labelledComponentQuotient H ends S).IsAcyclic ↔
      LabelledEdgeIndependent H ends S := by
  exact (labelledEdgeIndependent_iff_labelledQuotientForest H ends S).symm

private noncomputable def componentRepresentative (H : SimpleGraph V)
    (c : H.ConnectedComponent) : V :=
  Classical.choose c.exists_rep

@[simp] private lemma connectedComponentMk_componentRepresentative (H : SimpleGraph V)
    (c : H.ConnectedComponent) :
    H.connectedComponentMk (componentRepresentative H c) = c :=
  Classical.choose_spec c.exists_rep

private def collapseExtensionVertex (H : SimpleGraph V) :
    LabelledExtensionVertex V E → LabelledExtensionVertex H.ConnectedComponent E
  | Sum.inl v => Sum.inl (H.connectedComponentMk v)
  | Sum.inr eb => Sum.inr eb

private noncomputable def sectionExtensionVertex (H : SimpleGraph V) :
    LabelledExtensionVertex H.ConnectedComponent E → LabelledExtensionVertex V E
  | Sum.inl c => Sum.inl (componentRepresentative H c)
  | Sum.inr eb => Sum.inr eb

@[simp] private lemma collapse_sectionExtensionVertex (H : SimpleGraph V)
    (x : LabelledExtensionVertex H.ConnectedComponent E) :
    collapseExtensionVertex H (sectionExtensionVertex H x) = x := by
  cases x <;> simp [collapseExtensionVertex, sectionExtensionVertex]

private lemma adj_finset_sup_exists {W : Type*} (F : E → SimpleGraph W)
    (S : Finset E) {x y : W} (h : (S.sup F).Adj x y) :
    ∃ e ∈ S, (F e).Adj x y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at h
  | @insert e S he ih =>
      rw [sup_insert, sup_adj] at h
      rcases h with h | h
      · exact ⟨e, mem_insert_self e S, h⟩
      · obtain ⟨f, hf, h⟩ := ih h
        exact ⟨f, mem_insert_of_mem hf, h⟩

private lemma labelledExtension_base_reachable {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E} {u v : V} (h : H.Reachable u v) :
    (labelledExtension H ends S).Reachable (Sum.inl u) (Sum.inl v) := by
  let f : H →g labelledExtension H ends S :=
    { toFun := Sum.inl
      map_rel' := by
        intro x y hxy
        exact Or.inl ⟨x, y, hxy, rfl, rfl⟩ }
  exact h.map f

private lemma section_collapse_reachable [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E} (x : LabelledExtensionVertex V E) :
    (labelledExtension H ends S).Reachable x
      (sectionExtensionVertex H (collapseExtensionVertex H x)) := by
  cases x with
  | inl v =>
      apply labelledExtension_base_reachable
      apply ConnectedComponent.exact
      simp [sectionExtensionVertex, collapseExtensionVertex]
  | inr eb => exact Reachable.refl _

private lemma collapse_adj_reachable [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E} {x y : LabelledExtensionVertex V E}
    (hxy : (labelledExtension H ends S).Adj x y) :
    (labelledComponentQuotient H ends S).Reachable
      (collapseExtensionVertex H x) (collapseExtensionVertex H y) := by
  rw [labelledExtension, sup_adj] at hxy
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨u, v, huv, rfl, rfl⟩
    simp only [collapseExtensionVertex]
    rw [ConnectedComponent.sound huv.reachable]
  · obtain ⟨e, he, hxy⟩ := adj_finset_sup_exists (labelledPath ends) S hxy
    apply Adj.reachable
    rw [labelledComponentQuotient, labelledExtension, sup_adj]
    right
    have hle : labelledPath (componentEnds H ends) e ≤
        S.sup (labelledPath (componentEnds H ends)) := Finset.le_sup he
    apply hle
    cases x <;> cases y <;>
      simp [labelledPath, componentEnds, collapseExtensionVertex] at hxy ⊢ <;> aesop

private lemma collapse_reachable [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E} {x y : LabelledExtensionVertex V E}
    (hxy : (labelledExtension H ends S).Reachable x y) :
    (labelledComponentQuotient H ends S).Reachable
      (collapseExtensionVertex H x) (collapseExtensionVertex H y) := by
  rw [reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact Reachable.refl _
  | tail h hadj ih => exact ih.trans (collapse_adj_reachable hadj)

private lemma quotient_adj_sections_reachable [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E}
    {x y : LabelledExtensionVertex H.ConnectedComponent E}
    (hxy : (labelledComponentQuotient H ends S).Adj x y) :
    (labelledExtension H ends S).Reachable
      (sectionExtensionVertex H x) (sectionExtensionVertex H y) := by
  rw [labelledComponentQuotient, labelledExtension, sup_adj] at hxy
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨u, v, huv, _, _⟩
    simp at huv
  · obtain ⟨e, he, hxy : (labelledPath (componentEnds H ends) e).Adj x y⟩ :=
      adj_finset_sup_exists (labelledPath (componentEnds H ends)) S hxy
    have hedge {a b : LabelledExtensionVertex V E}
        (hab : (labelledPath ends e).Adj a b) :
        (labelledExtension H ends S).Reachable a b := by
      apply Adj.reachable
      rw [labelledExtension, sup_adj]
      have hle : labelledPath ends e ≤ S.sup (labelledPath ends) := Finset.le_sup he
      exact Or.inr (hle hab)
    simp only [labelledPath, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
      Sym2.eq_iff, componentEnds] at hxy
    rcases hxy with (hxy | hxy) | hxy
    · rcases hxy with ⟨hxy | hxy, _⟩
      · rcases hxy with ⟨rfl, rfl⟩
        exact (labelledExtension_base_reachable
          (ConnectedComponent.exact (connectedComponentMk_componentRepresentative H _))).trans
            (hedge (by simp [labelledPath, sectionExtensionVertex]))
      · rcases hxy with ⟨rfl, rfl⟩
        exact (hedge (by simp [labelledPath, sectionExtensionVertex])).trans
          (labelledExtension_base_reachable
            (ConnectedComponent.exact
              (connectedComponentMk_componentRepresentative H _).symm))
    · rcases hxy with ⟨hxy | hxy, _⟩
      · rcases hxy with ⟨rfl, rfl⟩
        exact hedge (by simp [labelledPath, sectionExtensionVertex])
      · rcases hxy with ⟨rfl, rfl⟩
        exact hedge (by simp [labelledPath, sectionExtensionVertex])
    · rcases hxy with ⟨hxy | hxy, _⟩
      · rcases hxy with ⟨rfl, rfl⟩
        exact (hedge (by simp [labelledPath, sectionExtensionVertex])).trans
          (labelledExtension_base_reachable
            (ConnectedComponent.exact
              (connectedComponentMk_componentRepresentative H _).symm))
      · rcases hxy with ⟨rfl, rfl⟩
        exact (labelledExtension_base_reachable
          (ConnectedComponent.exact (connectedComponentMk_componentRepresentative H _))).trans
            (hedge (by simp [labelledPath, sectionExtensionVertex]))

private lemma quotient_reachable_sections [DecidableEq E] {H : SimpleGraph V}
    {ends : E → V × V} {S : Finset E}
    {x y : LabelledExtensionVertex H.ConnectedComponent E}
    (hxy : (labelledComponentQuotient H ends S).Reachable x y) :
    (labelledExtension H ends S).Reachable
      (sectionExtensionVertex H x) (sectionExtensionVertex H y) := by
  rw [reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact Reachable.refl _
  | tail h hadj ih => exact ih.trans (quotient_adj_sections_reachable hadj)

/-- Reachability is unchanged by contracting the acyclic base graph to its
connected components.  This statement does not require `H` to be acyclic. -/
theorem labelledExtension_reachable_iff_componentQuotient [DecidableEq E]
    (H : SimpleGraph V) (ends : E → V × V) (S : Finset E)
    (x y : LabelledExtensionVertex V E) :
    (labelledExtension H ends S).Reachable x y ↔
      (labelledComponentQuotient H ends S).Reachable
        (collapseExtensionVertex H x) (collapseExtensionVertex H y) := by
  constructor
  · exact collapse_reachable
  · intro hxy
    exact (section_collapse_reachable x).trans
      ((quotient_reachable_sections hxy).trans (section_collapse_reachable y).symm)

private def inlEmbedding (V X : Type*) : V ↪ V ⊕ X :=
  ⟨fun v => Sum.inl v, Sum.inl_injective⟩

private lemma map_inl_walk_exists {X : Type*} {H : SimpleGraph V}
    {x y : V ⊕ X} (p : (H.map (inlEmbedding V X)).Walk x y) :
    ∀ (u : V) (hu : x = Sum.inl u), ∀ (v : V) (hv : y = Sum.inl v),
      ∃ q : H.Walk u v,
        q.map (SimpleGraph.Embedding.map (inlEmbedding V X) H).toHom =
          p.copy hu hv := by
  induction p with
  | nil =>
      intro u hu v hv
      have huv : u = v := Sum.inl.inj (hu.symm.trans hv)
      subst v
      exact ⟨Walk.nil, by simp [Walk.copy_nil]⟩
  | cons h p ih =>
      intro u hu v hv
      cases hu
      cases hv
      rcases h with ⟨a, b, hab, ha, hb⟩
      have hau : a = u := Sum.inl.inj ha
      subst a
      cases ha
      cases hb
      obtain ⟨q, hq⟩ := ih b rfl v rfl
      refine ⟨Walk.cons hab q, ?_⟩
      simp [hq]

private lemma isAcyclic_map_inl {X : Type*} {H : SimpleGraph V} (hH : H.IsAcyclic) :
    (H.map (inlEmbedding V X)).IsAcyclic := by
  intro x c hc
  cases c with
  | nil => exact hc.not_of_nil
  | cons ha p =>
      let c0 := Walk.cons ha p
      have hc0 : c0.IsCycle := hc
      rcases ha with ⟨u, v, huv, hu, hv⟩
      subst x
      subst_vars
      obtain ⟨q, hq⟩ := map_inl_walk_exists p v rfl u rfl
      let qcycle : H.Walk u u := Walk.cons huv q
      have hmap : qcycle.map (SimpleGraph.Embedding.map
          (inlEmbedding V X) H).toHom = c0 := by
        simp [qcycle, c0, hq]
      have hqc : qcycle.IsCycle := by
        apply (Walk.map_isCycle_iff_of_injective (p := qcycle)
          (f := (SimpleGraph.Embedding.map (inlEmbedding V X) H).toHom)
          Sum.inl_injective).mp
        simpa [hmap] using hc0
      exact hH qcycle hqc

private theorem labelledExtension_isAcyclic_iff_erased [DecidableEq E]
    {H : SimpleGraph V} (hH : H.IsAcyclic) (ends : E → V × V) (S : Finset E) :
    (labelledExtension H ends S).IsAcyclic ↔
      ∀ e ∈ S, ¬(labelledExtension H ends (S.erase e)).Reachable
        (Sum.inl (ends e).1) (Sum.inl (ends e).2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isAcyclic_map_inl (X := E × Bool) hH)
  | @insert e S he ih =>
      constructor
      · intro hAll f hf
        have hfne : f ∉ (insert e S).erase f := notMem_erase f _
        have hins : insert f ((insert e S).erase f) = insert e S := insert_erase hf
        have hAll' :
            (labelledExtension H ends (insert f ((insert e S).erase f))).IsAcyclic := by
          rw [hins]
          exact hAll
        exact ((labelledExtension_insert_isAcyclic_iff
          (H := H) (ends := ends) hfne).mp hAll').2
      · intro hInd
        have heInd : ¬(labelledExtension H ends S).Reachable
            (Sum.inl (ends e).1) (Sum.inl (ends e).2) := by
          simpa [erase_insert he] using hInd e (mem_insert_self e S)
        have hOldInd : ∀ f ∈ S,
            ¬(labelledExtension H ends (S.erase f)).Reachable
              (Sum.inl (ends f).1) (Sum.inl (ends f).2) := by
          intro f hf hreach
          apply hInd f (mem_insert_of_mem hf)
          apply hreach.mono
          apply labelledExtension_mono le_rfl
          intro x hx
          simp only [mem_erase] at hx ⊢
          exact ⟨hx.1, mem_insert_of_mem hx.2⟩
        exact (labelledExtension_insert_isAcyclic_iff
          (H := H) (ends := ends) he).mpr ⟨ih.mpr hOldInd, heInd⟩

/-- Contracting an acyclic base graph preserves acyclicity after adjoining any
finite family of label-retaining subdivided physical edges.

No injectivity assumption on endpoint pairs is needed: physical parallel edges
and loops remain distinct because every label has private subdivision vertices. -/
theorem labelledExtension_isAcyclic_iff_componentQuotient
    [DecidableEq E] (H : SimpleGraph V) (hH : H.IsAcyclic)
    (ends : E → V × V) (S : Finset E) :
    (labelledExtension H ends S).IsAcyclic ↔
      (labelledComponentQuotient H ends S).IsAcyclic := by
  rw [labelledExtension_isAcyclic_iff_erased hH]
  rw [labelledComponentQuotient_isAcyclic_iff]
  constructor
  · intro h e he
    refine ⟨?_, ?_⟩
    · intro hsame
      apply h e he
      apply labelledExtension_base_reachable
      exact ConnectedComponent.exact hsame
    · intro hq
      apply h e he
      apply (labelledExtension_reachable_iff_componentQuotient
        H ends (S.erase e) (Sum.inl (ends e).1) (Sum.inl (ends e).2)).mpr
      simpa [collapseExtensionVertex, componentEnds] using hq
  · intro h e he
    intro hp
    apply (h e he).2
    have hq := (labelledExtension_reachable_iff_componentQuotient
      H ends (S.erase e) (Sum.inl (ends e).1) (Sum.inl (ends e).2)).mp hp
    simpa [collapseExtensionVertex, componentEnds] using hq

end SimpleGraph
