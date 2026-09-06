import GridGraphs.Routing.LocalizedHallRouting

/-!
# Finite alternating exchange

Geometry-independent infrastructure for alternating searches in a finite
bipartite incidence relation.  A partial matching is oriented from resources
to their current owners.  This makes the forced resource-to-source half of an
alternating search canonical.
-/

namespace GridGraphs

open Finset

section Matching

variable {Source Resource : Type*}

/-- A partial injective matching, oriented from resources to sources. -/
structure PartialMatching (Adjacent : Source → Resource → Prop) where
  owner : Resource → Option Source
  owner_injective : ∀ {r₁ r₂ s}, owner r₁ = some s → owner r₂ = some s → r₁ = r₂
  adjacent_owner : ∀ {r s}, owner r = some s → Adjacent s r

namespace PartialMatching

variable {Adjacent : Source → Resource → Prop} (M : PartialMatching Adjacent)

/-- A source is currently represented by the partial matching. -/
def IsMatched (s : Source) : Prop := ∃ r, M.owner r = some s

/-- A resource is currently free. -/
def IsUnowned (r : Resource) : Prop := M.owner r = none

/-- A source-to-resource incidence step or the forced step from an owned
resource to its owner. -/
inductive Step : (Source ⊕ Resource) → (Source ⊕ Resource) → Prop
  | toResource {s r} (hadj : Adjacent s r) : Step (.inl s) (.inr r)
  | toOwner {r s} (howner : M.owner r = some s) : Step (.inr r) (.inl s)

/-- Alternating reachability from a source. -/
def Reachable (root : Source) (x : Source ⊕ Resource) : Prop :=
  Relation.ReflTransGen M.Step (.inl root) x

theorem reachable_root (root : Source) : M.Reachable root (.inl root) :=
  Relation.ReflTransGen.refl

theorem reachable_resource_of_source {root s r}
    (hs : M.Reachable root (.inl s)) (hadj : Adjacent s r) :
    M.Reachable root (.inr r) :=
  hs.tail (.toResource hadj)

theorem reachable_owner_of_resource {root r s}
    (hr : M.Reachable root (.inr r)) (howner : M.owner r = some s) :
    M.Reachable root (.inl s) :=
  hr.tail (.toOwner howner)

theorem exists_reachable_owner_of_reachable_source {root s}
    (hs : M.Reachable root (.inl s)) (hne : s ≠ root) :
    ∃ r, M.Reachable root (.inr r) ∧ M.owner r = some s := by
  cases hs with
  | refl => exact False.elim (hne rfl)
  | tail hprefix hstep =>
      cases hstep with
      | toOwner howner => exact ⟨_, hprefix, howner⟩

/-- Occurrence-labelled alternating states retain the source which initiated
their search, even if different searches reach the same bipartite vertex. -/
structure OccurrenceState (Source Resource : Type*) where
  origin : Source
  vertex : Source ⊕ Resource

/-- A step between occurrence states never merges their origins. -/
def OccurrenceStep (x y : OccurrenceState Source Resource) : Prop :=
  x.origin = y.origin ∧ M.Step x.vertex y.vertex

theorem origin_eq_of_occurrencePath {x y : OccurrenceState Source Resource}
    (hxy : Relation.ReflTransGen M.OccurrenceStep x y) :
    y.origin = x.origin := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih => exact hstep.1.symm.trans ih

end PartialMatching

end Matching

section Exchange

variable {Source Resource : Type*} [DecidableEq Source]
    {Adjacent : Source → Resource → Prop}

noncomputable local instance : DecidableEq Resource := Classical.decEq Resource

/-- A finite alternating exchange certificate.  Resources used by the
replacement are either free or currently owned inside the exchanged source
set, so no source outside the set can be displaced. -/
structure FiniteExchange (M : PartialMatching Adjacent) (root : Source) where
  sources : Finset Source
  root_mem : root ∈ sources
  root_unmatched : ¬M.IsMatched root
  replacement : Source → Resource
  replacement_adjacent : ∀ s ∈ sources, Adjacent s (replacement s)
  replacement_injective : Set.InjOn replacement sources
  replacement_available : ∀ s ∈ sources,
    M.owner (replacement s) = none ∨
      ∃ t ∈ sources, M.owner (replacement s) = some t

namespace FiniteExchange

variable {M : PartialMatching Adjacent} {root : Source}

/-- Resource ownership after simultaneously applying an exchange. -/
noncomputable def exchangedOwner (E : FiniteExchange M root) (r : Resource) :
    Option Source :=
  if h : ∃ s, s ∈ E.sources ∧ E.replacement s = r then
    some (Classical.choose h)
  else
    match M.owner r with
    | some s => if s ∈ E.sources then none else some s
    | none => none

theorem exchangedOwner_eq_some_of_not_range (E : FiniteExchange M root)
    {r : Resource} {s : Source}
    (h : ¬∃ t, t ∈ E.sources ∧ E.replacement t = r) :
    E.exchangedOwner r = some s ↔ M.owner r = some s ∧ s ∉ E.sources := by
  rw [exchangedOwner, dif_neg h]
  cases ho : M.owner r with
  | none => simp
  | some t =>
      simp only [Option.some.injEq]
      by_cases ht : t ∈ E.sources
      · rw [if_pos ht]
        constructor
        · intro hnone
          cases hnone
        · rintro ⟨hts, hs⟩
          exact False.elim (hs (hts ▸ ht))
      · simp only [if_neg ht, Option.some.injEq]
        constructor
        · intro hts
          exact ⟨hts, hts ▸ ht⟩
        · exact fun h => h.1

theorem exchangedOwner_replacement (E : FiniteExchange M root)
    {s : Source} (hs : s ∈ E.sources) :
    E.exchangedOwner (E.replacement s) = some s := by
  let h : ∃ t, t ∈ E.sources ∧ E.replacement t = E.replacement s := ⟨s, hs, rfl⟩
  have heq : Classical.choose h = s := E.replacement_injective
    (Classical.choose_spec h).1 hs (Classical.choose_spec h).2
  simp [exchangedOwner, h, heq]

theorem exchangedOwner_of_owner_not_mem (E : FiniteExchange M root)
    {r : Resource} {s : Source} (howner : M.owner r = some s)
    (hs : s ∉ E.sources) : E.exchangedOwner r = some s := by
  have hnrange : ¬∃ t, t ∈ E.sources ∧ E.replacement t = r := by
    rintro ⟨t, ht, htr⟩
    rcases E.replacement_available t ht with hfree | ⟨u, hu, huowner⟩
    · rw [htr, howner] at hfree
      cases hfree
    · have hus : u = s := Option.some.inj (huowner.symm.trans (htr ▸ howner))
      exact hs (hus ▸ hu)
  exact (E.exchangedOwner_eq_some_of_not_range hnrange).2 ⟨howner, hs⟩

/-- Install all replacement edges simultaneously, clearing obsolete edges
owned by exchanged sources. -/
noncomputable def toMatching (E : FiniteExchange M root) :
    PartialMatching Adjacent where
  owner := E.exchangedOwner
  owner_injective := by
    intro r₁ r₂ s hr₁ hr₂
    by_cases h₁ : ∃ t, t ∈ E.sources ∧ E.replacement t = r₁
    · by_cases h₂ : ∃ t, t ∈ E.sources ∧ E.replacement t = r₂
      · have hc₁ : Classical.choose h₁ = s := by
          simpa [exchangedOwner, h₁] using hr₁
        have hc₂ : Classical.choose h₂ = s := by
          simpa [exchangedOwner, h₂] using hr₂
        calc
          r₁ = E.replacement (Classical.choose h₁) :=
            (Classical.choose_spec h₁).2.symm
          _ = E.replacement (Classical.choose h₂) := by rw [hc₁, hc₂]
          _ = r₂ := (Classical.choose_spec h₂).2
      · have hold₂ : M.owner r₂ = some s ∧ s ∉ E.sources := by
          exact (E.exchangedOwner_eq_some_of_not_range h₂).1 hr₂
        have hc₁ : Classical.choose h₁ = s := by
          simpa [exchangedOwner, h₁] using hr₁
        exact False.elim (hold₂.2 (hc₁ ▸ (Classical.choose_spec h₁).1))
    · by_cases h₂ : ∃ t, t ∈ E.sources ∧ E.replacement t = r₂
      · have hold₁ : M.owner r₁ = some s ∧ s ∉ E.sources := by
          exact (E.exchangedOwner_eq_some_of_not_range h₁).1 hr₁
        have hc₂ : Classical.choose h₂ = s := by
          simpa [exchangedOwner, h₂] using hr₂
        exact False.elim (hold₁.2 (hc₂ ▸ (Classical.choose_spec h₂).1))
      · have hold₁ : M.owner r₁ = some s ∧ s ∉ E.sources := by
          exact (E.exchangedOwner_eq_some_of_not_range h₁).1 hr₁
        have hold₂ : M.owner r₂ = some s ∧ s ∉ E.sources := by
          exact (E.exchangedOwner_eq_some_of_not_range h₂).1 hr₂
        exact M.owner_injective hold₁.1 hold₂.1
  adjacent_owner := by
    intro r s hrs
    by_cases h : ∃ t, t ∈ E.sources ∧ E.replacement t = r
    · have hc : Classical.choose h = s := by
        simpa [exchangedOwner, h] using hrs
      have ha := E.replacement_adjacent (Classical.choose h)
        (Classical.choose_spec h).1
      have ha' : Adjacent s (E.replacement s) := by simpa only [hc] using ha
      have hrepl : E.replacement s = r := by
        simpa only [hc] using (Classical.choose_spec h).2
      exact hrepl ▸ ha'
    · have hold : M.owner r = some s ∧ s ∉ E.sources := by
        exact (E.exchangedOwner_eq_some_of_not_range h).1 hrs
      exact M.adjacent_owner hold.1

/-- One matching augments another at a source when it newly matches that
source without losing any previously matched source. -/
def Augments (M M' : PartialMatching Adjacent) (root : Source) : Prop :=
  ¬M.IsMatched root ∧
    (∀ s, M.IsMatched s → M'.IsMatched s) ∧ M'.IsMatched root

/-- Every certified finite alternating exchange augments the matching at its
unmatched root. -/
theorem toMatching_augments (E : FiniteExchange M root) :
    Augments M E.toMatching root := by
  refine ⟨E.root_unmatched, ?_, ?_⟩
  · intro s hs
    by_cases hsource : s ∈ E.sources
    · refine ⟨E.replacement s, ?_⟩
      exact E.exchangedOwner_replacement hsource
    · obtain ⟨r, hr⟩ := hs
      refine ⟨r, ?_⟩
      exact E.exchangedOwner_of_owner_not_mem hr hsource
  · refine ⟨E.replacement root, ?_⟩
    exact E.exchangedOwner_replacement E.root_mem

end FiniteExchange

/-- A typed alternating path to a free resource together with the finite
rerouting extracted from it.  Recording the exchange separately permits the
reachability path to contain cycles while the rerouting remains injective. -/
structure CertifiedAugmentingPath (M : PartialMatching Adjacent) (root : Source) where
  terminal : Resource
  path : M.Reachable root (.inr terminal)
  terminal_unowned : M.IsUnowned terminal
  exchange : FiniteExchange M root

namespace CertifiedAugmentingPath

/-- A certified alternating path ending at an unowned resource augments the
current matching without losing any previously matched source. -/
theorem augments (P : CertifiedAugmentingPath M root) :
    FiniteExchange.Augments (Adjacent := Adjacent)
      M P.exchange.toMatching root :=
  P.exchange.toMatching_augments

end CertifiedAugmentingPath

end Exchange

section Closure

variable {Source Resource : Type*} [DecidableEq Source] [DecidableEq Resource]
    {Adjacent : Source → Resource → Prop}

/-- The finite neighborhood induced by a bipartite adjacency relation. -/
def adjacencyNeighborhood [Fintype Resource] (Adjacent : Source → Resource → Prop)
    [DecidableRel Adjacent] (s : Source) : Finset Resource :=
  Finset.univ.filter (Adjacent s)

/-- A saturated alternating closure around an unmatched root.  Every resource
neighboring the closure is owned in the closure, and every non-root source in
the closure is represented by one of those resources. -/
structure DeficientClosure [Fintype Resource] [DecidableRel Adjacent]
    (M : PartialMatching Adjacent) (root : Source) where
  sources : Finset Source
  root_mem : root ∈ sources
  root_unmatched : ¬M.IsMatched root
  closed_owner : ∀ r ∈ sources.biUnion (adjacencyNeighborhood Adjacent),
    ∃ s ∈ sources, M.owner r = some s
  represented : ∀ s ∈ sources, s ≠ root →
    ∃ r ∈ sources.biUnion (adjacencyNeighborhood Adjacent), M.owner r = some s

namespace DeficientClosure

variable [Fintype Resource] [DecidableRel Adjacent]
    {M : PartialMatching Adjacent} {root : Source}

/-- If an alternating search from an unmatched root reaches no free resource,
its reachable sources form a saturated deficient closure. -/
noncomputable def ofNoAugmentingPath [Fintype Source]
    (hroot : ¬M.IsMatched root)
    (hno : ∀ r, M.Reachable root (.inr r) → ¬M.IsUnowned r) :
    DeficientClosure M root := by
  classical
  let reached := Finset.univ.filter fun s => M.Reachable root (.inl s)
  refine
    { sources := reached
      root_mem := by simp [reached, M.reachable_root]
      root_unmatched := hroot
      closed_owner := ?_
      represented := ?_ }
  · intro r hr
    obtain ⟨s, hs, hadj⟩ := Finset.mem_biUnion.mp hr
    have hsreach : M.Reachable root (.inl s) := by simpa [reached] using hs
    have hrreach := M.reachable_resource_of_source hsreach
      (by simpa [adjacencyNeighborhood] using hadj)
    cases howner : M.owner r with
    | none => exact False.elim (hno r hrreach howner)
    | some t =>
        refine ⟨t, ?_, rfl⟩
        simp [reached, M.reachable_owner_of_resource hrreach howner]
  · intro s hs hne
    have hsreach : M.Reachable root (.inl s) := by simpa [reached] using hs
    obtain ⟨r, hrreach, howner⟩ :=
      M.exists_reachable_owner_of_reachable_source hsreach hne
    refine ⟨r, ?_, howner⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hs, ?_⟩
    simpa [adjacencyNeighborhood] using M.adjacent_owner howner

/-- A saturated alternating closure has exactly one more source than resource
neighbor: the unmatched root. -/
theorem neighborhood_card_lt (C : DeficientClosure M root) :
    (C.sources.biUnion (adjacencyNeighborhood Adjacent)).card < C.sources.card := by
  classical
  let N := C.sources.biUnion (adjacencyNeighborhood Adjacent)
  let ownerOf : Resource → Source := fun r =>
    if h : r ∈ N then Classical.choose (C.closed_owner r h) else root
  have howner {r} (hr : r ∈ N) : M.owner r = some (ownerOf r) := by
    simp only [ownerOf, dif_pos hr]
    exact (Classical.choose_spec (C.closed_owner r hr)).2
  have hmem {r} (hr : r ∈ N) : ownerOf r ∈ C.sources := by
    simp only [ownerOf, dif_pos hr]
    exact (Classical.choose_spec (C.closed_owner r hr)).1
  have hne {r} (hr : r ∈ N) : ownerOf r ≠ root := by
    intro heq
    apply C.root_unmatched
    exact ⟨r, (howner hr).trans (congrArg some heq)⟩
  have hinj : Set.InjOn ownerOf N := by
    intro r₁ hr₁ r₂ hr₂ heq
    exact M.owner_injective (howner hr₁) ((howner hr₂).trans (congrArg some heq).symm)
  have himage : N.image ownerOf = C.sources.erase root := by
    ext s
    constructor
    · intro hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_erase.mpr ⟨hne hr, hmem hr⟩
    · intro hs
      obtain ⟨hsne, hsC⟩ := Finset.mem_erase.mp hs
      obtain ⟨r, hr, hrs⟩ := C.represented s hsC hsne
      exact Finset.mem_image.mpr ⟨r, hr, Option.some.inj ((howner hr).symm.trans hrs)⟩
  have hcard : N.card = (C.sources.erase root).card := by
    rw [← himage, Finset.card_image_iff.mpr]
    intro r₁ hr₁ r₂ hr₂
    exact hinj hr₁ hr₂
  rw [hcard]
  exact (Finset.card_erase_lt_of_mem C.root_mem)

/-- In particular, a saturated closure is a Hall witness. -/
theorem not_localizedHall (C : DeficientClosure M root) :
    ¬LocalizedHall (adjacencyNeighborhood Adjacent) := by
  intro hHall
  have := hHall C.sources
  exact (Nat.not_le_of_lt C.neighborhood_card_lt) this

/-- No augmenting path from an unmatched source supplies a strict Hall
obstruction on the finite alternating closure. -/
theorem not_localizedHall_of_no_augmentingPath [Fintype Source]
    (hroot : ¬M.IsMatched root)
    (hno : ∀ r, M.Reachable root (.inr r) → ¬M.IsUnowned r) :
    ¬LocalizedHall (adjacencyNeighborhood Adjacent) :=
  (ofNoAugmentingPath hroot hno).not_localizedHall

end DeficientClosure

end Closure

end GridGraphs
