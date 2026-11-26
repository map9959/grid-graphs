import GridGraphs.Geometry.CapPitchArrows

namespace GridGraphs.CapBill
open SimpleGraph Finset

/-- Zero extension of the padded board to lattice coordinates. Unlike
clamping an index, it does not identify the two ends of a missing edge. -/
abbrev Pt := Int × Int
def coord {r h} (x : Cell r h) : Pt := (x.1.val,x.2.val)
def onBoard {r h} (F : Finset (Cell r h)) (p : Pt) := ∃ v∈F, coord v=p
def sends {r h} (F : Finset (Cell r h)) (p q : Pt) :=
  ∃ v w, coord v=p ∧ coord w=q ∧ (bonds F).Adj v w ∧ arrow F v=w
def unitEdge (p q : Pt) : Prop :=
  (p.1=q.1 ∧ (p.2+1=q.2 ∨ q.2+1=p.2)) ∨
  (p.2=q.2 ∧ (p.1+1=q.1 ∨ q.1+1=p.1))

theorem coord_injective {r h} : Function.Injective (coord (r:=r) (h:=h)) := by
  intro v w eq
  exact Prod.ext (Fin.ext (by exact_mod_cast (Prod.mk.inj eq).1))
    (Fin.ext (by exact_mod_cast (Prod.mk.inj eq).2))

private theorem adj_coords {r h} (v w : Cell r h) :
    (board r h).Adj v w ↔ unitEdge (coord v) (coord w) := by
  change (_ ∨ _) ↔ _
  simp only [unitEdge,coord,Fin.ext_iff]; omega

theorem sends_unique {r h} {F : Finset (Cell r h)} {p a b}
    (ha : sends F p a) (hb : sends F p b) : a=b := by
  obtain ⟨v,w,rfl,rfl,_,e⟩ := ha
  obtain ⟨v',w',eq,rfl,_,e'⟩ := hb
  have := coord_injective eq; subst v'; rw [e] at e'; rw [e']

theorem sends_not_reverse {r h} {F : Finset (Cell r h)} {p q}
    (forward : sends F p q) : ¬sends F q p := by
  obtain ⟨v,w,rfl,rfl,adj,e⟩ := forward
  rintro ⟨a,b,ha,hb,_,back⟩
  cases coord_injective ha
  cases coord_injective hb
  have down {x y : Cell r h} (ne : x≠y) (out : arrow F x=y) :
      depth (capDest F) y < depth (capDest F) x := by
    have nonroot : x≠dest (capDest F) x := by
      intro fixed
      have := (parent_fix (capDest F) (root_class _ _ _) x).mpr fixed
      change arrow F x=x at this; rw [out] at this; exact ne this.symm
    exact out ▸ (parent_step (capDest F) (root_class _ _ _) nonroot).2
  exact (not_lt_of_ge (down adj.ne e).le) (down adj.ne.symm back)

theorem sends_forced {r h} {F : Finset (Cell r h)} {p q} (a : sends F p q) :
    unitEdge p q ∧ (onBoard F p ∨ onBoard F q) := by
  obtain ⟨v,w,rfl,rfl,e,_⟩ := a
  exact ⟨(adj_coords v w).mp e.1,e.2.elim
    (fun m => Or.inl ⟨_,m,rfl⟩) (fun m => Or.inr ⟨_,m,rfl⟩)⟩

private theorem realize_neighbor {r h} {F : Finset (Cell r h)} (pad : Padded F)
    {v : Cell r h} (vm : v∈F) (q : Pt) (above : 0≤q.1) (near : unitEdge (coord v) q) :
    ∃ w : Cell r h, coord w=q := by
  obtain ⟨qy,qx⟩ := q
  have room := pad.sides v vm; have endRow := pad.bottom v vm
  simp only [coord,unitEdge] at near
  dsimp at above
  refine ⟨(⟨qy.toNat,by omega⟩,⟨qx.toNat,by omega⟩),?_⟩
  simp [coord,Int.toNat_of_nonneg above,Int.toNat_of_nonneg (show 0≤qx by omega)]

/-- Every forced bond of the zero-extended half-plane has exactly one
sender, including bonds adjacent to a blank guard or the far blank row. -/
theorem oriented_bond {r h} {F : Finset (Cell r h)} (pad : Padded F) {p q : Pt}
    (p0 : 0≤p.1) (q0 : 0≤q.1) (adj : unitEdge p q) :
    (sends F p q ∨ sends F q p) ↔ (onBoard F p ∨ onBoard F q) := by
  constructor
  · rintro (s|s)
    · exact (sends_forced s).2
    · exact (sends_forced s).2.symm
  · have fromMark {p q : Pt} (z : 0≤q.1) (e : unitEdge p q) (m : onBoard F p) :
        sends F p q ∨ sends F q p := by
      obtain ⟨v,hv,rfl⟩ := m
      obtain ⟨w,rfl⟩ := realize_neighbor pad hv q z e
      have edge : (bonds F).Adj v w := ⟨(adj_coords _ _).mpr e,Or.inl hv⟩
      rcases parent_covers (capDest F) (root_class _ _ _) pad.forest edge with dir|dir
      · exact Or.inl ⟨_,_,rfl,rfl,edge,dir⟩
      · exact Or.inr ⟨_,_,rfl,rfl,edge.symm,dir⟩
    rintro (m|m)
    · exact fromMark q0 adj m
    · exact (fromMark p0 (by unfold unitEdge at *; grind) m).symm

/-- Nonsending blank sites really are isolates, rather than free roots on
a slit. Conversely the nonsending marked sites are exactly chosen roots. -/
theorem sending_iff {r h} {F : Finset (Cell r h)} (v : Cell r h) :
    (∃ q, sends F (coord v) q) ↔ ¬keeps (board r h) (terminalSet F) F v := by
  constructor
  · rintro ⟨q,a,b,ha,_,edge,e⟩ fixed
    have := coord_injective ha; subst a
    have fix := (parent_fix (capDest F) (root_class _ _ _) v).mpr fixed
    change arrow F v=v at fix; rw [e] at fix; exact edge.ne fix.symm
  · intro nf
    exact ⟨_,_,_,rfl,rfl,(parent_step (capDest F) (root_class _ _ _) nf).1,rfl⟩

theorem blank_has_sender {r h} {F : Finset (Cell r h)} {p q : Pt} (blank : ¬onBoard F p)
    (edge : sends F p q ∨ sends F q p) : ∃ z, sends F p z := by
  rcases edge with out|incoming
  · exact ⟨q,out⟩
  obtain ⟨w,v,rfl,rfl,e,_⟩ := incoming
  have bv : v ∉ F := fun m => blank ⟨_,m,rfl⟩
  have mw := e.2.resolve_right bv
  apply (sending_iff v).mpr
  intro fixed
  have zero := (blank_fixed (board r h) _ F (filter_subset _ _) bv).mp fixed
  have pos : (F.filter fun a => (board r h).Adj a v).Nonempty := ⟨w,mem_filter.mpr ⟨mw,e.1⟩⟩
  have := card_pos.mpr pos
  unfold hits at zero; omega

end GridGraphs.CapBill
