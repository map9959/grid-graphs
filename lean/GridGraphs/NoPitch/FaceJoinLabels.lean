import GridGraphs.NoPitch.FaceJoinStops

namespace GridGraphs.NoPitch.FaceJoin
open Finset SimpleGraph PitchCut Wired

def pre (m : Mask) (q : PartitionBits) := (wires q).foldl merge (base m)
def post (m : Mask) (q : PartitionBits) := (newEdges m).foldl merge (pre m q)
def colors (s : Labels) := univ.image fun c : Corner => s[cv c]
/-- `rank44_faces.table`: number of wired corner labels lost on insertion
of the newly forced face edges. Refill acceptance is immaterial here. -/
def joins (m : Mask) (q : PartitionBits) := (colors (pre m q)).card-(colors (post m q)).card

private theorem fold_preserves (l : List E) (s : Labels) {x y : V} (eq : s[x]=s[y]) :
    (l.foldl merge s)[x]=(l.foldl merge s)[y] := by
  induction l generalizing s with
  | nil => exact eq
  | cons e l ih =>
    apply ih
    change s[x.val]=s[y.val] at eq
    simp [merge,eq]

private theorem fold_edge (s : Labels) (l : List E) {e : E} (h : e∈l) :
    (l.foldl merge s)[e.1]=(l.foldl merge s)[e.2] := by
  induction l generalizing s with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl|h
    · apply fold_preserves l (merge s e)
      change (s.map _)[e.1.val]=(s.map _)[e.2.val]
      simp
    · exact ih _ h

private theorem fold_sound {α : Type*} (f : V → α) (l : List E) (s : Labels)
    (sound : ∀ x y : V, s[x]=s[y] → f x=f y) (ok : ∀ e∈l, f e.1=f e.2) :
    ∀ x y : V, (l.foldl merge s)[x]=(l.foldl merge s)[y] → f x=f y := by
  induction l generalizing s with
  | nil => exact sound
  | cons e l ih =>
    apply ih
    · intro x y h
      change (s.map _)[x.val]=(s.map _)[y.val] at h
      simp only [Vector.getElem_map] at h
      have edge := ok e (by simp)
      split at h <;> split at h
      · rename_i a b; exact (sound _ _ a).trans (sound _ _ b).symm
      · rename_i a _; exact (sound _ _ a).trans (edge.symm.trans (sound _ _ h))
      · rename_i _ b; exact (sound _ _ h).trans (edge.trans (sound _ _ b).symm)
      · exact sound _ _ h
    · exact fun e he => ok e (by simp [he])

variable {k : Nat} (F : Finset (Site k)) (p : FacePos k)

private theorem place_box (x : V) : box p (place p x) := by
  have a := (cell x).1.isLt; have b := (cell x).2.isLt
  dsimp [box,place,coord]; omega

private theorem corner_joint (c : Corner) : corner p c∈Budget.joints k := by
  simp [Budget.joints,corner,cornerOffset,coord,Nat.mul_comm]

private theorem cv_eq (c : Corner) : place p (cv c)=corner p c := by
  have h : ∀ c : Corner, cell (cv c)=(cornerOffset c.1,cornerOffset c.2) := by decide
  simp [place,h,corner]

private theorem lay {e : E} (he : e∈es) : (gridGraph (N k) (N k)).Adj (place p e.1) (place p e.2) := by
  have h : ∀ e∈es, (gridGraph 4 4).Adj (cell e.1) (cell e.2) := by decide +kernel
  specialize h e he
  change adjacent _ _ _ _ at h ⊢
  simp only [adjacent,place,coord,Fin.ext_iff] at h ⊢
  omega

private theorem old_adj {e} (he : e∈baseEdges (faceMask F p)) :
    (Budget.base F).Adj (place p e.1) (place p e.2) := by
  obtain ⟨mem,hit⟩ := List.mem_filter.mp he
  refine ⟨lay p mem,?_⟩
  have loc (x : V) (m : marked (faceMask F p) x) (r : rim x) : place p x∈skeleton F := by
    have t : ∀ x : V, rim x=true → (cell x).1.val%3=0 ∨ (cell x).2.val%3=0 := by decide
    refine mem_filter.mpr ⟨of_decide_eq_true m,?_⟩
    simpa [place,coord,Nat.mul_comm] using t x r
  rcases Bool.or_eq_true_iff.mp hit with h|h
  · exact .inl (loc _ (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2)
  · exact .inr (loc _ (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2)

private theorem extra_adj {e} (he : e∈newEdges (faceMask F p)) :
    (Budget.G F).Adj (place p e.1) (place p e.2) := by
  obtain ⟨mem,hit⟩ := List.mem_filter.mp he
  exact ⟨lay p mem,(Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp hit).1).imp of_decide_eq_true of_decide_eq_true⟩

private theorem wires_sound {α : Type*} (f : Site k → α)
    (old : ∀ {x y}, (Budget.base F).Reachable x y → f x=f y) :
    ∀ x y : V, (pre (faceMask F p) (faceAtom F p).2)[x]=(pre (faceMask F p) (faceAtom F p).2)[y] →
      f (place p x)=f (place p y) := by
  apply fold_sound
  · apply fold_sound
    · intro x y h; simp [initial] at h; rw [h]
    · intro e he; exact old (old_adj F p he).reachable
  · intro e he
    obtain ⟨⟨c,d⟩,h,rfl⟩ := List.mem_map.mp he
    rw [cv_eq,cv_eq]
    exact old (of_decide_eq_true (List.mem_filter.mp h).2)

private theorem before_pre (c d : Corner) :
    before F (corner p c)=before F (corner p d) →
    (pre (faceMask F p) (faceAtom F p).2)[cv c]=(pre (faceMask F p) (faceAtom F p).2)[cv d] := by
  intro eq
  have a := old_reach_stop F (corner p c)
  have b := old_reach_stop F (corner p d)
  rw [eq] at a
  have w : (faceAtom F p).2 c d := decide_eq_true (a.trans b.symm)
  apply fold_edge (e:=(cv c,cv d))
  have all : ∀ a b : Corner, (a,b)∈cpairs := by decide +kernel
  exact List.mem_map.mpr ⟨(c,d),List.mem_filter.mpr ⟨all c d,w⟩,rfl⟩

private theorem image_le {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (h : ∀ a b, g a=g b → f a=f b) :
    (univ.image f).card ≤ (univ.image g).card := by
  classical
  let pick (y : ↑(univ.image g)) := (mem_image.mp y.2).choose
  have hp y : g (pick y)=(y:γ) := (mem_image.mp y.2).choose_spec.2
  have all : univ.image f ⊆ univ.image (fun y : ↑(univ.image g) => f (pick y)) := by
    intro x hx; obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    let y : ↑(univ.image g) := ⟨g a,mem_image_of_mem _ (mem_univ _)⟩
    exact mem_image.mpr ⟨y,mem_univ _,h _ _ (hp y)⟩
  exact (card_le_card all).trans (by simpa using (card_image_le (f:=fun y : ↑(univ.image g) => f (pick y)) (s:=univ)))

theorem joins_le_charges (acy : (Budget.G F).IsAcyclic) :
    joins (faceMask F p) (faceAtom F p).2 ≤ (charges F p).card := by
  classical
  let B := fun c => before F (corner p c)
  let A := fun c => after F p (corner p c)
  have low := image_le (fun c => (pre (faceMask F p) (faceAtom F p).2)[cv c]) B (before_pre F p)
  have high := image_le A (fun c => (post (faceMask F p) (faceAtom F p).2)[cv c]) (by
    have h := fold_sound (after F p ∘ place p) (newEdges (faceMask F p))
      (pre (faceMask F p) (faceAtom F p).2)
      (wires_sound F p _ (after_eq F p acy))
      (fun e he => after_edge F p acy (place_box ..) (place_box ..) (extra_adj F p he))
    intro c d eq; simpa [A,cv_eq,Function.comp_def] using h (cv c) (cv d) eq)
  have sub : univ.image B ⊆ univ.image A ∪ charges F p := by
    intro x hx; obtain ⟨c,_,rfl⟩ := mem_image.mp hx
    by_cases h : B c∈charges F p
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_image.mpr ⟨c,mem_univ _,unchanged F p acy (corner_joint p c) h⟩)
  have bound := (card_le_card sub).trans (card_union_le _ _)
  unfold joins colors; omega

end GridGraphs.NoPitch.FaceJoin
