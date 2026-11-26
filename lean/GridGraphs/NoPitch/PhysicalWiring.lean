import GridGraphs.NoPitch.WiredFace

namespace GridGraphs.NoPitch.Wired
open SimpleGraph PitchCut Finset

variable {W : Type*} (f : V → W)
def Sound (H : SimpleGraph W) (s : Labels) :=
  ∀ x y : V, s[x]=s[y] → H.Reachable (f x) (f y)

private theorem sound_initial (H : SimpleGraph W) : Sound f H initial := by
  intro x y eq
  simp [initial] at eq; rw [eq]

private theorem sound_merge {H : SimpleGraph W} {s : Labels} {e : E} (h : Sound f H s)
    (r : H.Reachable (f e.1) (f e.2)) : Sound f H (merge s e) := by
  intro x y eq
  change (s.map _)[x.val]=(s.map _)[y.val] at eq
  simp only [Vector.getElem_map] at eq
  split at eq <;> split at eq
  · rename_i a b; exact h _ _ (a.trans b.symm)
  · rename_i a b; exact ((h _ _ a).trans r.symm).trans (h _ _ eq)
  · rename_i a b; exact ((h _ _ eq).trans r).trans (h _ _ b.symm)
  · exact h _ _ eq

private theorem sound_fold (H : SimpleGraph W) (l : List E) (s : Labels) (h : Sound f H s)
    (edges : ∀ e∈l, H.Reachable (f e.1) (f e.2)) : Sound f H (l.foldl merge s) := by
  induction l generalizing s with
  | nil => exact h
  | cons e l ih => exact ih _ (sound_merge f h (edges _ (by simp))) (fun d hd => edges d (by simp [hd]))

/-- A failed union would close a cycle in the actual forest: add the
other physical edges in list order, never using the edge under test. -/
theorem fresh_of_forest (inj : Function.Injective f) (T : SimpleGraph W) (acy : T.IsAcyclic)
    (l : List E) (unique : l.Nodup) (s : Labels) (H : SimpleGraph W)
    (le : H≤T) (h : Sound f H s)
    (edges : ∀ e∈l, e.1<e.2 ∧ T.Adj (f e.1) (f e.2) ∧ ¬H.Adj (f e.1) (f e.2)) :
    fresh s l := by
  induction l generalizing H s with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨ord,a,missing⟩ := edges e (by simp)
    let K := H ⊔ SimpleGraph.edge (f e.1) (f e.2)
    have kle : K≤T := sup_le le ((edge_le_iff T).mpr (Or.inr a))
    have ke : K.Adj (f e.1) (f e.2) := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,a.ne⟩)
    have ne : s[e.1]≠s[e.2] := by
      intro eq
      rcases (isAcyclic_sup_fromEdgeSet_iff.mp (acy.anti kle)).2 (h _ _ eq) with z|z
      · exact a.ne z
      · exact missing z
    have tail := List.nodup_cons.mp unique
    simp only [fresh,Bool.and_eq_true,bne_iff_ne]
    refine ⟨ne,ih tail.2 _ K kle (sound_merge f (fun x y eq => (h x y eq).mono le_sup_left)
      ke.reachable) ?_⟩
    intro d hd
    obtain ⟨o,b,absent⟩ := edges d (by simp [hd])
    refine ⟨o,b,?_⟩
    rintro (c|c)
    · exact absent c
    · rcases (edge_adj ..).mp c with ⟨⟨u,v⟩|⟨u,v⟩,_⟩
      · exact tail.1 (Prod.ext (inj u) (inj v) ▸ hd)
      · rw [inj u,inj v] at o; exact ord.asymm o

variable {k : Nat} (p : FacePos k)
def place (x : V) : Site k := (coord p.1 (cell x).1,coord p.2 (cell x).2)
private theorem coords_inj (x y : V) : cell x=cell y → x=y := by
  revert x y; decide +kernel
private theorem place_inj : Function.Injective (place p) := by
  intro x y eq; apply coords_inj
  have a := congrArg (fun w : Site k => w.1.val) eq
  have b := congrArg (fun w : Site k => w.2.val) eq
  dsimp only [place,coord] at a b
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private theorem layout : ∀ e∈es, e.1<e.2 ∧
    (gridGraph 4 4).Adj (cell e.1) (cell e.2) := by decide +kernel
private theorem unique_edges : es.Nodup := by decide +kernel
private theorem adj {e : E} (mem : e∈es) :
    (gridGraph (N k) (N k)).Adj (place p e.1) (place p e.2) := by
  have loc := (layout e mem).2
  change adjacent _ _ _ _ at loc ⊢
  unfold adjacent place coord at *
  simp only [Fin.ext_iff] at *
  omega

private theorem rim_iff (v : V) :
    rim v=true ↔ (place p v).1.val%3=0 ∨ (place p v).2.val%3=0 := by
  have res : ∀ x : V, rim x=true ↔ (cell x).1.val%3=0 ∨ (cell x).2.val%3=0 := by decide +kernel
  simpa [place,coord,Nat.mul_comm] using res v

abbrev G (F : Finset (Site k)) := forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)
private theorem mark_iff (F : Finset (Site k)) (v : V) :
    marked (faceMask F p) v=true ↔ place p v∈F := by simp [marked,faceMask,place]
private theorem old_iff (F : Finset (Site k)) (e : E) :
    old (faceMask F p) e=true ↔ place p e.1∈skeleton F ∨ place p e.2∈skeleton F := by
  simp only [old,Bool.or_eq_true,Bool.and_eq_true,mark_iff,rim_iff p,skeleton,mem_filter]
private theorem cv_place (c : Corner) : place p (cv c)=corner p c := by
  have h : ∀ c : Corner, cell (cv c)=(cornerOffset c.1,cornerOffset c.2) := by decide +kernel
  simp [place,h,corner]

theorem physical_wiring (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    let m := faceMask F p
    let q := (faceAtom F p).2
    fresh initial (rawEdges m) ∧ compatible m q := by
  classical
  let m := faceMask F p
  let q := (faceAtom F p).2
  let S := G (skeleton F)
  have sub : S≤G F := forcedEdgeGraph_mono _ (by intro x hx; exact (mem_filter.mp hx).1)
  have j (c d : Corner) : q c d=true ↔ S.Reachable (place p (cv c)) (place p (cv d)) := by
    simp [q,faceAtom,joined,cv_place,S]
  have be {e} (he : e∈baseEdges m) : S.Adj (place p e.1) (place p e.2) :=
    ⟨adj p (List.mem_filter.mp he).1,(old_iff ..).mp (List.mem_filter.mp he).2⟩
  have bs := sound_fold (place p) S (baseEdges m) initial (sound_initial (place p) S)
    (fun _ he => (be he).reachable)
  have raw : fresh initial (rawEdges m) := by
    apply fresh_of_forest _ (place_inj p) _ acy _ (unique_edges.filter _) initial ⊥ bot_le (sound_initial (place p) ⊥)
    intro e he
    obtain ⟨he,one⟩ := List.mem_filter.mp he
    exact ⟨(layout _ he).1,⟨adj p he,(Bool.or_eq_true_iff.mp one).imp ((mark_iff ..).mp) ((mark_iff ..).mp)⟩,
      by simp⟩
  refine ⟨raw,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_,?_⟩,?_⟩⟩
  · apply fresh_of_forest _ (place_inj p) _ acy _ (unique_edges.filter _) initial ⊥ bot_le (sound_initial (place p) ⊥)
    intro e he
    exact ⟨(layout _ (List.mem_filter.mp he).1).1,sub (be he),by simp⟩
  · apply List.all_eq_true.mpr
    intro ⟨c,d⟩ _
    by_cases e : (base m)[cv c]=(base m)[cv d]
    · exact Bool.or_eq_true_iff.mpr (.inr ((j c d).mpr (bs _ _ e)))
    · exact Bool.or_eq_true_iff.mpr (.inl (bne_iff_ne.mpr e))
  · apply fresh_of_forest _ (place_inj p) _ acy _ (unique_edges.filter _) _ S sub
    · apply sound_fold _ _ _ _ bs
      intro e he
      obtain ⟨⟨c,d⟩,mem,rfl⟩ := List.mem_map.mp he
      exact (j c d).mp (List.mem_filter.mp mem).2
    · intro e he
      obtain ⟨he,bits⟩ := List.mem_filter.mp he
      obtain ⟨one,no⟩ := Bool.and_eq_true_iff.mp bits
      refine ⟨(layout _ he).1,⟨adj p he,(Bool.or_eq_true_iff.mp one).imp ((mark_iff ..).mp) ((mark_iff ..).mp)⟩,?_⟩
      intro a
      have yes : old m e=true := (old_iff p F e).mpr a.2
      rw [yes] at no; contradiction

end GridGraphs.NoPitch.Wired
