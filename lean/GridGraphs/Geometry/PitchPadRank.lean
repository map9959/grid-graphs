import GridGraphs.Geometry.PitchPadding

namespace GridGraphs.PitchCut
open SimpleGraph Finset GridGraphs.CapBill

private theorem reach_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W)
    (edge : ∀ ⦃x y⦄, G.Adj x y → H.Reachable (f x) (f y)) {x y} (hr : G.Reachable x y) :
    H.Reachable (f x) (f y) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons e _ ih => exact (edge e).trans ih

private theorem image_compare {I A B : Type*} [Fintype I] [DecidableEq A] [DecidableEq B]
    (f : I→A) (g : I→B) (h : ∀ i j, f i=f j → g i=g j) :
    (univ.image g).card ≤ (univ.image f).card := by
  classical
  by_cases empty : IsEmpty I
  · let _ := empty; simp
  let _ : Nonempty I := not_isEmpty_iff.mp empty
  let choose (a : A) := if p : ∃ i, f i=a then p.choose else Classical.arbitrary I
  have rep (i : I) : g (choose (f i))=g i := by
    let p : ∃ j, f j=f i := ⟨i,rfl⟩
    simp only [choose,dif_pos p]; exact h _ _ p.choose_spec
  have eq : (univ.image f).image (fun a => g (choose a))=univ.image g := by
    rw [image_image]; change univ.image (fun i => g (choose (f i)))=_
    simp only [rep]
  rw [←eq]; exact card_image_le

private theorem rank_congr {I V W : Type*} [Fintype I] (G : SimpleGraph V) (H : SimpleGraph W)
    (a : I→V) (b : I→W) (eq : ∀ i j, G.Reachable (a i) (a j) ↔ H.Reachable (b i) (b j)) :
    rank G a = rank H b := by
  classical
  have le := image_compare (fun i => G.connectedComponentMk (a i)) (fun i => H.connectedComponentMk (b i))
    (fun i j e => ConnectedComponent.sound ((eq i j).mp (ConnectedComponent.exact e)))
  have ge := image_compare (fun i => H.connectedComponentMk (b i)) (fun i => G.connectedComponentMk (a i))
    (fun i j e => ConnectedComponent.sound ((eq i j).mpr (ConnectedComponent.exact e)))
  unfold rank classes; rw [le_antisymm ge le]

variable {k : Nat} (F : Finset (Site k)) (v : Fin (N k))
def inclusive (up : Bool) := confined
  (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)) (onSide v up)

private theorem proj_tooth (up : Bool) (i : Fin (k+1)) :
    project v up (tooth i) = (v,teeth k i) := by
  have vi := v.isLt; have ti := i.isLt
  apply Prod.ext
  · apply Fin.ext; cases up <;> dsimp [project,N,tooth] at *; omega
  · apply Fin.ext; change min (3*k+1-1) (3*i.val+1-1)=3*i.val; omega

theorem inclusive_rank (up : Bool) : rank (bonds (mask v up F)) tooth =
    rank (inclusive F v up) (fun i => (v,teeth k i)) := by
  apply rank_congr
  intro i j; constructor
  · intro p
    have map {x y} (e : (bonds (mask v up F)).Adj x y) :
        (inclusive F v up).Reachable (project v up x) (project v up y) := by
      rcases project_bond v up e with eq|edge
      · rw [eq]
      · exact (show (inclusive F v up).Adj _ _ from
            ⟨edge,project_side v up _,project_side v up _⟩).reachable
    simpa only [proj_tooth] using reach_map (project v up) (@map) p
  · intro p
    have map {x y} (e : (inclusive F v up).Adj x y) :
        (bonds (mask v up F)).Reachable (embed v up x) (embed v up y) := by
      have a := recover_side v up x e.2.1
      have b := recover_side v up y e.2.2
      apply Adj.reachable
      refine ⟨(inside_adj _ _ _ _ (embed_inner ..) (embed_inner ..)).mpr (by rw [a,b]; exact e.1.1),?_⟩
      simp only [Finset.mem_coe,mask_mem,embed_inner,true_and,a,b]
      exact e.1.2
    have emb (i : Fin (k+1)) : embed v up (v,teeth k i)=tooth i := by
      rw [←proj_tooth v up i]
      apply recover_inner
      unfold inner tooth N; dsimp; have := i.isLt; omega
    simpa only [emb] using reach_map (embed v up) (@map) p

def nearest (c : Fin (N k)) : Fin (k+1) :=
  ⟨(c.val+1)/3,by have := c.isLt; unfold N at *; omega⟩

private theorem on_pitch {c : Fin (N k)} (pitch : Pitch F v) :
    (v,c) ∈ F ↔ c=teeth k (nearest c) := by
  constructor
  · intro m
    have h : (v,c)∈rowTeeth k v := pitch ▸ mem_filter.mpr ⟨m,rfl⟩
    obtain ⟨i,_,e⟩ := mem_image.mp h
    have col := congrArg (fun z : Site k => z.2.val) e
    change 3*i.val=c.val at col
    apply Fin.ext; change c.val=3*((c.val+1)/3); omega
  · intro eq
    have h : (v,teeth k (nearest c)) ∈ rowTeeth k v := mem_image_of_mem _ (mem_univ _)
    rw [←pitch] at h
    exact eq.symm ▸ (mem_filter.mp h).1

private theorem spoke_only {u : Fin (N k)} (next : u.val+1=v.val)
    (pitch : Pitch F v) (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (c : Fin (N k)) (mark : (u,c)∈F ∨ (v,c)∈F) : c=teeth k (nearest c) := by
  rcases mark with m|m
  · by_contra ne
    let d := teeth k (nearest c)
    have gap : c.val+1=d.val ∨ d.val+1=c.val := by
      have diff : c.val≠3*((c.val+1)/3) := fun e => ne (Fin.ext e)
      change c.val+1=3*((c.val+1)/3) ∨ 3*((c.val+1)/3)+1=c.val
      omega
    have diag : (v,d)∈F := by
      have h : (v,d)∈rowTeeth k v := mem_image_of_mem _ (mem_univ _)
      rw [←pitch] at h; exact (mem_filter.mp h).1
    let G := gridGraph (N k) (N k)
    have a : G.Adj (u,c) (v,c) := Or.inr ⟨rfl,Or.inl next⟩
    have b : G.Adj (v,c) (v,d) := Or.inl ⟨rfl,gap⟩
    have e : G.Adj (v,d) (u,d) := Or.inr ⟨rfl,Or.inr next⟩
    have f : G.Adj (u,d) (u,c) := Or.inl ⟨rfl,gap.symm⟩
    have uv : u≠v := by rintro rfl; omega
    have := fourCycle_has_unforced_edge a b e f (fun eq => uv (Prod.mk.inj eq).1)
      (fun eq => uv (Prod.mk.inj eq).1.symm) acy
    tauto
  · exact (on_pitch F v pitch).mp m

theorem upper_rank (u : Fin (N k)) (next : u.val+1=v.val) (pitch : Pitch F v)
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic) :
    rank (inclusive F v true) (fun i => (v,teeth k i)) =
    rank (aboveCap F v) (fun i => (u,teeth k i)) := by
  let fold (x : Site k) : Site k := if x.1=v then (u,teeth k (nearest x.2)) else x
  have same (i : Fin (k+1)) : nearest (teeth k i)=i := Fin.ext (by
    change (3*i.val+1)/3=i.val; omega)
  have toothEdge (i : Fin (k+1)) : (inclusive F v true).Adj (v,teeth k i) (u,teeth k i) := by
    refine ⟨⟨Or.inr ⟨rfl,Or.inr next⟩,Or.inl ((on_pitch F v pitch).mpr (by rw [same]))⟩,?_,?_⟩ <;>
      simp [onSide]; omega
  apply rank_congr; intro i j
  constructor
  · intro p
    have map {x y : Site k} (e : (inclusive F v true).Adj x y) :
        (aboveCap F v).Reachable (fold x) (fold y) := by
      have sx : x.1.val≤v.val := e.2.1
      have sy : y.1.val≤v.val := e.2.2
      by_cases hx : x.1=v <;> by_cases hy : y.1=v
      · have adj := (grid_adj_coords ..).mp e.1.1
        have m := e.1.2
        have hm : x.2=teeth k (nearest x.2) ∨ y.2=teeth k (nearest y.2) := by
          rcases m with mx|my
          · exact Or.inl ((on_pitch F v pitch).mp (by rw [←hx]; exact mx))
          · exact Or.inr ((on_pitch F v pitch).mp (by rw [←hy]; exact my))
        have eq : nearest x.2=nearest y.2 := by
          apply Fin.ext
          simp only [hx,hy] at adj
          change (x.2.val+1)/3=(y.2.val+1)/3
          rcases hm with m|m
          · have e := congrArg Fin.val m
            change x.2.val=3*((x.2.val+1)/3) at e; omega
          · have e := congrArg Fin.val m
            change y.2.val=3*((y.2.val+1)/3) at e; omega
        simp [fold,hx,hy,eq]
      · have adj := (grid_adj_coords ..).mp e.1.1
        have yn : y.1.val≠v.val := fun eq => hy (Fin.ext eq)
        have xy : x.2=y.2 := Fin.ext (by rw [hx] at adj; omega)
        have row : y.1=u := Fin.ext (by rw [hx] at adj; omega)
        have wx : x=(v,x.2) := Prod.ext hx rfl
        have wy : y=(u,x.2) := Prod.ext row xy.symm
        have mark : (u,x.2)∈F ∨ (v,x.2)∈F := e.1.2.symm.imp (wy ▸ ·) (wx ▸ ·)
        have col := spoke_only F v next pitch acy _ mark
        simp only [fold,if_pos hx,if_neg hy,←col,←wy]; rfl
      · have adj := (grid_adj_coords ..).mp e.1.1
        have xn : x.1.val≠v.val := fun eq => hx (Fin.ext eq)
        have xy : x.2=y.2 := Fin.ext (by rw [hy] at adj; omega)
        have row : x.1=u := Fin.ext (by rw [hy] at adj; omega)
        have wx : x=(u,y.2) := Prod.ext row xy
        have wy : y=(v,y.2) := Prod.ext hy rfl
        have mark : (u,y.2)∈F ∨ (v,y.2)∈F := e.1.2.imp (wx ▸ ·) (wy ▸ ·)
        have col := spoke_only F v next pitch acy _ mark
        simp only [fold,if_neg hx,if_pos hy,←col,←wx]; rfl
      · simp only [fold,if_neg hx,if_neg hy]
        exact (show (aboveCap F v).Adj x y from ⟨e.1,
          lt_of_le_of_ne sx (fun eq => hx (Fin.ext eq)),
          lt_of_le_of_ne sy (fun eq => hy (Fin.ext eq))⟩).reachable
    simpa [fold,same] using reach_map fold (@map) p
  · intro p
    have sub : aboveCap F v ≤ inclusive F v true := by
      intro x y e; exact ⟨e.1,e.2.1.le,e.2.2.le⟩
    exact (toothEdge i).reachable.trans ((p.mono sub).trans (toothEdge j).symm.reachable)

end GridGraphs.PitchCut
