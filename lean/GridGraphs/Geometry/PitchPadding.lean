import GridGraphs.Geometry.PhysicalCapTrace

namespace GridGraphs.PitchCut
open SimpleGraph Finset GridGraphs.CapBill
variable {k : Nat} (v : Fin (N k)) (up : Bool)

def height := if up then v.val else N k-1-v.val
abbrev Rect := Cell (k+1) (height v up)
def inner (z : Rect v up) := z.1.val≤height v up ∧ 0<z.2.val ∧ z.2.val≤N k
def onSide (x : Site k) := if up then x.1.val≤v.val else v.val≤x.1.val
instance (z : Rect v up) : Decidable (inner v up z) := by unfold inner; infer_instance
instance (x : Site k) : Decidable (onSide v up x) := by unfold onSide; infer_instance

def project (z : Rect v up) : Site k :=
  (⟨if up then v.val-z.1.val else min (N k-1) (v.val+z.1.val),by
      have := v.isLt; split_ifs <;> omega⟩,
   ⟨min (N k-1) (z.2.val-1),by have := v.isLt; omega⟩)

def embed (x : Site k) : Rect v up :=
  (⟨min (height v up) (if up then v.val-x.1.val else x.1.val-v.val),by omega⟩,
   ⟨x.2.val+1,by have := x.2.isLt; unfold N at *; omega⟩)

theorem embed_inner (x : Site k) : inner v up (embed v up x) := by
  have := x.2.isLt; dsimp [inner,embed]; omega
theorem project_side (z : Rect v up) : onSide v up (project v up z) := by
  have hv : v.val<3*k+1 := v.isLt
  cases up <;> dsimp [onSide,project,N] <;> omega
theorem recover_inner (z : Rect v up) (core : inner v up z) : embed v up (project v up z)=z := by
  have hv : v.val<3*k+1 := v.isLt; unfold inner at core
  apply Prod.ext <;> apply Fin.ext <;> cases up <;> dsimp [embed,project,height,N] at * <;> omega
theorem recover_side (x : Site k) (side : onSide v up x) : project v up (embed v up x)=x := by
  have := x.1.isLt; have := x.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> cases up <;> simp [embed,project,height,onSide] at * <;> omega

def mask (F : Finset (Site k)) := univ.filter (fun z : Rect v up => inner v up z ∧ project v up z∈F)
@[simp] theorem mask_mem (F : Finset (Site k)) (z : Rect v up) :
    z∈mask v up F ↔ inner v up z ∧ project v up z∈F := by simp [mask]

theorem grid_adj_coords {m n : Nat} (x y : GridVertex m n) :
    (gridGraph m n).Adj x y ↔
      (x.1.val=y.1.val ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val)) ∨
      (x.2.val=y.2.val ∧ (x.1.val+1=y.1.val ∨ y.1.val+1=x.1.val)) := by
  simp [gridGraph,adjacent,Fin.ext_iff]

theorem inside_adj (x y : Rect v up) (cx : inner v up x) (cy : inner v up y) :
    (board (k+1) (height v up)).Adj x y ↔ (gridGraph (N k) (N k)).Adj (project v up x) (project v up y) := by
  rw [grid_adj_coords,grid_adj_coords]
  have := v.isLt
  cases up <;> simp only [inner,height,project,if_true,Bool.false_eq_true,if_false] at * <;> omega

theorem project_bond {F : Finset (Site k)} {x y : Rect v up} (e : (bonds (mask v up F)).Adj x y) :
    project v up x=project v up y ∨
      (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).Adj (project v up x) (project v up y) := by
  by_cases both : inner v up x ∧ inner v up y
  · exact Or.inr ⟨(inside_adj v up _ _ both.1 both.2).mp e.1,
      e.2.elim (fun hx => Or.inl ((mask_mem ..).mp hx).2) (fun hy => Or.inr ((mask_mem ..).mp hy).2)⟩
  · left
    have member : inner v up x ∨ inner v up y := e.2.imp
      (fun hx => ((mask_mem ..).mp hx).1) (fun hy => ((mask_mem ..).mp hy).1)
    have adj := (grid_adj_coords ..).mp e.1
    have xb := x.1.isLt; have yb := y.1.isLt; have := v.isLt
    apply Prod.ext <;> apply Fin.ext <;> cases up <;> dsimp [inner,project,height,N] at * <;> omega

/-- A vertex of a cycle has two distinct neighbors on it, so padding
with vertices of degree at most one cannot create a cycle. -/
private theorem forest_pad {V W : Type*} {H : SimpleGraph V} {T : SimpleGraph W}
    (tree : T.IsAcyclic) (core : Set V) (f : V → W) (inj : Set.InjOn f core)
    (edge : ∀ ⦃x y⦄, H.Adj x y → x∈core → y∈core → T.Adj (f x) (f y))
    (leaf : ∀ x∉core, ∀ ⦃y z⦄, H.Adj x y → H.Adj x z → y=z) : H.IsAcyclic := by
  classical
  intro a w cyc
  have all (x) (hx : x∈w.support) : x∈core := by
    by_contra missing
    let d := w.rotate x hx
    have cd : d.IsCycle := cyc.rotate _
    exact cd.snd_ne_penultimate (leaf _ missing (d.adj_snd cd.not_nil) (d.adj_penultimate cd.not_nil).symm)
  let hom : H.induce core →g T :=
    ⟨fun z => f z.val,fun {a b} e => edge e a.property b.property⟩
  have embedded : (H.induce core).IsAcyclic :=
    tree.comap hom (fun x y eq => Subtype.ext (inj x.property y.property eq))
  have cycle : (w.induce core all).IsCycle := Walk.IsCycle.of_map (f:=(Embedding.induce core).toHom)
    (by simpa using cyc)
  exact embedded _ cycle

theorem mask_forest {F : Finset (Site k)}
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic) :
    (bonds (mask v up F)).IsAcyclic := by
  apply forest_pad acy {z | inner v up z} (project v up)
  · intro x hx y hy eq; rw [←recover_inner v up x hx,←recover_inner v up y hy,eq]
  · intro x y e hx hy
    exact ⟨(inside_adj v up _ _ hx hy).mp e.1,e.2.imp
      (fun m => ((mask_mem ..).mp m).2) (fun m => ((mask_mem ..).mp m).2)⟩
  · intro x outside y z ey ez
    change ¬inner v up x at outside
    have cy := ((mask_mem ..).mp (ey.2.resolve_left (fun m => outside ((mask_mem ..).mp m).1))).1
    have cz := ((mask_mem ..).mp (ez.2.resolve_left (fun m => outside ((mask_mem ..).mp m).1))).1
    have hy := (grid_adj_coords ..).mp ey.1
    have hz := (grid_adj_coords ..).mp ez.1
    unfold inner at outside cy cz
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem pad_mask {F : Finset (Site k)} (pitch : Pitch F v)
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic) :
    Padded (mask v up F) := by
  have topProj {z : Rect v up} (zero : z.1.val=0) : (project v up z).1=v := by
    have hv : v.val<3*k+1 := v.isLt
    apply Fin.ext; cases up <;> simp [project,zero,N]; omega
  have topRow : (mask v up F).filter (fun z => z.1.val=0) =
      univ.image (tooth (r:=k+1) (h:=height v up)) := by
    ext z; simp only [mem_filter,mask_mem,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨⟨core,mark⟩,zero⟩
      have p : project v up z∈rowTeeth k v := pitch ▸ mem_filter.mpr ⟨mark,topProj zero⟩
      obtain ⟨i,_,eq⟩ := mem_image.mp p
      have cx := congrArg (fun w : Site k => w.2.val) eq
      refine ⟨i,Prod.ext (Fin.ext zero.symm) (Fin.ext ?_)⟩
      unfold inner N at core; change 3*i.val=min (3*k+1-1) (z.2.val-1) at cx
      change 3*i.val+1=z.2.val; omega
    · rintro ⟨i,rfl⟩
      have e : project v up (tooth i)=(v,teeth k i) := by
        refine Prod.ext (topProj rfl) (Fin.ext ?_)
        change min (3*k+1-1) (3*i.val+1-1)=3*i.val
        have := i.isLt; omega
      have mem : (v,teeth k i)∈rowTeeth k v := mem_image_of_mem _ (mem_univ _)
      rw [←pitch] at mem
      refine ⟨⟨?_,e ▸ (mem_filter.mp mem).1⟩,rfl⟩
      unfold inner tooth N; dsimp; have := i.isLt; omega
  constructor
  · intro z m
    have a := ((mask_mem ..).mp m).1; unfold inner N at a; omega
  · intro z m
    have a := ((mask_mem ..).mp m).1.1; omega
  · intro z m zero
    have mem : z∈(mask v up F).filter (fun w => w.1.val=0) := mem_filter.mpr ⟨m,zero⟩
    rw [topRow] at mem
    obtain ⟨i,_,rfl⟩ := mem_image.mp mem
    dsimp [tooth]; omega
  · rw [topRow,card_image_of_injective]
    · simp
    · intro i j eq; apply Fin.ext
      have := congrArg (fun z : Rect v up => z.2.val) eq; dsimp [tooth] at this; omega
  · exact mask_forest v up acy

end GridGraphs.PitchCut
