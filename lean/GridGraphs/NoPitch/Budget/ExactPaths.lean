import GridGraphs.NoPitch.Budget.JunctionRank

namespace GridGraphs.NoPitch.Budget
open SimpleGraph Finset PitchCut
open scoped Sym2
variable {k : Nat}

private theorem radial {x y : Site k} (j : isJoint y)
    (a : (gridGraph (N k) (N k)).Adj x y) : ¬isJoint x ∧ hub x=y := by
  have u : (hub x).1.val=3*((x.1.val+1)/3) := rfl
  have v : (hub x).2.val=3*((x.2.val+1)/3) := rfl
  change adjacent _ _ _ _ at a
  simp only [adjacent,Fin.ext_iff,isJoint,Prod.ext_iff] at *
  omega

private theorem unique_neighbor (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    {x y z : Site k} (hx : ¬isJoint x) (off : ¬(base F).Adj x (hub x))
    (hy : y∈skeleton F) (hz : z∈skeleton F)
    (ey : (base F).Adj x y) (ez : (base F).Adj x z) : y=z := by
  have ny : ¬isJoint y := fun h => off ((radial h ey.1).2.symm ▸ ey)
  have nz : ¬isJoint z := fun h => off ((radial h ez.1).2.symm ▸ ez)
  have ry := (mem_filter.mp hy).2; have rz := (mem_filter.mp hz).2
  have ay := ey.1; have az := ez.1
  change adjacent _ _ _ _ at ay az
  simp only [adjacent,Fin.ext_iff] at ay az
  have diag := CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy y z
    (mem_filter.mp hy).1 (mem_filter.mp hz).1
  simp only [isJoint,Prod.ext_iff,Fin.ext_iff] at *
  by_contra! bad
  have dr : y.1.val+1=z.1.val ∨ z.1.val+1=y.1.val := by omega
  have dc : y.2.val+1=z.2.val ∨ z.2.val+1=y.2.val := by omega
  exact diag dr dc

private theorem nonradial (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    {x y : Site k} (hx : ¬isJoint x) (e : (base F).Adj x y)
    (off : ¬(base F).Adj x (hub x)) : target F x=y := by
  classical
  have xm : x∉skeleton F := by
    intro m
    have u : (hub x).1.val=3*((x.1.val+1)/3) := rfl
    have v : (hub x).2.val=3*((x.2.val+1)/3) := rfl
    have rim := (mem_filter.mp m).2
    apply off; refine ⟨?_,.inl m⟩
    change adjacent _ _ _ _; simp only [adjacent,Fin.ext_iff]
    unfold isJoint at hx; omega
  have ym := e.2.resolve_left xm
  have h : ∃ z∈skeleton F, (base F).Adj x z := ⟨_,ym,e⟩
  unfold target
  simp only [if_neg off,dif_pos h]
  exact unique_neighbor F acy hx off h.choose_spec.1 ym h.choose_spec.2 e

private theorem radial_rim (F : Finset (Site k)) {x} (e : (base F).Adj x (hub x)) :
    onRim x := by
  have u : (hub x).1.val=3*((x.1.val+1)/3) := rfl
  have v : (hub x).2.val=3*((x.2.val+1)/3) := rfl
  have a := e.1; change adjacent _ _ _ _ at a
  simp only [adjacent,Fin.ext_iff] at a; unfold onRim; omega

private theorem horizontal {a b c : Fin (N k)} (row : a.val%3=0)
    (lx : b.val%3≠0) (rx : c.val%3≠0) (next : b.val+1=c.val) :
    ∃ s : Seg k, point s 1=(a,b) ∧ point s 2=(a,c) := by
  refine ⟨(false,owner a,⟨b.val/3,by have := c.isLt; unfold N at this; omega⟩),?_,?_⟩ <;>
    apply Prod.ext <;> apply Fin.ext
  all_goals first | change 3*((a.val+1)/3)=a.val; omega
                  | change 3*(b.val/3)+1=b.val; omega
                  | change 3*(b.val/3)+2=c.val; omega

private theorem segment_of_adj {x y : Site k} (nx : ¬isJoint x) (ny : ¬isJoint y)
    (rx : onRim x) (ry : onRim y) (a : (gridGraph (N k) (N k)).Adj x y) :
    ∃ s : Seg k, midEdge s=s(x,y) := by
  rcases x with ⟨u,b⟩; rcases y with ⟨v,c⟩
  change adjacent _ _ _ _ at a
  simp only [adjacent] at a
  unfold onRim isJoint at *
  dsimp only at *
  have hor {x y z : Fin (N k)} (r : x.val%3=0) (h : y.val+1=z.val)
      (p : y.val%3≠0) (q : z.val%3≠0) := horizontal r p q h
  rcases a with ⟨rfl,h|h⟩|⟨rfl,h|h⟩
  all_goals first
    | obtain ⟨s,A,B⟩ := hor (x:=u) (by omega) h (by omega) (by omega)
      refine ⟨s,?_⟩
      simp only [midEdge,A,B] <;> first | rfl | exact Sym2.eq_swap
    | obtain ⟨⟨d,i,j⟩,A,B⟩ := hor (x:=b) (by omega) h (by omega) (by omega)
      refine ⟨(!d,i,j),?_⟩
      have sw (t : Fin 4) : point (!d,i,j) t=(point (d,i,j) t).swap := by cases d <;> rfl
      simp only [midEdge,sw,A,B,Prod.swap_prod_mk] <;> first | rfl | exact Sym2.eq_swap

private theorem hub_points (s : Seg k) :
    hub (point s 1)=point s 0 ∧ hub (point s 2)=point s 3 := by
  have tooth (u : J k) : (teeth k u).val=3*u.val := rfl
  rcases s with ⟨b,i,j⟩
  cases b <;> simp [Prod.ext_iff,Fin.ext_iff,tooth,hub,point,coord,owner] <;> omega

theorem ledgerEdges_exact (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    ledgerEdges F=(base F).edgeFinset := by
  apply Subset.antisymm (ledgerEdges_sub F)
  intro z
  induction z using Sym2.inductionOn with | _ x y =>
    intro m
    have e := mem_edgeFinset.mp m
    change (base F).Adj x y at e
    have owned {p q : Site k} (a : (base F).Adj p q) (n : ¬isJoint p) (t : target F p=q) :
        s(p,q)∈ledgerEdges F := mem_union_left _ (mem_image.mpr
          ⟨p,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,.inr ⟨_,a⟩⟩,
            fun h => n (mem_filter.mp h).2⟩,congrArg (fun w => s(p,w)) t⟩)
    have radialOwn {p q : Site k} (a : (base F).Adj p q) (j : isJoint q) :
        s(p,q)∈ledgerEdges F := by
      obtain ⟨n,eq⟩ := radial j a.1
      exact owned a n (by simp [target,eq,a])
    by_cases nx : isJoint x
    · rw [Sym2.eq_swap]; exact radialOwn e.symm nx
    by_cases ny : isJoint y
    · exact radialOwn e ny
    by_cases a : (base F).Adj x (hub x)
    · by_cases b : (base F).Adj y (hub y)
      · obtain ⟨s,eq⟩ := segment_of_adj nx ny (radial_rim F a) (radial_rim F b) e.1
        refine mem_union_right _ (mem_image.mpr ⟨s,mem_filter.mpr ⟨mem_univ _,?_⟩,eq⟩)
        obtain ⟨h₁,h₂⟩ := hub_points s
        rcases Sym2.eq_iff.mp eq with ⟨l,r⟩|⟨r,l⟩
        · rw [←l] at a; rw [←r] at b; rw [h₁] at a; rw [h₂] at b
          exact ⟨a.symm,l ▸ r ▸ e,b⟩
        · rw [←l] at a; rw [←r] at b; rw [h₂] at a; rw [h₁] at b
          exact ⟨b.symm,l ▸ r ▸ e.symm,a⟩
      · rw [Sym2.eq_swap]; exact owned e.symm ny (nonradial F acy ny e.symm b)
    · exact owned e nx (nonradial F acy nx e a)

theorem physical_paths_sinks_exits (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    axisPaths F + axisPaths (trans F) + (sinks F).card + (exits F).card = ((k:Int)+1)^2 := by
  have b := ledgerEdges_count F; rw [ledgerEdges_exact F acy] at b
  have h := exits_euler F acy
  have sub : joints k ⊆ oldSites F := fun x j => mem_filter.mpr ⟨mem_univ _,.inl j⟩
  have z := card_sdiff_add_card_eq_card sub
  rw [joints_card] at z
  rw [paths_eq]; exact_mod_cast (show (liveSegs F).card+(sinks F).card+(exits F).card=(k+1)^2 by omega)

end GridGraphs.NoPitch.Budget
