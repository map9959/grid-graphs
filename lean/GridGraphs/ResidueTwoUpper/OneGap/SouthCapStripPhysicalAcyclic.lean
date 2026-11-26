import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPhysicalReadout

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph ResidueZero L7 Camera FanSeed BoundarySix.Connected
namespace GridScan

/-- Isolated dummy and off-range indices may map anywhere. Injectivity
is needed only on endpoints of actual graph edges. -/
theorem acyclic_of_active_hom {X Y : Type} {G : SimpleGraph X} {W : SimpleGraph Y}
    (f : G →g W) (acy : W.IsAcyclic)
    (inj : ∀ x y, (∃ b, G.Adj x b) → (∃ b, G.Adj y b) → f x=f y → x=y) :
    G.IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro a b e
  apply isBridge_iff.mpr
  intro r
  let lift : G.deleteEdges {s(a,b)} →g W.deleteEdges {s(f a,f b)} :=
    ⟨f,by
      intro x y e'
      simp only [deleteEdges_adj,Set.mem_singleton_iff] at e' ⊢
      refine ⟨f.map_rel' e'.1,?_⟩
      intro eq
      apply e'.2
      apply Sym2.eq_iff.mpr
      rcases Sym2.eq_iff.mp eq with ⟨l,r⟩|⟨l,r⟩
      · exact .inl ⟨inj x a ⟨y,e'.1⟩ ⟨b,e⟩ l,inj y b ⟨x,e'.1.symm⟩ ⟨a,e.symm⟩ r⟩
      · exact .inr ⟨inj x b ⟨y,e'.1⟩ ⟨a,e.symm⟩ l,inj y a ⟨x,e'.1.symm⟩ ⟨b,e⟩ r⟩⟩
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp acy (f.map_rel' e))) (r.map lift)

def boxedPoint {u h : Nat} (s : Window h (width h)) (v : View)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43) (j : Nat) (i : Fin (3*s.depth))
    (jl : j<3*s.length) : (prefixBox s (11+14*u) (3*s.length)).vertices (n:=35+42*u) v := by
  let B := prefixBox s (11+14*u) (3*s.length)
  let p := scanPoint B s.axis j i
  let x := point u v p
  have eq : coordinates v x=p := coords_point (scanPoint_board s hk lo hi le_rfl jl i.isLt)
  refine ⟨x,?_⟩
  change B.Contains (coordinates v x)
  rw [eq]
  exact (scanPoint_contains s _ _ j i).mpr ⟨jl,i.isLt⟩

theorem boxedPoint_coords {u h : Nat} (s : Window h (width h)) (v : View)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43) (j : Nat) (i : Fin (3*s.depth))
    (jl : j<3*s.length) :
    coordinates v (boxedPoint s v hk lo hi j i jl).val =
      scanPoint (prefixBox s (11+14*u) (3*s.length)) s.axis j i :=
  coords_point (scanPoint_board s hk lo hi le_rfl jl i.isLt)

def physicalInterior {u h : Nat} (s : Window h (width h)) (v : View)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43) (j : Nat) (i : Fin (3*s.depth))
    (jl : j<3*s.length) : Interior (35+42*u) :=
  let a := boxedPoint s v hk lo hi j i jl
  ⟨a.val,prefix_site_interior v s hk lo hi _ le_rfl a⟩

def physicalImage {u h : Nat} (s : Window h (width h)) (v : View)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43) : Vertex (3*s.depth) → Option (Interior (35+42*u))
  | none | some (0,_) => none
  | some (j+1,i) => if jl : j<3*s.length then some (physicalInterior s v hk lo hi j i jl) else none

theorem active_physicalImage {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (x y : Vertex (3*s.depth))
    (ax : ∃ b, (graph (physicalProgram s F v north) (3*s.length)).Adj x b)
    (ay : ∃ b, (graph (physicalProgram s F v north) (3*s.length)).Adj y b)
    (eq : physicalImage s v hk lo hi x=physicalImage s v hk lo hi y) : x=y := by
  have active (z : Vertex (3*s.depth)) (a : ∃ b, (graph (physicalProgram s F v north) (3*s.length)).Adj z b) :
      z=none ∨ ∃ (j : Nat) (i : Fin (3*s.depth)), j<3*s.length ∧ z=site (j+1) i := by
    cases z with
    | none => exact .inl rfl
    | some z =>
      obtain ⟨b,e⟩ := a
      obtain ⟨j,i⟩ := z
      have bound : 0<j ∧ j≤3*s.length := by
        cases b with
        | none => exact ⟨((graph_adj_root ..).mp e).1,((graph_adj_root ..).mp e).2.1⟩
        | some t => exact ⟨((graph_adj_sites ..).mp e).1,((graph_adj_sites ..).mp e).2.1⟩
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
      exact .inr ⟨k,i,by omega,rfl⟩
  rcases active x ax with rfl|⟨j,i,jl,rfl⟩ <;> rcases active y ay with rfl|⟨k,b,kl,rfl⟩
  · rfl
  · simp [site,physicalImage,kl] at eq
  · simp [site,physicalImage,jl] at eq
  · simp only [site,physicalImage,dif_pos jl,dif_pos kl,Option.some.injEq] at eq
    have pt := congrArg (fun a : Interior (35+42*u) => coordinates v a.val) eq
    change coordinates v (boxedPoint s v hk lo hi j i jl).val =
      coordinates v (boxedPoint s v hk lo hi k b kl).val at pt
    rw [boxedPoint_coords,boxedPoint_coords] at pt
    have off := scanPoint_offsets s (11+14*u) (3*s.length) j i
    dsimp only at off
    rw [pt] at off
    have off' := scanPoint_offsets s (11+14*u) (3*s.length) k b
    dsimp only at off'
    have je : j=k := by omega
    have ie : i=b := Fin.ext (by omega)
    rw [je,ie]

private def Wired {u h : Nat} (s : Window h (width h)) (F : Finset (Site u)) (v : View)
    (x : Interior (35+42*u)) : Prop :=
  let B := prefixBox s (11+14*u) (3*s.length)
  x.val=railPoint u v (1+3*(11+14*u-1)) (firstRow (11+14*u) h+1) ∨
    (x.val∈B.vertices v ∧ x.val∈F ∧ EngineRimContact s
      (alongOffset s.axis B (coordinates v x.val)) (acrossOffset s.axis B (coordinates v x.val)))

/-- The exact generated graph is acyclic. Its lattice bonds embed into
the retained physical forest, while wire choices go to the one-gap
apex forest. Dummy indices carry no edges. -/
theorem physical_graph_acyclic {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (s : Window h (width h)) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : FanSlab.square F v (firstRow (11+14*u) h) (1+3*(11+14*u-1))=73) :
    (graph (physicalProgram s F v north) (3*s.length)).IsAcyclic := by
  classical
  let p := physicalProgram s F v north
  let B := prefixBox s (11+14*u) (3*s.length)
  let C := Finset.univ.filter (Wired s F v)
  let W := apexGraph (interiorGraph F) C
  have ac : W.IsAcyclic := axis_free_wired_acyclic H acy one s hk lo hi line top _ le_rfl C
    (fun x hx => (Finset.mem_filter.mp hx).2)
  let f := physicalImage s v hk lo hi
  have wire (j : Nat) (i : Fin (3*s.depth)) (jl : j<3*s.length)
      (m : p.mark j i=true) (t : p.tooth j i=true) :
      physicalInterior s v hk lo hi j i jl∈C := by
    let a := boxedPoint s v hk lo hi j i jl
    have mark : a.val∈F := (physical_program_mark s F v north hk lo hi j i jl).mp m
    have read : coordinates v a.val=scanPoint B s.axis j i := boxedPoint_coords s v hk lo hi j i jl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    dsimp only [Wired]
    change _ ∨ (a.val∈B.vertices v ∧ a.val∈F ∧ EngineRimContact s
      (alongOffset s.axis B (coordinates v a.val)) (acrossOffset s.axis B (coordinates v a.val)))
    simp only [p,physicalProgram,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at t
    rcases t with rim|⟨_,root⟩
    · right
      refine ⟨a.2,mark,?_⟩
      rw [read]
      have offsets := scanPoint_offsets s (11+14*u) (3*s.length) j i
      change alongOffset s.axis B (scanPoint B s.axis j i)=j ∧
        acrossOffset s.axis B (scanPoint B s.axis j i)=i.val at offsets
      rwa [offsets.1,offsets.2]
    · left
      change a.val=_
      apply point_inj v
      rw [read,railPoint_coords (by omega : 1+3*(11+14*u-1)<35+42*u)
        (by unfold firstRow; omega : firstRow (11+14*u) h+1<35+42*u)]
      simpa [Nat.cast_add] using root
  let map : graph p (3*s.length) →g W := ⟨f,by
    intro a b e
    cases a with
    | none =>
      cases b with
      | none => exact (e.ne rfl).elim
      | some z =>
        obtain ⟨j,i⟩ := z
        obtain ⟨lo',hi',m,t⟩ := (graph_adj_root p _ j i).mp e.symm
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
        have kl : k<3*s.length := by omega
        simpa [f,physicalImage,kl,W,apexGraph] using wire k i kl m t
    | some z =>
      obtain ⟨j,i⟩ := z
      cases b with
      | none =>
        obtain ⟨lo',hi',m,t⟩ := (graph_adj_root p _ j i).mp e
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
        have kl : k<3*s.length := by omega
        simpa [f,physicalImage,kl,W,apexGraph] using wire k i kl m t
      | some z =>
        obtain ⟨k,b⟩ := z
        obtain ⟨ja,jb,ka,kb,near,marks⟩ := (graph_adj_sites p _ j k i b).mp e
        obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
        obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
        have rl : r<3*s.length := by omega
        have cl : c<3*s.length := by omega
        let x := boxedPoint s v hk lo hi r i rl
        let y := boxedPoint s v hk lo hi c b cl
        have ee : (Bonds F).Adj x.val y.val := by
          constructor
          · rw [Camera.adj_iff v,boxedPoint_coords,boxedPoint_coords]
            have metric := (lattice_metric _ _ _ _).mp near
            cases ax : s.axis <;> simpa [scanPoint,ax,abs_sub_comm,add_comm] using metric
          · exact marks.imp (physical_program_mark s F v north hk lo hi r i rl).mp
              (physical_program_mark s F v north hk lo hi c b cl).mp
        simpa [f,physicalImage,physicalInterior,rl,cl,W,apexGraph,x,y] using ee⟩
  exact acyclic_of_active_hom map ac (active_physicalImage s F v north hk lo hi)

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
