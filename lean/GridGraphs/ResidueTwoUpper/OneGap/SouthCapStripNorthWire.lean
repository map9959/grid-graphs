import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripAttachment

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 FanSeed FanSlab Camera BoundarySix.Connected SimpleGraph

def railPoint (u : Nat) (v : View) (c r : Nat) : Site u :=
  point u v ((r:Int),(c:Int))

theorem railPoint_coords {u : Nat} {v : View} {c r : Nat}
    (cc : c<35+42*u) (rr : r<35+42*u) :
    coordinates v (railPoint u v c r)=((r:Int),(c:Int)) :=
  coords_point (by unfold Camera.In; dsimp; omega)

private theorem railPoint_inner {u : Nat} {v : View} {c r : Nat}
    (cl : 0<c) (cu : c+1<35+42*u) (rl : 0<r) (ru : r+1<35+42*u) :
    ¬IsGridBoundary (railPoint u v c r) := by
  rw [boundary_in_view v,railPoint_coords (by omega : c<35+42*u) (by omega : r<35+42*u)]
  dsimp
  omega

def railInner (u : Nat) (v : View) (c r : Nat) (cl : 0<c) (cu : c+1<35+42*u)
    (rl : 0<r) (ru : r+1<35+42*u) : Interior (35+42*u) :=
  ⟨railPoint u v c r,railPoint_inner cl cu rl ru⟩

theorem rail_edge {u c r : Nat} {F : Finset (Site u)} {v : View}
    (cc : c<35+42*u) (rr : r+1<35+42*u)
    (markedEdge : marked F (L7.view v (35+42*u:Nat) r c) ||
      marked F (L7.view v (35+42*u:Nat) (r+1:Nat) c)) :
    (Bonds F).Adj (railPoint u v c r) (railPoint u v c (r+1)) := by
  constructor
  · rw [Camera.adj_iff v,railPoint_coords cc (by omega : r<35+42*u),railPoint_coords cc rr]
    simp
  · have h₁ := railPoint_coords (v:=v) cc (by omega : r<35+42*u)
    have h₂ := railPoint_coords (v:=v) cc rr
    have e₁ := coords_view v (railPoint u v c r)
    have e₂ := coords_view v (railPoint u v c (r+1))
    rw [h₁] at e₁
    rw [h₂] at e₂
    rw [e₁,e₂,marked_at,marked_at,Bool.or_eq_true] at markedEdge
    exact markedEdge.imp of_decide_eq_true of_decide_eq_true

private theorem northRail_path {u c stop : Nat} {F : Finset (Site u)} {v : View}
    (cl : 0<c) (cu : c+1<35+42*u)
    (last : stop+2<35+42*u)
    (marks : ∀ r<stop+1, marked F (L7.view v (35+42*u:Nat) r c) ||
      marked F (L7.view v (35+42*u:Nat) (r+1:Nat) c)) :
    (interiorGraph F).Reachable (railInner u v c 1 cl cu (by decide) (by omega))
      (railInner u v c (stop+1) cl cu (by omega) (by omega)) := by
  induction stop with
  | zero => exact .rfl
  | succ k ih =>
    have prev := ih (by omega) (fun r hr => marks r (by omega))
    have e : (interiorGraph F).Adj
        (railInner u v c (k+1) cl cu (by omega) (by omega))
        (railInner u v c (k+2) cl cu (by omega) (by omega)) :=
      rail_edge (by omega) (by omega) (marks (k+1) (by omega))
    exact prev.trans e.reachable

/-- The extra north contact is attached to an actual perimeter vertex
by the retained `RootLine`, extended by one edge at the marked foot.
It is not justified merely by the outgoing arrow at the cut. -/
def north_attachment {u c stop : Nat} {F : Finset (Site u)} {v : View}
    (cl : 0<c) (cu : c+1<35+42*u)
    (last : stop+2<35+42*u)
    (marks : ∀ r<stop+1, marked F (L7.view v (35+42*u:Nat) r c) ||
      marked F (L7.view v (35+42*u:Nat) (r+1:Nat) c)) :
    Attachment F (railInner u v c (stop+1) cl cu (by omega) (by omega)) where
  inside := railInner u v c 1 cl cu (by decide) (by omega)
  rim := ⟨railPoint u v c 0, (boundary_in_view v _).mpr (by
    rw [railPoint_coords (by omega : c<35+42*u) (by omega : 0<35+42*u)]
    exact Or.inl rfl)⟩
  reached := (northRail_path cl cu last marks).symm
  link := (rail_edge (by omega) (by omega) (marks 0 (by omega))).symm

theorem north_marked_edges {u k h : Nat} {F : Finset (Site u)} {v : View}
    (line : RootLine F v (k-1) (k-h))
    (top : square F v (firstRow k h) (1+3*(k-1))=73) :
    ∀ r<firstRow k h+1, marked F (L7.view v (35+42*u:Nat) r (1+3*(k-1):Nat)) ||
      marked F (L7.view v (35+42*u:Nat) (r+1:Nat) (1+3*(k-1):Nat)) := by
  intro r bound
  by_cases before : r<firstRow k h
  · exact line r before
  · have eq : r=firstRow k h := by omega
    subst r
    let f (i : Fin 9) := marked F (L7.view v (35+42*u:Nat)
      (firstRow k h+i.val/3:Nat) (1+3*(k-1)+i.val%3:Nat))
    change bits f=73 at top
    have b := (unpack f).2 0
    rw [top] at b
    change 1=(marked F (L7.view v (35+42*u:Nat) (firstRow k h) (1+3*(k-1):Nat))).toNat at b
    apply Bool.or_eq_true_iff.mpr
    left
    generalize marked F (L7.view v (35+42*u:Nat) (firstRow k h) (1+3*(k-1):Nat)) = a at b ⊢
    cases a
    · exact (Nat.one_ne_zero b).elim
    · rfl

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
