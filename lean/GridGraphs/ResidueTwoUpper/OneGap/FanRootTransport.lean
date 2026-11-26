import GridGraphs.ResidueTwoUpper.OneGap.FanRoot

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7 BoundarySix.Connected TwoGap.Words GridGraphs.ResidueTwoUpper.Exceptional.Frame

/-- Face the opposite side but keep exactly the same physical line. -/
def opposite (w : View) : View := if w.swap then {w with colFar := !w.colFar} else {w with rowFar := !w.rowFar}
theorem opposite_pos (w : View) (n r c : Int) : L7.view (opposite w) n r c=L7.view w n (n-1-r) c := by
  cases w with | mk x y s => cases x <;> cases y <;> cases s <;> ext <;> simp [opposite,L7.view,reflect]

abbrev Crop (n : Nat) := {p : GridVertex n n // ¬IsGridBoundary p}
def atDepth {n} (w : View) (r c : Nat) (hr : r<n) (hc : c<n) : GridVertex n n :=
  onSite (L7.view w n r c) (inside_view w hr hc)
private theorem geometry' {n} (w : View) (c : Nat) (hc : 0<c ∧ c+1<n) (r : Nat) (hr : r+1<n) :
    (IsGridBoundary (atDepth (n:=n) w r c (by omega) (by omega)) ↔ r=0) ∧
    (gridGraph n n).Adj (atDepth w r c (by omega) (by omega)) (atDepth w (r+1) c hr (by omega)) := by
  have coords (d : Nat) (hd : d<n) : coord (atDepth w d c hd (by omega))=L7.view w n d c := coord_onSite ..
  have R := congrArg Prod.fst (coords r (by omega)); have C := congrArg Prod.snd (coords r (by omega))
  have S := congrArg Prod.fst (coords (r+1) hr); have T := congrArg Prod.snd (coords (r+1) hr)
  change (_ ↔ _) ∧ adjacent ..
  cases w with | mk x y s => cases x <;> cases y <;> cases s <;>
    simp only [L7.view,reflect,coord,Bool.false_eq_true,if_false,if_true,IsGridBoundary,adjacent,Fin.ext_iff,
      Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_one] at * <;> omega

def inner {n} (w : View) (r c : Nat) (hr : 0<r ∧ r+1<n) (hc : 0<c ∧ c+1<n) : Crop n :=
  ⟨atDepth w r c (by omega) (by omega),fun h => by have := (geometry' w c hc r hr.2).1.mp h; omega⟩

/-- No identification of two roots is made when advancing a line: it
retains the input crop vertex, even if some sites on the line are unmarked. -/
theorem carry {n} (F : Finset (GridVertex n n)) (w : View) (c l h : Nat) (hc : 0<c ∧ c+1<n)
    (hl : 0<l) (lh : l≤h) (hh : h+1<n) (src : Crop n)
    (rooted : ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src (inner w l c ⟨hl,by omega⟩ hc))
    (covered : ∀ r, l≤r → r<h → marked F (L7.view w n r c) || marked F (L7.view w n (r+1:Nat) c)) :
    ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src (inner w h c ⟨by omega,hh⟩ hc) := by
  induction h,lh using Nat.le_induction with
  | base => exact rooted
  | succ k le ih =>
    apply (ih (by omega) rooted (fun r a b => covered r a (by omega))).trans
    apply SimpleGraph.Adj.reachable
    refine ⟨(geometry' w c hc k (by omega)).2,?_⟩
    have z := covered k le (by omega)
    have mark (r : Nat) (hr : r<n) : marked F (L7.view w n r c)=decide (atDepth w r c hr (by omega)∈F) :=
      (congrArg (marked F) (coord_onSite ..)).symm.trans (marked_at F _)
    change atDepth (n:=n) w k c (by omega) (by omega)∈F ∨ atDepth (n:=n) w (k+1) c (by omega) (by omega)∈F
    simpa only [mark k (by omega),mark (k+1) (by omega),Bool.or_eq_true,decide_eq_true_eq] using z

/-- In a normalized one-gap frame the diagonally opposite corner is closed. -/
theorem opposite_closed (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) (w : View) (s f : Bool)
    (h : rim F w s f) : ∀ b, (otherEnd (opposite w),b)∉gaps (n:=35+42*u) (by omega) F := by
  let n := 35+42*u
  have hn : 35≤n := by dsimp [n]; omega
  obtain ⟨P,_,step,_,_,_,good,_⟩ := frame_of_score u F acy score
  rw [exact_holes hn F (corners_marked u F acy score) (fun x => (star_geometry hn F P step x (good (.inl x))).1),
    Finset.card_image_of_injective _ (gapEdge_inj hn)] at one
  let t := if s then !w.swap else w.swap
  have un (i : Fin 3) (hi : i.val=1 ∨ i.val=2) : (atArm hn (corner w,t) i).1∉F := by
    have E : coord (atArm hn (corner w,t) i).1=L7.view w n (if s then (i.val:Int) else 0) (if s then 0 else (i.val:Int)) := by
      cases w with | mk x y z => cases x <;> cases y <;> cases z <;> cases s <;> ext <;> simp [corner,t,coord,atArm,loc,L7.view,reflect] <;> omega
    have Z : marked F (coord (atArm hn (corner w,t) i).1)=false := by
      rw [E]; cases s
      · exact h 0 i.val (by decide) (by omega) false (by simp [preset,hi])
      · exact h i.val 0 (by omega) (by omega) false (by simp [preset,hi,show i.val≠0 by omega])
    simpa [marked_at] using Z
  have G : (corner w,t)∈gaps hn F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,un 1 (.inl rfl),un 2 (.inr rfl)⟩
  have ne : otherEnd (opposite w)≠corner w := by cases w with | mk x y z => cases x <;> cases y <;> cases z <;> decide
  intro b H; apply ne
  obtain ⟨a,eq⟩ := Finset.card_eq_one.mp one
  rw [eq,Finset.mem_singleton] at H G
  exact congrArg Prod.fst (H.trans G.symm)

set_option maxHeartbeats 1500000 in
/-- Terminal obstruction with no supplied root, path, or closed-corner
hypothesis. The edge interval is [5,n-6), on the final aligned column n-4. -/
theorem break_or_cap (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1)
    (clean : ∀ a, patchSlack F a=0) (w : View) (s f : Bool) (side : rim F w s f)
    (seed : tile F w 1 (31+42*u)=72) (more : lane (tile F w 4 (31+42*u)) 0=1)
    (cap : tile F (opposite w) 4 (31+42*u)=73) :
    ∃ r, 5≤r ∧ r<29+42*u ∧ marked F (L7.view w (35+42*u:Nat) r (31+42*u:Nat))=false ∧
      marked F (L7.view w (35+42*u:Nat) (r+1:Nat) (31+42*u:Nat))=false := by
  classical
  by_contra! no
  obtain ⟨root,src,dst,er,es,ed,edge,path⟩ := rooted_seed u _ F w s f side (by omega) (by omega) seed more
  have end' : (cut u (opposite w)).1=atDepth w (29+42*u) (31+42*u) (by omega) (by omega) := by
    apply coord_injective
    change coord (lineSite u (opposite w) 5)=_
    rw [show coord (lineSite u (opposite w) 5)=_ from coord_onSite ..,opposite_pos,
      show coord (atDepth w (29+42*u) (31+42*u) (by omega) (by omega))=_ from coord_onSite ..]
    congr 1 <;> push_cast <;> omega
  have ne : root≠foot u (opposite w) := by
    intro same
    have hh := congrArg (fun a : PerimeterVertex (35+42*u) => coord a.1) same
    rw [er] at hh
    change coord (siteAt u _ _ w 0)=coord (lineSite u (opposite w) 0) at hh
    rw [show coord (siteAt u (31+42*u) _ w 0)=_ from coord_onSite ..,
      show coord (lineSite u (opposite w) 0)=_ from coord_onSite ..,opposite_pos] at hh
    cases w with | mk a b z => cases a <;> cases b <;> cases z <;> simp [L7.view,reflect] at hh <;> omega
  apply cap_of_score u F acy score one clean (opposite w) (opposite_closed u F acy score one w s f side) src root ne edge _
    (by simpa only [tile,show 31+42*u+1=32+42*u by omega,show 31+42*u+2=33+42*u by omega] using cap)
  have st : dst=inner w 5 (31+42*u) (by omega : 0<5 ∧ 5+1<35+42*u) (by omega) := Subtype.ext ed
  rw [st] at path
  have H := carry F w _ 5 (29+42*u) (by omega) (by omega) (by omega) (by omega) src path (by
    intro r hr ha; have := no r hr ha; cases e : marked F (L7.view w (35+42*u:Nat) r (31+42*u:Nat)) <;> simp_all)
  exact (show inner w (29+42*u) (31+42*u) (by omega : 0<29+42*u ∧ 29+42*u+1<35+42*u) (by omega)=cut u (opposite w) from Subtype.ext end'.symm) ▸ H
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
