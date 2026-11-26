import GridGraphs.ResidueTwoUpper.OneGap.FanSeedPhysical
import GridGraphs.ResidueTwoUpper.OneGap.Grounding
import GridGraphs.ResidueTwoUpper.OneGap.L7Rim

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7 BoundarySix.Connected

/-- The five terminal columns are checked in order. The horizontal low
end is not used: either choice for that frame bit is allowed. -/
private theorem close_test : ∀ s f : Bool, ∀ a∈opt s f 30, ∀ b∈opt s f 31,
    ∀ c∈opt s f 32, cleanBand 30 a b c → ∀ d∈opt s f 33, cleanBand 31 b c d →
    window b c d 4=73 → ∀ e∈opt s f 34, cleanBand 32 c d e →
    ∀ r : Fin 7, r.val≠1 → lane b r=1 := by native_decide

def siteAt (u j : Nat) (hj : j<35+42*u) (w : View) (r : Fin 7) : GridVertex (35+42*u) (35+42*u) :=
  onSite (L7.view w (35+42*u:Nat) r.val (j:Nat)) (inside_view w (by have := r.isLt; omega) (by omega))
theorem geometry (u j : Nat) (hj : 0<j ∧ j+1<35+42*u) (w : View) (r : Fin 7) :
    (IsGridBoundary (siteAt u j (by omega) w r) ↔ r.val=0) ∧
    ∀ t : Fin 7, r.val+1=t.val → (gridGraph _ _).Adj (siteAt u j (by omega) w r) (siteAt u j (by omega) w t) := by
  have coord' (r : Fin 7) : coord (siteAt u j (by omega) w r)=L7.view w (35+42*u:Nat) r.val (j:Nat) := coord_onSite ..
  have A (r : Fin 7) := congrArg Prod.fst (coord' r)
  have B (r : Fin 7) := congrArg Prod.snd (coord' r)
  constructor
  · have := A r; have := B r; have := r.isLt
    cases w with | mk a b s => cases a <;> cases b <;> cases s <;>
      simp only [IsGridBoundary,L7.view,reflect,coord,Bool.false_eq_true,if_true,if_false,
        Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at * <;> omega
  · intro t ht
    have := A r; have := A t; have := B r; have := B t
    change adjacent _ _ _ _; simp only [adjacent,Fin.ext_iff]
    cases w with | mk a b s => cases a <;> cases b <;> cases s <;>
      simp [L7.view,reflect,coord] at * <;> omega

abbrev lineSite (u : Nat) (w : View) := siteAt u (31+42*u) (by omega) w
private abbrev geom (u : Nat) (w : View) := geometry u (31+42*u) (by omega) w
def cut (u : Nat) (w : View) : {p : GridVertex (35+42*u) (35+42*u) // ¬IsGridBoundary p} :=
  ⟨lineSite u w 5,fun h => (by decide : (5:Fin 7).val≠0) ((geom u w 5).1.mp h)⟩
def foot (u : Nat) (w : View) : PerimeterVertex (35+42*u) := ⟨lineSite u w 0,(geom u w 0).1.mpr rfl⟩

/-- Physical south-east terminal at the last seven physical rows. Only the last line
is assumed rooted: if its tile is 73, clean patches and the true closed
corner connect it all the way to the south tooth. -/
theorem south_cap (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1) (clean : ∀ a,patchSlack F a=0)
    (w : View) (s f : Bool) (rim : ∀ k : Fin 5, chartCol F w (30+42*u+k.val)∈opt s f (30+k.val))
    (src : {p : GridVertex (35+42*u) (35+42*u) // ¬IsGridBoundary p})
    (root : PerimeterVertex (35+42*u)) (different : root≠foot u w) (edge : (Bonds F).Adj src.1 root.1)
    (rooted : ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src (cut u w)) :
    window (chartCol F w (31+42*u)) (chartCol F w (32+42*u)) (chartCol F w (33+42*u)) 4≠73 := by
  intro seed
  let X := chartCol F w
  have in' (k : Fin 5) : X (30+k.val+42*u)∈opt s f (30+k.val) := by
    simpa only [Nat.add_right_comm] using rim k
  have band' (k : Fin 3) : cleanBand (30+k.val) (X (30+k.val+42*u))
      (X ((30+k.val+1)+42*u)) (X ((30+k.val+2)+42*u)) := by
    have h := physical u F acy clean w (30+k.val+42*u) (by have := k.isLt; omega)
    rw [show fold u (30+k.val+42*u)=30+k.val by unfold fold; split_ifs <;> omega] at h
    simpa only [Nat.add_right_comm _ (42*u)] using h
  have line := close_test s f _ (in' 0) _ (in' 1) _ (in' 2) (band' 0) _ (in' 3) (band' 1) seed _ (in' 4) (band' 2)
  have marked' (r : Fin 7) (ne : r.val≠1) : lineSite u w r∈F := by
    have H := line r ne; change lane (chartCol F w (31+42*u)) r=1 at H
    rw [col_bit,←show coord (lineSite u w r)=_ from coord_onSite ..,marked_at] at H
    simpa using H
  let I (k : Fin 6) : {p : GridVertex (35+42*u) (35+42*u) // ¬IsGridBoundary p} :=
    ⟨lineSite u w ⟨k.val+1,by have := k.isLt; omega⟩,fun h => Nat.succ_ne_zero _ ((geom ..).1.mp h)⟩
  have link (k l : Fin 6) (eq : k.val+1=l.val) :
      ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable (I l) (I k) := by
    apply SimpleGraph.Adj.reachable
    exact ⟨((geom ..).2 _ (by dsimp; omega)).symm,Or.inl (marked' _ (by dsimp; omega))⟩
  have path := rooted.trans ((link 3 4 rfl).trans ((link 2 3 rfl).trans
    ((link 1 2 rfl).trans (link 0 1 rfl))))
  apply different (unique_attachment (by omega) F acy one src (I 0) root (foot u w) path edge _).2
  exact ⟨((geom u w 0).2 1 rfl).symm,Or.inr (marked' 0 (by decide))⟩

open TwoGap.Words GridGraphs.ResidueTwoUpper.Exceptional.Frame

/-- Only the far corner needs to be closed. The certificate does not
prescribe the near corner on the south side. -/
theorem cap_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (clean : ∀ a,patchSlack F a=0)
    (w : View) (closed : ∀ b, (otherEnd w,b)∉gaps (n:=35+42*u) (by omega) F)
    (src : {p : GridVertex (35+42*u) (35+42*u) // ¬IsGridBoundary p})
    (root : PerimeterVertex (35+42*u)) (different : root≠foot u w) (edge : (Bonds F).Adj src.1 root.1)
    (rooted : ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src (cut u w)) :
    window (chartCol F w (31+42*u)) (chartCol F w (32+42*u)) (chartCol F w (33+42*u)) 4≠73 := by
  obtain ⟨P,_,step,_,_,_,good,_⟩ := frame_of_score u F acy score
  have hn : 35≤35+42*u := by omega
  have geo (p) := star_geometry hn F P step p (good (.inl p))
  obtain ⟨f,h⟩ := realize_on hn F w false (fun j => 30+42*u≤j) (corners_marked u F acy score)
    (fun p => (geo p).1) (fun p => (geo p).2.1) (fun i _ h => by have := i.isLt; omega)
    (fun _ _ h => by omega) closed (physicalWord_ok hn F P good _)
  apply south_cap u F acy one clean w false f _ src root different edge rooted
  intro k
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr (col_lt ..),List.all_eq_true.mpr ?_⟩
  intro r hr
  have idx : preset (35+42*u) false f r (30+42*u+k.val)=preset 35 false f r (30+k.val) := by
    have := k.isLt; unfold preset; split_ifs <;> first | rfl | omega
  cases e : preset 35 false f r (30+k.val) with
  | none => simp
  | some b =>
    have z := h r (30+42*u+k.val) (by omega) (List.mem_range.mp hr) (by have := k.isLt; omega) b (idx.trans e)
    have B := (col_bit F w ⟨r,List.mem_range.mp hr⟩ (30+42*u+k.val)).trans (congrArg Bool.toNat z)
    simp [B]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
