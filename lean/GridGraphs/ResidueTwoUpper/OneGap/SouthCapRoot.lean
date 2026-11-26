import GridGraphs.ResidueTwoUpper.OneGap.SouthCapHaloPrices
import GridGraphs.ResidueTwoUpper.OneGap.L7Exclusion

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil Finset

private theorem corner_bill {n : Nat} (hn : 12≤n)
    (P : GridVertex n n → GridVertex n n) (v : GridVertex n n)
    (corner : isCorner v) (sink : P v=v) :
    cornerBill P v=8*Stencil.cornerPrices.getD 0 0 := by
  have lo : axis n 6 0=0 := by unfold axis; split_ifs <;> omega
  have hi : axis n 6 ((n:Int)-1)=14 := by unfold axis; split_ifs <;> omega
  have dims (i : Fin n) (h : i.val=0 ∨ i.val+1=n) :
      (i.val:Int)=0 ∨ (i.val:Int)=(n:Int)-1 := by omega
  obtain row|row := dims v.1 corner.1 <;> obtain col|col := dims v.2 corner.2 <;>
    simp [cornerBill,sink,outDir,twoCornerAt,coord,row,col,
      show List.range 8=[0,1,2,3,4,5,6,7] by decide,corner_price,ResidueZero.image,atPos,lo,hi]

private theorem ranked_parent {n : Nat} (F : Finset (GridVertex n n))
    (root : GridVertex n n) (acy : (Bonds F).IsAcyclic) :
    ∃ (P : GridVertex n n → GridVertex n n) (rank : GridVertex n n → Nat),
      P root=root ∧ (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧
      (∀ x, P x≠x → rank (P x)<rank x) := by
  classical
  let R (c : (Bonds F).ConnectedComponent) :=
    if (Bonds F).connectedComponentMk root=c then root else c.out
  have sec c : (Bonds F).connectedComponentMk (R c)=c := by
    dsimp [R]; split_ifs <;> first | assumption | exact Quot.out_eq _
  let P := CapBill.parent R sec
  have step {v} (h : P v≠v) := CapBill.parent_step R sec (mt (CapBill.parent_fix R sec v).mpr h)
  refine ⟨P,CapBill.depth R,(CapBill.parent_fix R sec root).mpr (by simp [CapBill.dest,R]),
    fun _ h => (step h).1,?_,fun _ h => (step h).2⟩
  intro v w e
  constructor
  · intro a b
    have x := (step (v:=v) (by simpa [a] using e.ne.symm)).2
    have y := (step (v:=w) (by simpa [b] using e.ne)).2
    change CapBill.depth R (P v)<_ at x
    change CapBill.depth R (P w)<_ at y
    rw [a] at x; rw [b] at y; omega
  · intro h; exact (CapBill.parent_covers R sec acy e).resolve_right h

/-- Move the distinguished root without moving a mark. The isolated
defect is fixed by *any* admissible orientation, so it still spends the
whole budget. In particular all newly oriented rim stars have zero
price, even where their directions changed. -/
theorem reroot_clean (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (old : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (oldStep : ∀ x, old x≠x → (Bonds F).Adj x (old x))
    (d root : GridVertex (35+42*u) (35+42*u))
    (iso : (Bonds F).IsIsolated d) (paid : starSlack F old d=full)
    (corner : isCorner root) :
    ∃ P, ∃ rank : GridVertex (35+42*u) (35+42*u) → Nat, P root=root ∧ (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧
      starSlack F P d=full ∧ (∀ x, x≠d → starSlack F P x=0) ∧
      (∀ a, patchSlack F a=0) ∧ (∀ x, P x≠x → rank (P x)<rank x) := by
  classical
  let n := 35+42*u
  obtain ⟨P,rank,fix,step,covers,down⟩ := ranked_parent F root acy
  have pd : P d=d := by by_contra ne; exact iso _ (step _ ne)
  have od : old d=d := by by_contra ne; exact iso _ (oldStep _ ne)
  have price : starSlack F P d=full := by simpa [starSlack,pd,od] using paid
  let t := 5+14*u
  have e : n=20+3*t := by dsimp [n,t]; omega
  have ei : (n:Int)=20+3*(t:Int) := by exact_mod_cast e
  have ep : ((n-2:Nat):Int)=18+3*(t:Int) := by omega
  have st (v : GridVertex n n) : 0 ≤ starSlack F P v := by
    unfold starSlack; rw [ei]
    exact star_nonneg_of_check checkStars t (ei ▸ coord_inside v)
      (by cases decide (v∈F) <;> decide) (code_lt _) (outDir_lt ..)
      (ei ▸ starOK_physical F acy v _ (fun h => step _ h.symm))
  have pt (v : origins n) : 0 ≤ patchSlack F v := by
    unfold patchSlack; rw [ei]
    exact patch_nonneg_of_check checkPatches t (ep ▸ coord_inside v)
      (Fin.isLt _) (physical_mask_ok F acy ..)
  have cb := sum_nonpos (s:=univ.erase root) (fun x _ =>
    Stencil.corner_nonpos n (coord x) (outDir x (P x)))
  have ledger := exact_ledger (n:=n) (by dsimp [n]; omega) F P step covers
  have avail : 8*rhs n-8*Stencil.scale*(F.card:Int)=full := by
    have b := budget t
    rw [←e] at b
    rw [score]; dsimp [t] at b; push_cast at b ⊢
    unfold Stencil.scale at b ⊢; unfold full; ring_nf at b ⊢; omega
  rw [←sum_erase_add (s:=univ) (mem_univ root) (f:=cornerBill P),
    corner_bill (by omega) P root corner fix, avail] at ledger
  change (∑ v ∈ univ.erase root, cornerBill P v) ≤ 0 at cb
  rw [←sum_erase_add (s:=univ) (mem_univ d) (f:=starSlack F P),price] at ledger
  have s0 := sum_nonneg (s:=univ.erase d) (fun x _ => st x)
  have p0 := sum_nonneg (s:=univ) (fun x _ => pt x)
  have sZero : (∑ x ∈ univ.erase d, starSlack F P x)=0 := by linarith
  have pZero : (∑ x, patchSlack F x)=0 := by linarith
  refine ⟨P,rank,fix,step,covers,price,?_,?_,down⟩
  · intro x ne
    have le := single_le_sum (s:=univ.erase d) (f:=starSlack F P)
      (fun v _ => st v) (mem_erase.mpr ⟨ne,mem_univ x⟩)
    rw [sZero] at le; exact le_antisymm le (st x)
  · intro a
    have le := single_le_sum (s:=univ) (f:=patchSlack F) (fun v _ => pt v) (mem_univ a)
    rw [pZero] at le; exact le_antisymm le (pt a)

open GridGraphs.ResidueTwoUpper.Exceptional.Frame
open BoundarySix.Connected

/-- For the actual scored one-gap forest the chosen corner can be the
catalogue sink. Rerooting neither creates an inward perimeter arrow
nor incurs any extra star or patch charge. -/
theorem rim_root_at_defect (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (root : PerimeterVertex (35+42*u))
    (corner : isCorner root.1)
    (old : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (d : GridVertex (35+42*u) (35+42*u)) (iso : (Bonds F).IsIsolated d)
    (step : ∀ x, old x≠x → (Bonds F).Adj x (old x))
    (zeroOld : ∀ x, x≠d → starSlack F old x=0) :
    ∃ P, ∃ rank : GridVertex (35+42*u) (35+42*u) → Nat, P root.1=root.1 ∧
      (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧
      exitSet P=∅ ∧ starSlack F P d=full ∧ (∀ x, x≠d → starSlack F P x=0) ∧
      (∀ a, patchSlack F a=0) ∧ (∀ x, P x≠x → rank (P x)<rank x) := by
  obtain ⟨Q,z,qstep,_,_,isz,_,qpaid,_⟩ := L7.isolated_star_of_score u F acy score one
  have qfix : Q z=z := by by_contra ne; exact isz _ (qstep _ ne)
  have ofix : old z=z := by by_contra ne; exact isz _ (step _ ne)
  have paidz : starSlack F old z=full := by simpa [starSlack,qfix,ofix] using qpaid
  have eq : z=d := by
    by_contra ne
    rw [zeroOld _ ne] at paidz
    exact (by decide : (0 : Int)≠full) paidz
  have paid : starSlack F old d=full := eq ▸ paidz
  obtain ⟨P,rank,fix,edges,covers,charge,stars,patches,down⟩ :=
    reroot_clean u F acy score old step d root.1 iso paid corner
  have zero (x : occurrence (35+42*u)) (ne : x≠Sum.inl d) : weightAt F P x=0 := by
    cases x with
    | inl x => exact stars x (fun h => ne (congrArg Sum.inl h))
    | inr a => exact patches a
  have corners := corners_marked u F acy score
  have good := frame_checked stars_checked patches_checked u F P acy edges corners (fun x => by
    by_cases eq : x=Sum.inl d
    · exact Or.inr (eq ▸ charge)
    · exact Or.inl (zero x eq))
  have rooted := all_marks_reachable u F acy score _ (corners _ corner)
  have h := gap_split (by omega) F P root corners
    (fun _ _ edge => rooted.symm.trans (all_active_reachable u F acy score edge).1)
    fix edges covers good (Sum.inl d) zero
  exact ⟨P,rank,fix,edges,covers,(h.resolve_right (fun bad => by omega)).2,charge,stars,patches,down⟩

theorem rim_root_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (root : PerimeterVertex (35+42*u))
    (corner : isCorner root.1) :
    ∃ P d, P root.1=root.1 ∧
      (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧
      exitSet P=∅ ∧ (Bonds F).IsIsolated d ∧ starSlack F P d=full ∧
      (∀ x, x≠d → starSlack F P x=0) ∧ (∀ a, patchSlack F a=0) := by
  obtain ⟨old,d,step,_,_,iso,_,_,zero⟩ := L7.isolated_star_of_score u F acy score one
  have clean (x) (ne : x≠d) : starSlack F old x=0 :=
    zero (.inl x) (fun eq => ne (Sum.inl.inj eq))
  obtain ⟨P,_,fix,edge,cover,ex,paid,star,patch,_⟩ :=
    rim_root_at_defect u F acy score one root corner old d iso step clean
  exact ⟨P,d,fix,edge,cover,ex,iso,paid,star,patch⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
