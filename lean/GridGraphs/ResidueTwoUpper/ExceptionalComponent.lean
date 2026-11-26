import GridGraphs.ResidueTwoUpper.ExceptionalBudget
import GridGraphs.ResidueTwoUpper.ExceptionalParityTransport

/-! Every mark in an exceptional upper witness is in the northwest
corner component. Otherwise root its detached component at that very
mark. A second corner sink or a noncorner marked sink exceeds the
entire available budget, even before any other atom is charged. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil Finset SimpleGraph

def nw (u : Nat) : GridVertex (35+42*u) (35+42*u) := (⟨0,by omega⟩,⟨0,by omega⟩)

private theorem two_roots {n} (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (v w : GridVertex n n) (disjoint : ¬(Bonds F).Reachable v w) :
    ∃ P : GridVertex n n → GridVertex n n, P v=v ∧ P w=w ∧
      (∀ a, P a≠a → (Bonds F).Adj a (P a)) ∧
      ∀ a b, (Bonds F).Adj a b → (P a=b ↔ P b≠a) := by
  classical
  let G := Bonds F
  let R (c : G.ConnectedComponent) := if G.connectedComponentMk v=c then v
    else if G.connectedComponentMk w=c then w else c.out
  have different : G.connectedComponentMk v≠G.connectedComponentMk w :=
    fun e => disjoint (ConnectedComponent.exact e)
  have sec c : G.connectedComponentMk (R c)=c := by
    dsimp [R]; split_ifs <;> first | assumption | exact Quot.out_eq _
  let P := CapBill.parent R sec
  have step {a} (h : P a≠a) := CapBill.parent_step R sec (mt (CapBill.parent_fix R sec a).mpr h)
  refine ⟨P,(CapBill.parent_fix R sec v).mpr (by simp [CapBill.dest,R]),
    (CapBill.parent_fix R sec w).mpr (by simp [CapBill.dest,R,different]),fun _ h => (step h).1,?_⟩
  intro a b e
  constructor
  · intro h k
    have x := (step (a:=a) (by simpa [h] using e.ne.symm)).2
    have y := (step (a:=b) (by simpa [k] using e.ne)).2
    change CapBill.depth R (P a)<_ at x
    change CapBill.depth R (P b)<_ at y
    rw [h] at x; rw [k] at y; omega
  · intro h; exact (CapBill.parent_covers R sec acy e).resolve_right h

private def onCorner (n : Int) (p : Pos) := (p.1=0 ∨ p.1=n-1) ∧ (p.2=0 ∨ p.2=n-1)
private def sinkCheck := decide (∀ (i j : Fin 23) (nb : Fin 16),
    let p : Pos := (i.val,j.val)
    ¬((i.val=0 ∨ i.val=22) ∧ (j.val=0 ∨ j.val=22)) → starOK 23 p 1 nb 4 →
      full<twoOrbitStar 23 p 1 nb 4)
private theorem sink_checked : sinkCheck := by native_decide

private theorem expensive {u : Nat} {p : Pos} (hp : inside (35+42*(u:Int)) p)
    (notcorner : ¬onCorner (35+42*(u:Int)) p) (nb : Fin 16) (ok : starOK (35+42*(u:Int)) p 1 nb 4) :
    full<twoOrbitStar (35+42*(u:Int)) p 1 nb 4 := by
  let j := 4+14*u
  have e : 35+42*(u:Int)=23+3*(j:Int) := by dsimp [j]; omega
  rw [e] at hp notcorner ok ⊢
  let v := representative 23 j p
  have lim (i : Int) (hi : 0 ≤ i ∧ i<23+3*(j:Int)) : 0≤rep 23 j i ∧ rep 23 j i<23 :=
    rep_bounds (by decide) (by positivity) hi.1 hi.2
  simp [inside] at hp
  have X := lim p.1 (by omega); have Y := lim p.2 (by omega)
  let i : Fin 23 := ⟨(v.1).toNat,by dsimp [v,representative]; omega⟩
  let k : Fin 23 := ⟨(v.2).toNat,by dsimp [v,representative]; omega⟩
  have coords : ((i.val:Int),(k.val:Int))=v := by
    ext <;> dsimp [i,k,v,representative] <;> omega
  have ends (z : Int) : (rep 23 j z=0 ↔ z=0) ∧ (rep 23 j z=22 ↔ z=23+3*(j:Int)-1) := by
    unfold rep; split_ifs <;> omega
  have hnc : ¬((i.val=0 ∨ i.val=22) ∧ (k.val=0 ∨ k.val=22)) := by
    have a := ends p.1; have b := ends p.2
    unfold onCorner at notcorner; dsimp [i,k,v,representative]; omega
  have loc := starLocation_transport (b:=23) (by decide) (j:=(j:Int)) (by positivity) p
  have ins (d : Nat) : inside (23+3*(j:Int)) (shift p d)=inside 23 (shift v d) := by
    have h := congrArg (fun l : StarLocation => (l.neighbour d).isSome) (loc 0)
    simp only [starLocation,ResidueZero.image,located] at h
    split_ifs at h <;> simp_all [v]
  have ok' : starOK 23 v 1 nb 4 := by simpa only [starOK,ins] using ok
  have chk := of_decide_eq_true sink_checked i k nb
  dsimp only at chk; rw [coords] at chk
  simpa only [twoOrbitStar,loc,v] using chk hnc ok'

set_option maxHeartbeats 500000 in
theorem all_marks_reachable (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    ∀ w ∈ F, (Bonds F).Reachable (nw u) w := by
  intro w marked
  by_contra detached
  let n := 35+42*u
  obtain ⟨P,root,fixed,step,covers⟩ := two_roots F acy (nw u) w detached
  have ne : w≠nw u := by rintro rfl; exact detached .rfl
  have ledger := exact_ledger (n:=n) (by dsimp [n]; omega) F P step covers
  let t := 5+14*u
  have e : n=20+3*t := by dsimp [n,t]; omega
  have ei : (n:Int)=20+3*(t:Int) := by exact_mod_cast e
  have ep : ((n-2:Nat):Int)=18+3*(t:Int) := by omega
  have st (v : GridVertex n n) : 0 ≤ starSlack F P v := by
    unfold starSlack; rw [ei]
    exact star_nonneg_of_check checkStars t (ei ▸ coord_inside v)
      (by cases decide (v∈F) <;> decide) (code_lt _) (outDir_lt ..)
      (ei ▸ starOK_physical F acy v _ (fun h => step _ h.symm))
  have pt (v : origins n) : 0≤patchSlack F v := by
    unfold patchSlack; rw [ei]
    exact patch_nonneg_of_check checkPatches t (ep ▸ coord_inside v) (Fin.isLt _) (physical_mask_ok F acy ..)
  have positive := sum_nonneg (s:=univ) (fun v _ => pt v)
  have atw := single_le_sum (s:=univ) (f:=starSlack F P) (fun v _ => st v) (mem_univ w)
  have price := budget t
  rw [←e] at price
  have avail : 8*rhs n-8*Stencil.scale*(F.card:Int)=full := by
    rw [score]; dsimp [t] at price; push_cast at price ⊢
    unfold Stencil.scale at price ⊢; unfold full; ring_nf at price ⊢; omega
  have rootVal : cornerBill P (nw u)=8*Stencil.cornerPrices.getD 0 0 := by
    unfold cornerBill; rw [root]
    simpa [nw,coord,outDir] using root_charge (n:=n) (by dsimp [n]; omega)
  have parts := sum_erase_add (s:=univ) (mem_univ (nw u)) (f:=cornerBill P)
  have rest := sum_nonpos (s:=univ.erase (nw u)) (fun v _ => Stencil.corner_nonpos n (coord v) (outDir v (P v)))
  change (∑ v ∈ univ.erase (nw u), cornerBill P v) ≤ 0 at rest
  rw [←parts,rootVal,avail] at ledger
  by_cases c : isCorner w
  · have lo : axis n 6 0=0 := by unfold axis; dsimp [n]; split_ifs <;> omega
    have hi : axis n 6 ((n:Int)-1)=14 := by unfold axis; dsimp [n]; split_ifs <;> omega
    have dims (i : Fin n) (h : i.val=0 ∨ i.val+1=n) :
        (i.val:Int)=0 ∨ (i.val:Int)=(n:Int)-1 := by omega
    have cprice : cornerBill P w= -27378014256 := by
      change twoCornerAt n (coord w) (outDir w (P w))=_
      obtain row|row := dims w.1 c.1 <;> obtain col|col := dims w.2 c.2 <;>
        simp [fixed,outDir,twoCornerAt,coord,row,col,show List.range 8=[0,1,2,3,4,5,6,7] by decide,
          corner_price,ResidueZero.image,atPos,lo,hi]
    have less := single_le_sum (s:=univ.erase (nw u)) (f:=fun v => -cornerBill P v)
      (fun v _ => neg_nonneg.mpr (Stencil.corner_nonpos n (coord v) (outDir v (P v)))) (mem_erase.mpr ⟨ne,mem_univ w⟩)
    rw [sum_neg_distrib,cprice] at less
    unfold full at ledger; linarith [st w]
  · have no : ¬onCorner (35+42*(u:Int)) (coord w) := by
      unfold isCorner at c; unfold onCorner; simp only [coord]; omega
    have ok := starOK_physical F acy w (P w) (fun h => step _ h.symm)
    simp [marked,fixed,outDir] at ok
    have cast : (n:Int)=35+42*(u:Int) := by dsimp [n]
    let nb : Fin 16 := ⟨neighbours F (coord w),code_lt _⟩
    have legal : starOK (35+42*(u:Int)) (coord w) 1 nb 4 := cast ▸ ok
    have bad := expensive (u:=u) (p:=coord w) (cast ▸ coord_inside w) no nb legal
    have eq : starSlack F P w=twoOrbitStar (35+42*(u:Int)) (coord w) 1 (neighbours F (coord w)) 4 := by
      simp [starSlack,cast,marked,fixed,outDir,n]
    rw [eq] at atw
    linarith

theorem all_active_reachable (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    {v w} (edge : (Bonds F).Adj v w) :
    (Bonds F).Reachable (nw u) v ∧ (Bonds F).Reachable (nw u) w := by
  rcases edge.2 with mark|mark
  · have r := all_marks_reachable u F acy score v mark
    exact ⟨r,r.trans edge.reachable⟩
  · have r := all_marks_reachable u F acy score w mark
    exact ⟨r.trans edge.symm.reachable,r⟩

end GridGraphs.ResidueTwoUpper.Exceptional
