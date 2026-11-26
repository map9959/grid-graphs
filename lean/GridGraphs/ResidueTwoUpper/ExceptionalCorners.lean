import GridGraphs.ResidueTwoUpper.ExceptionalComponent

namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil Finset SimpleGraph

private theorem corner_charge {n : Nat} (hn : 12≤n) (v : GridVertex n n) (c : isCorner v) :
    twoCornerAt n (coord v) 4=8*Stencil.cornerPrices.getD 0 0 := by
  have lo : axis n 6 0=0 := by unfold axis; split_ifs <;> omega
  have hi : axis n 6 ((n:Int)-1)=14 := by unfold axis; split_ifs <;> omega
  have dims (i : Fin n) (h : i.val=0 ∨ i.val+1=n) : (i.val:Int)=0 ∨ (i.val:Int)=(n:Int)-1 := by omega
  obtain row|row := dims v.1 c.1 <;> obtain col|col := dims v.2 c.2 <;>
    simp [twoCornerAt,coord,row,col,show List.range 8=[0,1,2,3,4,5,6,7] by decide,
      corner_price,ResidueZero.image,atPos,lo,hi]

private theorem sink_check : ∀ (r c : Fin 2) (m : Fin 16), let p : Pos := (22*r.val,22*c.val)
    m.val≠0 → starOK 23 p 0 m 4 → full<twoOrbitStar 23 p 0 m 4 := by native_decide

private theorem sink_price (u : Nat) (v : GridVertex (35+42*u) (35+42*u)) (c : isCorner v)
    (m : Fin 16) (nz : m.val≠0) (ok : starOK (35+42*(u:Int)) (coord v) 0 m 4) :
    full<twoOrbitStar (35+42*(u:Int)) (coord v) 0 m 4 := by
  let n := 35+42*u; let j := 4+14*u
  have e : 35+42*(u:Int)=23+3*(j:Int) := by dsimp [j]; omega
  rw [e] at ok ⊢
  let a := representative 23 j (coord v)
  have loc := starLocation_transport (b:=23) (by decide) (j:=(j:Int)) (by positivity) (coord v)
  have ins (d : Nat) : inside (23+3*(j:Int)) (shift (coord v) d)=inside 23 (shift a d) := by
    have h := congrArg (fun l : StarLocation => (l.neighbour d).isSome) (loc 0)
    simp only [starLocation,ResidueZero.image,located] at h
    split_ifs at h <;> simp_all [a]
  have ok' : starOK 23 a 0 m 4 := by simpa only [starOK,ins] using ok
  have mapEnd (i : Fin n) (h : i.val=0 ∨ i.val+1=n) :
      ∃ k : Fin 2, rep 23 j i.val=22*k.val := by
    rcases h with h|h
    · exact ⟨0,by simp [h,rep]⟩
    · refine ⟨1,?_⟩
      dsimp [n] at h; dsimp [j]; unfold rep; split_ifs <;> omega
  obtain ⟨r,hr⟩ := mapEnd v.1 c.1; obtain ⟨s,hs⟩ := mapEnd v.2 c.2
  have ea : a=(22*(r.val:Int),22*(s.val:Int)) := Prod.ext hr hs
  have result := sink_check r s m nz (ea ▸ ok')
  rw [←ea] at result
  simpa only [twoOrbitStar,loc,a] using result

theorem corners_marked (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    ∀ v, isCorner v → v∈F := by
  intro v c
  by_contra empty
  let n := 35+42*u
  have touched : ∃ y, (Bonds F).Adj v y := by
    by_cases isNW : v=nw u
    · subst v
      obtain ⟨y,mem⟩ := card_pos.mp (show 0<F.card by omega)
      obtain ⟨walk⟩ := all_marks_reachable u F acy score y mem
      cases walk with
      | nil => exact False.elim (empty mem)
      | cons e _ => exact ⟨_,e⟩
    · obtain ⟨Q,_,step,_,_,corners,_⟩ := exceptional_slack u F acy score
      exact ⟨Q v,step v (fun fix => isNW (corners v c fix))⟩
  obtain ⟨y,edge⟩ := touched
  have mark : y∈F := edge.2.resolve_left empty
  obtain ⟨P,fixed,step,covers⟩ := parent_exists F v acy
  let t := 5+14*u
  have e : n=20+3*t := by dsimp [n,t]; omega
  have ei : (n:Int)=20+3*(t:Int) := by exact_mod_cast e
  have ep : ((n-2:Nat):Int)=18+3*(t:Int) := by omega
  have st (x : GridVertex n n) : 0 ≤ starSlack F P x := by
    unfold starSlack; rw [ei]
    exact star_nonneg_of_check checkStars _ (ei ▸ coord_inside x)
      (by cases decide (x∈F) <;> decide) (code_lt _) (outDir_lt ..) (ei ▸ starOK_physical F acy x _ (fun h => step _ h.symm))
  have pt (a : origins n) : 0≤patchSlack F a := by
    unfold patchSlack; rw [ei]
    exact patch_nonneg_of_check checkPatches _ (ep ▸ coord_inside a) (Fin.isLt _) (physical_mask_ok F acy ..)
  have sumP := sum_nonneg (s:=univ) (fun x _ => pt x)
  have le := single_le_sum (s:=univ) (f:=starSlack F P) (fun x _ => st x) (mem_univ v)
  have bill := exact_ledger (n:=n) (by dsimp [n]; omega) F P step covers
  have rem := sum_nonpos (s:=univ.erase v) (fun x _ => Stencil.corner_nonpos n (coord x) (outDir x (P x)))
  change (∑ x ∈ univ.erase v, cornerBill P x) ≤ 0 at rem
  have val : cornerBill P v=8*Stencil.cornerPrices.getD 0 0 := by
    unfold cornerBill; rw [fixed]; simpa [outDir] using corner_charge (n:=n) (by dsimp [n]; omega) v c
  rw [←sum_erase_add (s:=univ) (mem_univ v) (f:=cornerBill P),val] at bill
  have b := budget t
  rw [←e] at b
  have avail : 8*rhs n-8*Stencil.scale*(F.card:Int)=full := by
    rw [score]; dsimp [t] at b; push_cast at b ⊢; unfold Stencil.scale at b ⊢; unfold full
    ring_nf at b ⊢; omega
  rw [avail] at bill
  have cap : starSlack F P v≤full := by linarith
  let m : Fin 16 := ⟨neighbours F (coord v),code_lt _⟩
  have nz : m.val≠0 := by
    have d : outDir v y <4 := by unfold outDir; split_ifs <;> simp_all [edge.1.ne]
    have h := neighbours_bit F (coord v) ⟨_,d⟩
    change bit m.val (outDir v y)=(marked F (shift (coord v) (outDir v y))).toNat at h
    rw [shift_out edge.1,marked_at] at h
    intro z; simp [z,bit,mark] at h
  have legal := starOK_physical F acy v _ (fun h => step _ h.symm)
  simp [empty,fixed,outDir] at legal cap
  have cast : (n:Int)=35+42*(u:Int) := by dsimp [n]
  have ok : starOK (35+42*(u:Int)) (coord v) 0 m 4 := cast ▸ legal
  have costly := sink_price u v c m nz ok
  have eq : starSlack F P v=twoOrbitStar (35+42*(u:Int)) (coord v) 0 m 4 := by
    simp [starSlack,empty,fixed,outDir,m]
  exact costly.not_ge (eq ▸ cap)

end GridGraphs.ResidueTwoUpper.Exceptional
