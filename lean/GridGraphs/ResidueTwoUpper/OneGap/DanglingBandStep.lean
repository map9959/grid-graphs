import GridGraphs.ResidueTwoUpper.OneGap.CollisionBand

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SlowBand
open ResidueZero Stencil L7 FanSlab FanSeed Camera Port Port.Halo Short BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan.Rooted.Buffered
local notation "TILE" => SouthCap.Strip.GridScan.Rooted.tile

-- Two incoming 73 rows; the two named dangling tips cannot point north.
private def pinned (r c m o : Nat) :=
  (r%3 != 0 || c%3 != 0 || r>3 || m==73) &&
    (r != 2 || c%3 != 2 || c+1>6 || o != 3)
private def board := build 21 fun r c =>
  ((List.range 512).filter fun m => accepts (5+(r+1)%3) (5+(c+1)%3) m).flatMap fun m =>
    ((List.range 4).filter fun o => active m o && pinned r c m o).map (m,·)
private def output := Short.prune 21 10 board
private theorem checks : ∀ j : Fin 2, ∀ i : Fin 4,
    (atRC output (6+3*j.val) (3*(1+j.val+i.val))).all fun z => bandMask z.1 := by native_decide

private theorem local_masks {u q F w P} (S : Short.Seed (u:=u) F P w q)
    (acy : (Bonds F).IsAcyclic) (Q : Flow F) {y a : Nat}
    (yl : 5≤y) (yh : y+10≤11+14*u) (al : 4≤a) (ah : a+10≤11+14*u)
    (dang : a+2≤q) (born : (q:Int)-a+3≤1+3*(y:Int))
    (front : Front F w q (11+14*u) y a)
    (prev : ∀ i, a ≤ i → i<11+14*u → TILE F w (y-1) i=73)
    {j i : Nat} (jl : j<2) (ih : i<4) :
    bandMask (TILE F w (y+1+j) (a+1+j+i)) := by
  let R := 1+3*(y-1); let C := 1+3*a
  have pr := prices_of_seed u q F acy w P S.step S.clean
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero)
  obtain ⟨X,agree,act,sq,ds⟩ := CollisionWide.owner_chart Q pr R C 21
    (by dsimp [R]; omega) (by dsimp [C]; omega)
  have kept : Kept 21 X board := by
    intro r hr c hc
    have mask := pr (R+r) (C+c) (by dsimp [R]; omega) (by dsimp [R]; omega)
      (by dsimp [C]; omega) (by dsimp [C]; omega)
    rw [←sq,show (R+r)%3=(r+1)%3 by dsimp [R]; omega,
      show (C+c)%3=(c+1)%3 by dsimp [C]; omega] at mask
    have pin : pinned r c (X r c).1 (X r c).2 := by
      apply Bool.and_eq_true_iff.mpr
      constructor
      · simp only [Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq,beq_iff_eq]
        by_contra! no
        apply no.2
        rw [sq,show C+c=1+3*(a+c/3) by dsimp [C]; omega]
        rcases (show r=0 ∨ r=3 by omega) with rfl|rfl
        · exact prev _ (by omega) (by omega)
        · rw [show R+3=1+3*y by dsimp [R]; omega]
          exact front.1 _ le_rfl le_rfl _ (by omega) (by omega)
      · simp only [Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq]
        by_contra! no
        obtain ⟨⟨⟨rfl,phase⟩,lim⟩,north⟩ := no
        let b := a+(c+1)/3
        have tag : (C+(c+1):Nat)=1+3*b := by dsimp [C,b]; omega
        have row : (R+(2+1):Nat)=1+3*y := by dsimp [R]; omega
        have pos := dangling_tip F w Q q y b (by dsimp [N]; omega)
          (by dsimp [N,b]; omega) (by dsimp [b]; omega)
          (front.2.1 b (by dsimp [b]; omega) (by dsimp [b]; omega) (by dsimp [b]; omega))
          (front.1 _ le_rfl le_rfl b (by dsimp [b]; omega) (by dsimp [b]; omega))
        have lt := dir_lt F w Q pr (R+3) (C+(c+1)) (by dsimp [R]; omega) (by dsimp [C]; omega)
        rw [ds] at north
        change arrow Q.parent w ((R+3:Nat),(C+(c+1):Nat))%4=3 at north
        rw [Nat.mod_eq_of_lt lt,row,tag] at north
        exact pos (by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using north)
    have bd : (X r c).1<512 := by rw [sq]; exact (unpack _).1
    have ar : (X r c).2<4 := (ds r c) ▸ (dirsAt Q w R C (r+1) (c+1)).isLt
    rw [board,at_build hr hc]
    exact List.mem_flatMap.mpr ⟨_,List.mem_filter.mpr ⟨List.mem_range.mpr bd,mask⟩,
      List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨List.mem_range.mpr ar,
        Bool.and_eq_true_iff.mpr ⟨act r hr c hc,pin⟩⟩,rfl⟩⟩
  have hit := List.all_eq_true.mp (checks ⟨j,jl⟩ ⟨i,ih⟩) _ (Short.prune_kept kept agree 10 _ (by dsimp; omega)
    _ (by dsimp; omega))
  change bandMask (X (6+3*j) (3*(1+j+i))).1=true at hit
  rwa [sq,show R+(6+3*j)=1+3*(y+1+j) by dsimp [R]; omega,
    show C+3*(1+j+i)=1+3*(a+1+j+i) by dsimp [C]; omega] at hit

private theorem grow {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a g : Nat} (yl : 4≤y) (yh : y+3≤11+14*u) (al : 4≤a) (ah : a+6≤11+14*u)
    (gl : 4≤g) (gh : g≤a+3)
    (top : ∀ i, a ≤ i → i<11+14*u → TILE F w y i=73)
    (root : RootLine F w (11+14*u-1) y)
    (seed : ∀ i, g ≤ i → i<a+3 → bandMask (TILE F w (y+1) i)) :
    (∀ i, g+1 ≤ i → i<11+14*u → TILE F w (y+1) i=73) ∧ RootLine F w (11+14*u-1) (y+1) := by
  let k := 11+14*u
  have far := bands_below H acy one score hk (D:=1) yl al (by omega) top 1 le_rfl
  have row : BandRow (TILE F w) (y+1) g k := by
    intro i lo hi
    by_cases right : a+3 ≤ i
    · exact far i (by omega) hi
    · apply physical_pair H acy score hk (by omega) (by omega) (by omega) hi
      · exact seed _ lo (by omega)
      · by_cases e : i+1<a+3
        · exact seed _ (by omega) e
        · exact band_left_mask (far (i+1) (by omega) (by omega))
  have m := top (k-1) (by dsimp [k]; omega) (by dsimp [k]; omega)
  have line := SouthCap.Strip.GridScan.Rooted.extend_line (y:=y) root
    (by rw [m]; decide) (.inl (by rw [m]; decide))
  have out := rigid H acy one score hk (by omega) (by omega) gl (by omega) row line
  refine ⟨?_,line⟩
  intro i l h
  rcases out i (by omega) h with m|⟨e,_⟩
  · exact m
  · omega

/-- Two dangling tips replace the assumption of straight masks across
an entire movement window. Four plain buffer columns pay for two rows;
the output carries seals and roots for the next application. -/
theorem advance {u q F P w} (S : Short.Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (Q : Flow F) {y a : Nat} (yl : 5≤y) (yh : y+10≤11+14*u)
    (al : 4≤a) (ah : a+10≤11+14*u) (dang : a+2≤q) (born : (q:Int)-a+3≤1+3*(y:Int))
    (front : Front F w q (11+14*u) y a)
    (prev : ∀ i, a ≤ i → i<11+14*u → TILE F w (y-1) i=73) :
    Front F w q (11+14*u) (y+2) (a+4) ∧
      ∀ i, a+4 ≤ i → i<11+14*u → TILE F w (y+1) i=73 := by
  let k := 11+14*u
  have fit := S.room
  have local' := @local_masks u q F w P S acy Q y a yl yh al ah dang born front prev
  have east := front.2.2 (k-1) (by dsimp [k]; omega) (by dsimp [k]; omega) (by dsimp [k]; omega)
  have first := grow H acy one score hk (g:=a+1) (by omega) (by omega) al (by omega)
    (by omega) (by omega) (front.1 y le_rfl le_rfl) east (by
      intro i lo hi
      simpa only [Nat.add_zero,show a+1+(i-(a+1))=i by omega] using
        local' (j:=0) (i:=i-(a+1)) (by decide) (by omega))
  have second := grow H acy one score hk (g:=a+2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) first.1 first.2 (by
      intro i lo hi
      simpa only [show a+1+1+(i-(a+2))=i by omega] using
        local' (j:=1) (i:=i-(a+2)) (by decide) (by omega))
  have pl : Plateau F w y (y+2) (a+3) k := by
    intro r rl rh i lo hi
    rcases (show r=y ∨ r=y+1 ∨ r=y+2 by omega) with rfl|rfl|rfl
    · exact front.1 _ le_rfl le_rfl _ (by omega) hi
    · exact first.1 _ (by omega) hi
    · exact second.1 _ lo hi
  exact ⟨advance_front F w (by omega) (by omega) (by omega)
    (fun t st rt => by omega) front pl,fun i l h => first.1 i (by omega) h⟩

/-- Exhaust a move budget by induction, without certifying any
individual depth. The cut stays no farther east than the first root. -/
theorem exclude_run {u q F P w} (S : Short.Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (Q : Flow F) {y a s : Nat} (yl : 5≤y)
    (al : 4≤a) (budget : a+4*s≤q+1) (height : y+2*s+8≤11+14*u)
    (width : q+1+8≤11+14*u) (born : (q:Int)-a+3≤1+3*(y:Int))
    (front : Front F w q (11+14*u) y a)
    (prev : ∀ i, a ≤ i → i<11+14*u → TILE F w (y-1) i=73)
    (slope : 3*(11+14*u-(y+2*s))≤4*(11+14*u-(q+1))) : False := by
  let k := 11+14*u
  have states (j : Nat) (bound : j ≤ s) :
      Front F w q k (y+2*j) (a+4*j) ∧
        ∀ i, a+4*j ≤ i → i<k → TILE F w (y+2*j-1) i=73 := by
    induction j with
    | zero => exact ⟨front,prev⟩
    | succ j ih =>
      obtain ⟨cur,last⟩ := ih (by omega)
      have m := advance S H acy one score hk Q (by omega) (by omega)
        (by omega) (by omega) (by omega) (by push_cast; omega) cur last
      simpa only [show y+2*(j+1)=y+2*j+2 by omega,show a+4*(j+1)=a+4*j+4 by omega,
        show y+2*j+2-1=y+2*j+1 by omega] using m
  have endF := (states s le_rfl).1
  apply SouthCap.Strip.GridScan.Rooted.Mixed.exclude_suffix H acy one score hk (y+2*s) (q+1)
    (by omega) (by omega) height width slope
  intro i l h
  exact ⟨.inl (endF.1 _ le_rfl le_rfl _ (by omega) h),endF.2.2 _ (by omega) h (by omega)⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SlowBand
