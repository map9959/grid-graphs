import GridGraphs.ResidueTwoUpper.OneGap.NestedCap
import GridGraphs.ResidueTwoUpper.OneGap.TrimmedCap
import GridGraphs.ResidueTwoUpper.OneGap.CollisionReach
import GridGraphs.ResidueTwoUpper.OneGap.CompactWindowChecks
import GridGraphs.ResidueTwoUpper.OneGap.FarDanglingMove

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Guarded
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan

/-- Sizes count plaquettes, not physical sites. The three extra
columns per increment of `a` pay for seven more rows of transfer. -/
private def sizes := [1,2,3,4,5,6,7,8]
private def W (a : Nat) := 3*a+1
private def D (a : Nat) := if a=5 ∨ 7≤a then 7*a else 7*a+5
private def s (a : Nat) := 7*a-1
private theorem checked {a} (ha : a∈sizes) : ∃ rounds, test (W a) (D a) (3*a) (s a) rounds true := by
  simp [sizes] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,tiny_test⟩
  · exact ⟨_,short_test⟩
  · exact ⟨_,medium_test⟩
  · exact ⟨_,long_test⟩
  · exact ⟨_,compact_bridge⟩
  · exact ⟨_,middle_test⟩
  · exact ⟨_,compact_extended⟩
  · exact ⟨_,far_test⟩

private theorem cover35 : RestartCover 10 20 35 := by
  intro j jl jh
  by_cases early : j≤27
  · left; dsimp [coneCost]; omega
  · exact .inr ⟨_,_,_,_,_,medium_test,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩

/-- One cover works for both of the largest moves. Every restart reads
strictly above the putative failure and uses only dangling tips. -/
private theorem cover49 {h : Nat} (height : h≤49) : RestartCover 19 24 h := by
  intro j jl jh
  by_cases early : j≤33
  · left; dsimp [coneCost]; omega
  by_cases first : j≤40
  · exact .inr ⟨_,_,_,_,_,long_test,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩
  by_cases second : j≤47
  · exact .inr ⟨_,_,_,_,_,bridge_test,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩
  · exact .inr ⟨_,_,_,_,_,middle_test,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩

private theorem cover56 : RestartCover 22 27 56 := by
  intro j jl jh
  by_cases before : j≤49
  · rcases cover49 (h:=49) le_rfl j jl before with cost|⟨w,d,b,s,r,ck,hs,hb,row,col,budget⟩
    · exact .inl (by omega)
    · exact .inr ⟨w,d,b,s,r,ck,hs,hb,row,by omega,by omega⟩
  · exact .inr ⟨_,_,_,_,_,compact_extended,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩

def endFits (k h f : Nat) : Prop := 14≤h ∧ f-1+topWidth h≤k
private instance (k h f) : Decidable (endFits k h f) := by unfold endFits; infer_instance
private def stepFits (k q h f a : Nat) : Prop :=
  D a+8≤h ∧ f+W a≤q ∧ f+W a+8≤k ∧
  f+(if a=8 then 34 else if a=5 then 27 else if 6≤a then 31 else coneCost (D a-1)+8)≤k
private instance (k q h f a) : Decidable (stepFits k q h f a) := by unfold stepFits; infer_instance
private def search (k q : Nat) : Nat → Nat → Nat → Bool
  | 0,h,f => decide (endFits k h f)
  | n+1,h,f => decide (endFits k h f) || sizes.any fun a =>
      decide (stepFits k q h f a) && search k q n (h-s a) (f+W a)

private def starts (q : Nat) :=
  let Y := (q-15)/6
  (List.range (CollisionWide.reach (q-6*Y)-1)).map (·+2)

def fits (k q : Nat) : Bool :=
  let Y := (q-15)/6
  (starts q).any fun z => search k q (k/6) (k-(Y+z)) (q-3*Y+3)

/-- All previously capacity-feasible long indices now have actual
schedules, with both the dangling-tip and physical width tests enabled. -/
theorem compact_routes_checked : [(4,57),(5,65),(5,67),(5,71),(5,73),(5,75),
    (6,89),(6,93),(7,107)].all (fun (u,q) => fits (11+14*u) q) := by native_decide

/-- Ignore every window-placement constraint. A path with `t` moves
and sum `A` of size indices necessarily consumes `7*A-t` rows and
`3*A+t` columns. Failure here cannot be repaired by loosening a
width test or by changing the order of these same moves. -/
def capacity (k h f : Nat) : Bool :=
  (List.range (h/6+1)).any fun t => (List.range (8*t+1)).any fun A =>
    decide (t≤A ∧ 7*A≤h+t ∧ endFits k (h+t-7*A) (f+3*A+t))

private theorem totals {k q n h f} (path : search k q n h f) :
    ∃ t A, t≤A ∧ A≤8*t ∧ 7*A≤h+t ∧ endFits k (h+t-7*A) (f+3*A+t) := by
  have stop (cap : endFits k h f) : ∃ t A, t≤A ∧ A≤8*t ∧ 7*A≤h+t ∧
      endFits k (h+t-7*A) (f+3*A+t) := ⟨0,0,by decide,by decide,by omega,by simpa using cap⟩
  induction n generalizing h f with
  | zero => exact stop (of_decide_eq_true path)
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp path with hit|steps
    · exact stop (of_decide_eq_true hit)
    obtain ⟨a,ha,p⟩ := List.any_eq_true.mp steps
    obtain ⟨fit,more⟩ := Bool.and_eq_true_iff.mp p
    obtain ⟨hr,_,_,_⟩ := of_decide_eq_true fit
    have size : 1≤a ∧ a≤8 := by simp [sizes] at ha; omega
    obtain ⟨t,A,low,hi,room,cap⟩ := ih more (fun cap => ⟨0,0,by decide,by decide,by omega,by simpa using cap⟩)
    refine ⟨t+1,A+a,by omega,by omega,?_,?_⟩
    · dsimp [s] at room; dsimp [D] at hr; split at hr <;> omega
    · convert cap using 1 <;> dsimp [s,W,D] at * <;> omega

def hasCapacity (k q : Nat) :=
  let Y := (q-15)/6
  (starts q).any fun z => capacity k (k-(Y+z)) (q-3*Y+3)

theorem capacity_of_fits {k q} (ok : fits k q) : hasCapacity k q := by
  obtain ⟨z,mem,path⟩ := List.any_eq_true.mp ok
  obtain ⟨t,A,lo,hi,room,cap⟩ := totals path
  apply List.any_eq_true.mpr; refine ⟨z,mem,?_⟩
  exact List.any_eq_true.mpr ⟨t,List.mem_range.mpr (by omega),List.any_eq_true.mpr
    ⟨A,List.mem_range.mpr (by omega),decide_eq_true ⟨lo,room,cap⟩⟩⟩

/-- Sound for every successful sequence: the search chooses dimensions
only. Induction transports both the front and its western guard on the
same physical square, including at the last (cap) read. -/
theorem exclude_from_cut {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (size : 53≤11+14*u) (feet : q+2≤11+14*u)
    {y f n} (ok : search (11+14*u) q n (11+14*u-y) f) (yl : 4≤y) (fl : 7≤f)
    (birth : (q:Int)-f+3≤3*(y:Int)) (fr : Front F v q (11+14*u) y f)
    (pl : endFits (11+14*u) (11+14*u-y) f → Plateau F v y y (f-1) (11+14*u)) : False := by
  let k := 11+14*u
  have hk : 53≤k := size
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have price := prices_of_seed u q F acy v H.parent H.step H.patches H.stars
  have stop {y f} (yl : 4≤y) (fl : 7≤f) (front : Front F v q k y f) (plain : Plateau F v y y (f-1) k)
      (cap : endFits k (k-y) f) : False := by
      obtain ⟨lo,pad⟩ := cap
      exact trimmed_excludes_of_ge53 H acy one score hk yl (by omega) (by omega) pad
        (plain _ le_rfl le_rfl) (front.2.2 _ (by dsimp [topWidth] at pad; omega) (by omega) (by omega))
  have go (n y f : Nat) (path : search k q n (k-y) f) (yl : 4≤y) (fl : 7≤f)
      (birth : (q:Int)-f+3≤3*(y:Int)) (front : Front F v q k y f)
      (plain : endFits k (k-y) f → Plateau F v y y (f-1) k) : False := by
    induction n generalizing y f with
    | zero => exact stop yl fl front (plain (of_decide_eq_true path)) (of_decide_eq_true path)
    | succ n ih =>
      rcases Bool.or_eq_true_iff.mp path with end'|steps
      · exact stop yl fl front (plain (of_decide_eq_true end')) (of_decide_eq_true end')
      obtain ⟨a,ha,p⟩ := List.any_eq_true.mp steps
      obtain ⟨fit,more⟩ := Bool.and_eq_true_iff.mp p
      obtain ⟨hr,tip,wc,budget⟩ := of_decide_eq_true fit
      have pos : 1≤a := by simp [sizes] at ha; omega
      have st : Straight F v y f (W a) (D a) := by
        by_cases far : a=8
        · subst a
          change f+34≤k at budget; change f+25≤q at tip
          exact nested_window H acy one score hk Q feet front yl fl (by omega) budget
            (by omega) birth (by decide) (by decide) cover56
        rw [if_neg far] at budget
        by_cases bridge : a=5
        · subst a
          change f+27≤k at budget; change f+16≤q at tip
          exact nested_window H acy one score hk Q feet front yl fl (by omega) budget
            (by omega) birth (by decide) (by decide) cover35
        by_cases large : 6≤a
        · rw [if_neg bridge,if_pos large] at budget
          have lim : a≤7 := by simp [sizes] at ha; omega
          have height : D a≤49 := by dsimp [D]; split <;> omega
          apply nested_window H acy one score hk Q feet front yl fl (by omega) (E:=24) budget
            (L:=19) (by dsimp [W] at tip; omega) birth (by dsimp [W]; omega) (by decide) (cover49 height)
        · rw [if_neg bridge,if_neg large] at budget
          exact Departure.straight_of_room H acy one score (by omega) Q price front le_rfl yl fl
            (by omega) wc (by dsimp [coneCost] at budget; omega) feet
      obtain ⟨rounds,ck⟩ := checked ha
      have hand := physical_dangling_step_rect u q y f _ _ _ _ rounds ck
        (by dsimp [s,D,W]; split <;> omega) (by dsimp [k] at *; omega) tip (by omega)
        F acy v H.parent H.step H.patches H.stars Q st front
      have more' : search k q n (k-(y+s a)) (f+W a) := by
        rwa [show k-(y+s a)=k-y-s a by omega]
      apply ih (y+s a) (f+W a) more' (by omega) (by omega) (by push_cast; omega)
      · simpa only [W,Nat.add_assoc] using hand.1
      · intro _ r rl rh i il ih'
        exact hand.2 r (by omega) rh i (by dsimp [W] at il; omega) ih'
  exact go n y f ok yl fl birth fr pl

def atCut (k q y f : Nat) := search k q (k/6) (k-y) f

theorem exclude_from {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (size : 53≤11+14*u) (feet : q+2≤11+14*u)
    {y f n} (ok : search (11+14*u) q n (11+14*u-y) f) (yl : 4≤y) (fl : 7≤f)
    (birth : (q:Int)-f+3≤3*(y:Int)) (fr : Front F v q (11+14*u) y f)
    (pl : Plateau F v y y (f-1) (11+14*u)) : False :=
  exclude_from_cut H acy one score size feet ok yl fl birth fr (fun _ => pl)

theorem exclude {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (big : 57≤q) (feet : q+2≤11+14*u)
    (ok : fits (11+14*u) q) :
    let Y := (q-15)/6
    Front F v q (11+14*u) (Y+2) (q-3*Y+3) →
    Plateau F v (Y+2) (Y+CollisionWide.reach (q-6*Y)) (q-3*Y+2) (11+14*u) → False := by
  intro Y fr pl
  let k := 11+14*u
  obtain ⟨z,mem,path⟩ := List.any_eq_true.mp ok
  simp only [starts,List.mem_map,List.mem_range] at mem
  obtain ⟨j,jh,rfl⟩ := mem
  change j<CollisionWide.reach (q-6*Y)-1 at jh
  have cut : Plateau F v (Y+2) (Y+(j+2)) (q-3*Y+2) k :=
    fun r lo hi => pl r lo (by omega)
  have base := advance_front F v (by omega) le_rfl (by omega)
    (fun t st rt => by push_cast at *; omega) fr cut
  exact exclude_from H acy one score (by omega) feet (y:=Y+(j+2)) (f:=q-3*Y+3) path (by dsimp [Y]; omega) (by dsimp [Y]; omega)
    (by push_cast; dsimp [Y]; omega) base (fun r rl rh i il ih => cut r (by omega) rh i (by omega) ih)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Guarded
