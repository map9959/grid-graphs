import GridGraphs.ResidueTwoUpper.OneGap.WestFanBase
import GridGraphs.ResidueTwoUpper.OneGap.DeepNorthSuffix
import GridGraphs.ResidueTwoUpper.OneGap.TrimmedCap

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
open ResidueZero L7 FanSlab Short BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan

private theorem translate {b x c : Nat} (h : x≤b) : edge (b-x) c=edge b (x+c) := by
  unfold edge; split_ifs <;> first | rfl | omega

theorem at_tile {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {seed L j z i b : Nat} (mode : Mode (seed==1) L j)
    (north : seed=1 → z=0) (bulk : seed≠1 → 2≤z) (loc : q+2=b+3*(z+j))
    (ib : i≤b) (strict : L=3 → i<b) (left : L+2 ≤ i)
    (fit : i+10≤11+14*u) (ht : z+8≤11+14*u)
    (prev : seed≠1 → ∀ a≤1, ∀ k≤L+8, maskAtTile F w (z+a) (i-L+k)=edge (b+(6-3*a)) (i-L+k))
    (ahead : i<b → ∀ c, i < c → c ≤ i+8 → maskAtTile F w (z+j) c=edge b c) :
    maskAtTile F w (z+j) i=edge b i := by
  let x := i-L
  have l : x+L=i := by dsimp [x]; omega
  have res := tile_step S acy mode north bulk (x:=x) (B:=b-x) (by omega) (by omega)
    (fun e => by have := strict e; omega) (by omega) (by omega) ht (by
      intro sn a ha k kh; rw [prev sn a ha k kh]
      rw [show b-x+(6-3*a)=b+(6-3*a)-x by omega,translate (by omega)]) (by
      intro lt k kl kh; rw [translate (by omega)]; exact ahead (by omega) _ (by omega) (by omega))
  rwa [translate (by omega),l] at res

set_option maxHeartbeats 1000000 in
/-- Across a short fan, the known interval starts three tiles further
east per row, while the first plain tile moves three tiles west. The
proof stops before the two interfaces touch. Only the base reads the
north seed; the inductive step uses the two previous physical rows. -/
theorem rows_restart {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {d : Nat} (pad : d=4 ∨ (d=1 ∧ 35≤q))
    {start : Nat} (room : q+11≤11+14*u ∨ q+12≤11+14*u+3*start)
    (earlier : ∀ r, 2≤r → r<start → 6*r+d≤q+1 → ∀ i, 3*r+d ≤ i → i<11+14*u →
      maskAtTile F w r i=edge (q+2-3*r) i)
    (y : Nat) (yl : 2≤y) (openFan : 6*y+d≤q+1) :
    ∀ i, 3*y+d ≤ i → i<11+14*u → maskAtTile F w y i=edge (q+2-3*y) i := by
  induction y using Nat.strong_induction_on with
  | h y ih =>
    by_cases prior : y<start
    · exact earlier y yl prior openFan
    have fit := S.room
    let b := q+2-3*y
    have loc : q+2=b+3*y := by dsimp [b]; omega
    have step (i : Nat) (lo : 3*y+d ≤ i) (hi : i≤b)
        (ahead : i<b → ∀ c, i < c → c ≤ i+8 → maskAtTile F w y c=edge b c) :
        maskAtTile F w y i=edge b i := by
      by_cases west : (y=2 ∨ y=3) ∧ i<3*y+4
      · rw [west_base S acy (by omega) west.1 (by omega) west.2]
        unfold edge; rw [if_pos (by dsimp [b]; omega)]
      by_cases two : y=2
      · subst y
        exact at_tile S acy (i:=i) (b:=b) (L:=8) (j:=2) (z:=0) (seed:=1) .seedTwo (by simp) (by simp)
          loc hi (by intro h; omega) (by omega) (by omega) (by omega) (by simp) ahead
      by_cases three : y=3
      · subst y
        exact at_tile S acy (i:=i) (b:=b) (L:=11) (j:=3) (z:=0) (seed:=1) .seedThree (by simp) (by simp)
          loc hi (by intro h; omega) (by omega) (by omega) (by omega) (by simp) ahead
      let z := y-2
      have eq : z+2=y := by dsimp [z]; omega
      have run {L : Nat} (m : Mode false L 2) (limit : L≤4)
          (extra : 3*(z+1)+d ≤ i-L) (strict : L=3 → i<b) := at_tile S acy (i:=i) (b:=b) (L:=L) (z:=z)
        (seed:=0) (j:=2) m (by simp) (by dsimp [z]; omega)
        (by omega : q+2=b+3*(z+2)) hi strict (by omega) (by omega) (by omega) (by
          intro _ a ha k kh
          have old := ih (z+a) (by omega) (by dsimp [z]; omega) (by omega)
            (i-L+k) (by omega) (by omega)
          rw [show q+2-3*(z+a)=b+(6-3*a) by omega] at old
          exact old) (eq ▸ ahead)
      by_cases atEnd : i=b
      · exact eq ▸ run .boundary (by decide) (by omega) (by intro h; omega)
      · exact eq ▸ run .interior (by decide) (by omega) (by omega)
    have first := step b (by omega) le_rfl (by omega)
    have plain (i : Nat) (low : b ≤ i) (hi : i<11+14*u) : maskAtTile F w y i=73 := by
      induction i,low using Nat.le_induction with
      | base => simpa [edge] using first
      | succ i low prev =>
        apply east_step u q y i (by omega) (by omega) (by omega) F acy w P S.step S.clean
        · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero
        · exact prev (by omega)
    intro i lo hi
    change maskAtTile F w y i=edge b i
    induction d : b-i using Nat.strong_induction_on generalizing i with
    | h d back =>
      by_cases east : b ≤ i
      · rw [plain _ east hi]; unfold edge; split_ifs <;> omega
      apply step _ lo (by omega)
      intro _ c ic cl
      by_cases inside : c<b
      · exact back (b-c) (by omega) c (by omega) (by omega) rfl
      · rw [plain _ (by omega) (by omega)]; unfold edge; split_ifs <;> omega

theorem rows_from {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {d : Nat} (pad : d=4 ∨ (d=1 ∧ 35≤q))
    (room : q+11≤11+14*u) (y : Nat) (yl : 2≤y) (openFan : 6*y+d≤q+1) :
    ∀ i, 3*y+d ≤ i → i<11+14*u → maskAtTile F w y i=edge (q+2-3*y) i :=
  rows_restart S acy pad (start:=0) (.inl room) (by intro r _ hr; omega) y yl openFan

theorem rows {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (room : q+11≤11+14*u) (y : Nat) (yl : 2≤y) (openFan : 6*y+3≤q) :
    ∀ i, 3*y+4 ≤ i → i<11+14*u → maskAtTile F w y i=edge (q+2-3*y) i :=
  rows_from S acy (.inl rfl) room y yl (by omega)

theorem last_line {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {y : Nat} (_hk : 53≤11+14*u) (room : q+17≤11+14*u) (yl : 3≤y) (openFan : 6*y+3≤q) :
    RootLine F w (11+14*u-1) (y+1) := by
  let k := 11+14*u
  have ray (r : Nat) (rl : 2≤r) (rh : r≤y) (i : Nat) (lo : q+2-3*r ≤ i) (hi : i<k) :
      maskAtTile F w r i=73 := by
    rw [rows S acy (by omega) r rl (by omega) i (by omega) hi]; unfold edge; split_ifs <;> omega
  have line (r : Nat) (rl : 3≤r) (rh : r≤y) : RootLine F w (k-1) (r+1) := by
    induction r,rl using Nat.le_induction with
    | base =>
      apply Short.North.line_from_three S (by dsimp [k]; omega) (by dsimp [k]; omega)
      intro j lo hi
      exact Short.North.plateau S acy (by omega) j lo (by omega) _ (by dsimp [k]; omega) (by dsimp [k]; omega)
    | succ r lo ih =>
      have tooth := ray (r+1) (by omega) rh (k-1) (by dsimp [k]; omega) (by dsimp [k]; omega)
      apply Rooted.extend_line (ih (by omega))
      · rw [show Rooted.tile F w (r+1) (k-1)=73 from tooth]; decide
      · left; rw [show Rooted.tile F w (r+1) (k-1)=73 from tooth]; decide
  exact line y yl le_rfl

theorem exclude_rows {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    {y : Nat} (hk : 53≤11+14*u) (room : q+17≤11+14*u) (yl : 4≤y) (openFan : 6*y+3≤q)
    (width : q+2-3*y+topWidth (11+14*u-y)≤11+14*u) : False := by
  apply trimmed_excludes_of_ge53 H acy one score hk yl (by omega) (by omega) width
  · intro i lo hi
    rw [show Rooted.tile F w y i=edge (q+2-3*y) i from rows S acy (by omega) y (by omega) openFan i (by omega) hi]
    unfold edge; split_ifs <;> omega
  · intro r hr; exact last_line S acy hk room (by omega) openFan r (by omega)

/-- Choose the deepest row before the two proven boundary cones meet. -/
def capRoom (u q : Nat) : Prop :=
  let k := 11+14*u; let y := (q-3)/6
  53≤k ∧ 4≤y ∧ q+17≤k ∧ q+2-3*y+topWidth (k-y)≤k
instance (u q) : Decidable (capRoom u q) := by unfold capRoom; infer_instance

theorem exclude_room {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : capRoom u q) : False := by
  obtain ⟨hk,yl,room,width⟩ := ok
  exact exclude_rows S H acy one score hk room yl (by omega) width
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
