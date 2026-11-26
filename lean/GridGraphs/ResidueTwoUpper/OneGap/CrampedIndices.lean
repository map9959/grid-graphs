import GridGraphs.ResidueTwoUpper.OneGap.CrampedTransfer
import GridGraphs.ResidueTwoUpper.OneGap.DepthNineTransfer

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.Cramped
open ResidueZero L7 FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

def fits (u q : Nat) : Bool :=
  decide (3≤u ∧ u≤18 ∧ q%2=1 ∧ q<57 ∧ q+2≤11+14*u ∧ 11+14*u+3<4*(max 3 (q+1)+12))

def indices : List (Nat × Nat) :=
  (List.range 19).flatMap fun u => ((List.range 57).filter (fits u)).map (u,·)

theorem mem_indices {u q : Nat} : (u,q)∈indices ↔ fits u q=true := by
  simp only [indices,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,
    Prod.mk.injEq,fits,decide_eq_true_eq]; grind

theorem indices_count : indices.length=227 ∧ indices.Nodup := by native_decide

/-- All threshold pairs below have the actual north suffix long enough
for the one-pass *finite* south test (including a pair on side 161).
The list is independent of the eight possible views. -/
def passed : List (Nat × Nat) :=
  [(3,1),(3,3),(3,5),(3,7),(3,9),(4,5),(4,7),(5,9),(6,13),(7,17),(8,19),(8,21),(9,23),(10,27),
   (11,31),(12,33),(12,35),(13,37),(14,41),(15,45),(16,47),(16,49),(17,51),(18,55)]

private def start (u q : Nat) := if u=3 ∧ (q=5 ∨ q=7 ∨ q=9) then 16 else max 3 (q+1)+12

private def check (p : Nat × Nat) : Bool :=
  let (u,q) := p
  let k := 11+14*u
  let f := start u q
  fits u q && decide (4≤f ∧ q<f ∧ f+4≤k) && FiniteTransfer.rejects (k-4) (k-f)

private theorem checked : passed.all check=true := by native_decide

theorem exclude_passed {u q F v P} (mem : (u,q)∈passed)
    (S : Seed (u:=u) F P v q) (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) : False := by
  let k := 11+14*u
  let f := start u q
  have ck := List.all_eq_true.mp checked _ mem
  change (fits u q && decide (4≤f ∧ q<f ∧ f+4≤k) && FiniteTransfer.rejects (k-4) (k-f))=true at ck
  simp only [Bool.and_eq_true,decide_eq_true_eq,fits] at ck
  obtain ⟨⟨⟨lo,_,_,_,_,_⟩,fl,feet,room⟩,reject⟩ := ck
  have front : Front F v q k 4 f := by
    by_cases special : u=3 ∧ (q=5 ∨ q=7 ∨ q=9)
    · obtain ⟨rfl,rfl|rfl|rfl⟩ := special
      · exact North.five_front S acy
      · exact North.seven_front S acy
      · exact North.nine_front S acy
    · simp only [f,start,if_neg special] at room ⊢
      exact North.front S acy (by dsimp [k] at room; omega)
  have words := physical_rim_bank H acy one score (by omega) 4 f le_rfl fl
    (by dsimp [k] at room; omega) (fun i low up => ⟨front.1 _ le_rfl le_rfl i low up,
      front.2.2 i low up (by omega)⟩)
  have no := FiniteTransfer.sound (k-4) (k-f) (by dsimp [k]; omega) (by omega) _ words
  rw [no] at reject
  contradiction

def translatedRoom (u q : Nat) : Prop :=
  53≤11+14*u ∧ 6≤q ∧ q+17≤11+14*u ∧ 4*(q+5)≤11+14*u+12

instance (u q : Nat) : Decidable (translatedRoom u q) := by unfold translatedRoom; infer_instance

/-- A size-independent cut, also valid for long indices. -/
theorem exclude_translated {u q F w P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (fit : translatedRoom u q) : False := by
  obtain ⟨hk,lo,room,wide⟩ := fit
  let v := q-3
  have eq : v+3=q := by dsimp [v]; omega
  have crops := North.translated_mixed (v:=v) (eq ▸ S : Seed F P w (v+3)) acy
    (by dsimp [v]; omega) (by omega)
  apply Mixed.exclude_suffix H acy one score hk 4 (v+8) le_rfl (by omega)
    (by omega) (by omega) (by omega)
  intro i l h
  refine ⟨(crops 4 (by decide) le_rfl i l h).imp_right And.right,?_⟩
  apply North.line_from_three S (by omega) h
  intro j jl jh
  rcases crops j jl (by omega) i l h with m|⟨e,_⟩
  · exact m
  · omega

def deeperRoom (u q : Nat) : Prop :=
  let k := 11+14*u
  53≤k ∧ q+17≤k ∧
    ((12≤q ∧ 4*(q+3)≤k+15) ∨ (15≤q ∧ 4*(q+1)≤k+15) ∨ (15≤q ∧ 4*(q+2)≤k+18))

instance (u q : Nat) : Decidable (deeperRoom u q) := by unfold deeperRoom; infer_instance

theorem exclude_deeper {u q F w P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (fit : deeperRoom u q) : False := by
  obtain ⟨hk,room,a|b|c⟩ := fit
  · exact North.Deep.exclude S H acy one score (d:=9) (y:=5) (e:=3) (.inl ⟨rfl,rfl,rfl⟩) hk a.1 room a.2
  · exact North.Deep.exclude S H acy one score (d:=12) (y:=5) (e:=1) (.inr (.inl ⟨rfl,rfl,rfl⟩)) hk b.1 room b.2
  · exact North.Deep.exclude S H acy one score (d:=12) (y:=6) (e:=2) (.inr (.inr ⟨rfl,rfl,rfl⟩)) hk c.1 room c.2

/-- Shallowest row at which the slope can work for a suffix strictly
east of the isolate, taking its most favorable starting column `q+1`.
Physical height and width margins are additional requirements. -/
def neededDepth (u q : Nat) := max 4 ((4*(q+1)+2-(11+14*u))/3)

theorem neededDepth_le {u q y : Nat} : neededDepth u q ≤ y ↔
    4≤y ∧ 4*(q+1)≤11+14*u+3*y := by unfold neededDepth; omega

def beforeSix := indices.filter fun p =>
  !(passed.contains p || decide (translatedRoom p.1 p.2) || decide (deeperRoom p.1 p.2))

def depthGroup (y : Nat) := beforeSix.filter fun p => neededDepth p.1 p.2 == y

theorem mem_depthGroup {p y} : p∈depthGroup y ↔ p∈beforeSix ∧ neededDepth p.1 p.2=y := by
  simp [depthGroup]

theorem firstDepthGroup : beforeSix.length=121 ∧
    beforeSix.all (fun p => decide (6≤neededDepth p.1 p.2)) ∧
    depthGroup 6=[(6,27),(10,41),(14,55)] := by native_decide

def sixRoom (u q : Nat) : Prop :=
  53≤11+14*u ∧ 21≤q ∧ q+17≤11+14*u ∧ neededDepth u q≤6
instance (u q : Nat) : Decidable (sixRoom u q) := by unfold sixRoom; infer_instance

theorem exclude_sixRoom {u q F w P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (six : sixRoom u q) : False :=
  North.Deep.exclude_six S H acy one score six.1 six.2.1 six.2.2.1 (neededDepth_le.mp six.2.2.2).2

def sevenRoom (u q : Nat) : Prop :=
  53≤11+14*u ∧ (q=17 ∨ 21≤q) ∧ q+17≤11+14*u ∧ neededDepth u q≤7
instance (u q : Nat) : Decidable (sevenRoom u q) := by unfold sevenRoom; infer_instance

theorem exclude_sevenRoom {u q F w P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (seven : sevenRoom u q) : False :=
  North.Deep.exclude_seven S H acy one score seven.1 seven.2.1 seven.2.2.1 (neededDepth_le.mp seven.2.2.2).2

def eightRoom (u q : Nat) : Prop :=
  53≤11+14*u ∧ 25≤q ∧ q+17≤11+14*u ∧ neededDepth u q≤8
instance (u q : Nat) : Decidable (eightRoom u q) := by unfold eightRoom; infer_instance

theorem exclude_eightRoom {u q F w P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (eight : eightRoom u q) : False :=
  North.Deep.exclude_eight S H acy one score eight.1 eight.2.1 eight.2.2.1 (neededDepth_le.mp eight.2.2.2).2

def nineRoom (u q : Nat) : Prop :=
  53≤11+14*u ∧ (q=19 ∨ 29≤q) ∧ q+17≤11+14*u ∧ neededDepth u q≤9
instance (u q : Nat) : Decidable (nineRoom u q) := by unfold nineRoom; infer_instance

theorem exclude_nineRoom {u q F w P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (nine : nineRoom u q) : False :=
  North.Deep.exclude_nine S H acy one score nine.1 nine.2.1 nine.2.2.1 (neededDepth_le.mp nine.2.2.2).2

def pending := beforeSix.filter fun p => !decide (sevenRoom p.1 p.2 ∨ eightRoom p.1 p.2 ∨ nineRoom p.1 p.2)

theorem pending_count : pending.length=104 ∧ pending.Nodup := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.Cramped
