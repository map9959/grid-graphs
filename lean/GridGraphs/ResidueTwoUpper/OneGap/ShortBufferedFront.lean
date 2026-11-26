import GridGraphs.ResidueTwoUpper.OneGap.DepthNineTransfer
import GridGraphs.ResidueTwoUpper.OneGap.CornerDrift

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero Stencil L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

@[noinline] private def rowFour (A : Board) :=
  decide (∀ w : View, wideFixed 96 (wideGrid A w 96 6 25) w 4 15)
private theorem rowFour_checked : rowFour (cached 3 chart) := by native_decide

@[noinline] private def rowFive (A : Board) :=
  decide (∀ w : View, wideFixed 120 (wideGrid A w 120 6 32) w 5 19)
private theorem rowFive_checked : rowFive (cached 3 chart) := by native_decide

/-- A translated tooth west of the roots pays for four-row blocks and
two single rows; the roots themselves remain at their physical columns. -/
theorem from_buffer {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (left : 28≤q) (room : q+17≤11+14*u)
    {r a s : Nat} (rows : 4≤r ∧ r≤8) (al : 5≤a) (budget : a+3*s+2=q+1)
    (height : r+4*s+4≤11+14*u) (first : square F w (1+3*r) (1+3*a)=73) :
    Front F w q (11+14*u) (r+4*s+2) (q+1) := by
  have grow (n : Nat) (h : a+n<11+14*u) :
      square F w (1+3*r) (1+3*(a+n))=73 := by
    induction n with
    | zero => exact first
    | succ n ih =>
      apply east_step u q r (a+n) (by omega) (by omega) (by omega) F acy w P S.step S.clean
      · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero
      · exact ih (by omega)
  have roots := suffix_from_sites S acy (y:=r) (e:=1) (by omega)
    (fun j lo hi => eight_sites S acy (by omega) room j lo (by omega)) hk (by omega) room
  have mid := CornerCone.blocks H acy one score hk (y:=r) (a:=a) (f:=q+1) (s:=s)
    rows.1 al (by omega) (by omega) (by omega) (by omega)
    (fun i lo hi => by
      have hit := grow (i-a) (by omega)
      rwa [show a+(i-a)=i by omega] at hit) (fun i lo hi => (roots i lo hi).2)
  have out := CornerCone.cone H acy one score hk (D:=2) (by omega) (by omega)
    (by omega) (by omega) (by omega) mid.1 mid.2 (by omega) 2 le_rfl
  exact ⟨fun j lo hi i il ih => by rw [show j=r+4*s+2 by omega]; exact out.1 i (by omega) ih,
    fun _ lo _ hi => by omega,fun i il ih _ => out.2 i il ih⟩

theorem buffered_front {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (left : 28≤q) (room : q+17≤11+14*u) :
    Front F w q (11+14*u) 18 (q+1) := by
  let v := q-25
  have eq : v+25=q := by dsimp [v]; omega
  apply from_buffer S H acy one score hk left room (r:=4) (a:=v+15) (s:=3)
    (by decide) (by omega) (by omega) (by omega)
  exact read_crop 32 (s:=6) (d:=25) (eq ▸ S : Seed F P w (v+25)) acy
    (.inr ⟨by dsimp [v]; omega,by decide⟩) (by decide) (by omega) (by decide) (by decide)
    (of_decide_eq_true rowFour_checked w)

theorem buffered_front_five {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (left : 35≤q) (room : q+17≤11+14*u) :
    Front F w q (11+14*u) 23 (q+1) := by
  let v := q-32
  have eq : v+32=q := by dsimp [v]; omega
  apply from_buffer S H acy one score hk (by omega) room (r:=5) (a:=v+19) (s:=4)
    (by decide) (by omega) (by omega) (by omega)
  exact read_crop 40 (s:=6) (d:=32) (eq ▸ S : Seed F P w (v+32)) acy
    (.inr ⟨by dsimp [v]; omega,by decide⟩) (by decide) (by omega) (by decide) (by decide)
    (of_decide_eq_true rowFive_checked w)

def bufferedRoom (u q : Nat) : Prop :=
  53≤11+14*u ∧ 28≤q ∧ q+17≤11+14*u ∧
    (4*(q+1)≤11+14*u+54 ∨ 35≤q ∧ 4*(q+1)≤11+14*u+69)
instance (u q) : Decidable (bufferedRoom u q) := by unfold bufferedRoom; infer_instance

theorem exclude_buffered {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : bufferedRoom u q) : False := by
  obtain ⟨hk,left,room,width⟩ := ok
  obtain ⟨y,yl,yh,slope,fr⟩ : ∃ y, 4≤y ∧ y+8≤11+14*u ∧ 4*(q+1)≤11+14*u+3*y ∧
      Front F w q (11+14*u) y (q+1) := by
    rcases width with h|⟨l,h⟩
    · exact ⟨18,by decide,by omega,h,buffered_front S H acy one score hk left room⟩
    · exact ⟨23,by decide,by omega,h,buffered_front_five S H acy one score hk l room⟩
  apply Mixed.exclude_suffix H acy one score hk y (q+1) yl (by omega) yh (by omega) (by omega)
  exact fun i lo hi => ⟨.inl (fr.1 _ le_rfl le_rfl i lo hi),fr.2.2 i lo hi (by omega)⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
