import GridGraphs.ResidueTwoUpper.OneGap.ShortSync
import GridGraphs.ResidueTwoUpper.OneGap.ShortCache

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7 ResidueZero Stencil

private theorem close_ends (u r c : Nat) :
    let b := syncBase u; let t := syncPos u r c
    (t.1<7 ↔ r<7) ∧ (r<7 → t.1=r) ∧
      (26+42*b≤t.1 ↔ 26+42*u≤r) ∧ (26+42*u≤r → t.1+pad u=r) ∧
    (t.2<7 ↔ c<7) ∧ (c<7 → t.2=c) ∧
      (26+42*b≤t.2 ↔ 26+42*u≤c) ∧ (26+42*u≤c → t.2+pad u=c) := by
  have size := sync_sizes u
  have bal : westPad (pad u) r≤pad u := by unfold westPad; omega
  dsimp only [syncPos]; refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (unfold fold12 ry; split_ifs <;> omega)
    | (dsimp [syncCol,foldAt,lx,ex]; split_ifs <;> omega)

theorem sync_tags (u r c : Nat) :
    let t := syncPos u r c
    tag (syncBase u) t.1=tag u r ∧ tag (syncBase u) t.2=tag u c := by
  obtain ⟨a,b,c',d,e,f,g,h⟩ := close_ends u r c
  obtain ⟨pr,pc⟩ := sync_phase u r c
  have sz := sync_sizes u
  dsimp only at *
  constructor <;> unfold tag <;> split_ifs <;> omega

private theorem raw_at {u r c} (hr : r<33+42*u) (hc : c<33+42*u) :
    atRC (cached u chart) r c = (atRC chart (tag u r) (tag u c)).filter fun z =>
      frameOK (35+42*u) r c z.1 && wallOK (35+42*u) r c z.1 z.2 := at_build hr hc _

/-- All synchronized visits have the correct 9-bit patch and 5-bit
star catalogue, including the southern and eastern fringes. -/
theorem sync_raw (u r c : Nat) :
    let t := syncPos u r c
    atRC chart (tag (syncBase u) t.1) (tag (syncBase u) t.2)=
      atRC chart (tag u r) (tag u c) := by
  simp only [(sync_tags u r c).1,(sync_tags u r c).2]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
