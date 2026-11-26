import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayExec

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

def memBank (D : Bank) : Domains := fun r c w => w∈D r c

def localCell {H W : Nat} (s : Window H W) (r c : Nat) : Option (Nat × Nat) :=
  let (j,i) := match s.axis with
    | .horizontal => (c,r)
    | .vertical => (r,c)
  if s.start ≤ i ∧ i+2 ≤ s.start+s.depth ∧ j+2 ≤ s.length then some (j,i-s.start)
  else none

theorem localCell_spec {H W : Nat} (s : Window H W) (r c j i : Nat) :
    localCell s r c=some (j,i) ↔
      j+2 ≤ s.length ∧ i+2 ≤ s.depth ∧ cell s.axis s.start j i=(r,c) := by
  cases ax : s.axis <;>
    simp [localCell,cell,ax,Prod.ext_iff] <;> omega

def updateBank {h : Nat} (z : Update h) (D : Bank) : Bank :=
  fun r c => match localCell z.window r c with
  | none => D r c
  | some (j,i) => acceptedWords z D j i

/-- A computed domain update is a sound over-approximation to the
semantic projection. In particular it cannot delete a physical
plaquette that survives the checked packed trace. -/
theorem updateBank_sound {h : Nat} (z : Update h) {D : Bank} (l : 2≤z.window.length) :
    ∀ r c w, z.replay (memBank D) r c w → w∈updateBank z D r c := by
  classical
  intro r c w survive
  unfold Update.replay Window.prune at survive
  unfold updateBank
  split
  · rename_i none
    have outside : ¬z.window.Inside r c := by
      rintro ⟨j,i,hj,hi,eq⟩
      have atCell := (localCell_spec z.window r c j i).mpr ⟨hj,hi,eq⟩
      rw [none] at atCell
      contradiction
    simpa only [if_neg outside,memBank] using survive
  · rename_i j i atCell
    obtain ⟨hj,hi,eq⟩ := (localCell_spec z.window r c j i).mp atCell
    rw [if_pos (show z.window.Inside r c from ⟨j,i,hj,hi,eq⟩)] at survive
    obtain ⟨b,consistent,trace,a,k,ha,hk,cellEq,wordEq⟩ := survive
    have indices : (a,k)=(j,i) := Option.some.inj
      (((localCell_spec z.window r c a k).mpr ⟨ha,hk,cellEq⟩).symm.trans atCell)
    cases indices
    rw [←wordEq]
    exact acceptedWords_cover z D b l consistent trace j i hj hi

theorem replay_mono {h : Nat} (z : Update h) {A B : Domains}
    (le : ∀ r c w, A r c w → B r c w) :
    ∀ r c w, z.replay A r c w → z.replay B r c w := by
  classical
  intro r c w
  unfold Update.replay Window.prune
  split
  · rintro ⟨b,h,tr,loc⟩
    exact ⟨b,fun j i hj hi => le _ _ _ (h j i hj hi),tr,loc⟩
  · exact le r c w

theorem length_ge2 {h : Nat} (lo : 14≤h) (s : Window h (width h)) :
    2 ≤ s.length := by
  cases ax : s.axis <;> simp [Window.length,ax,width]
  all_goals omega

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
