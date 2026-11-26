import GridGraphs.ResidueTwoUpper.OneGap.FanArm
import GridGraphs.ResidueTwoUpper.OneGap.FanSeedPhysical
import GridGraphs.ResidueTwoUpper.OneGap.FanSeedScan

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7 GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected

/-- The tile in the physical frame, with rows inward and columns along
its side. The scan uses overlapping patches; the conclusions below use
aligned, disjoint tiles with origins congruent to (1,1) modulo 3. -/
def tile {n} (F : Finset (GridVertex n n)) (w : View) (r j : Nat) :=
  window (chartCol F w j) (chartCol F w (j+1)) (chartCol F w (j+2)) r

private theorem cross_empty (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (p : GridVertex (35+42*u) (35+42*u)) (w : View) (i : Nat) (hi : i+5≤33+42*u)
    (hp : coord p=L7.view w (35+42*(u:Int)) 2 ((i:Int)+1)) (nb : neighbours F (coord p)=0)
    (um : p∉F) : tile F w 1 i &&& 186=0 := by
  let a := onSite (s:=35+42*u-2) (L7.view w (33+42*(u:Int)) 1 i) (by
    rw [show 35+42*u-2=33+42*u by omega]
    exact_mod_cast inside_view (n:=33+42*u) (r:=1) (j:=i) w (by omega) (by omega))
  have ha : coord a=L7.view w (33+42*(u:Int)) 1 i := coord_onSite ..
  have ha' : coord a=L7.view w ((35+42*(u:Int))-2) 1 i := by rw [ha]; congr 2 <;> ring
  have center : coord p=coord a+(1,1) := by rw [ha',view_center,hp]; rfl
  obtain ⟨x,y⟩ := PatchFilter.packed_center F a p center
  rw [nb] at y; simp [um] at x
  have ver : ∀ v : View, ∀ m : Fin 512, bit m 4=0 → PatchFilter.cnb m=0 → encode m v &&& 186=0 := by native_decide
  unfold tile; rw [←window_encode u F w 1 i (by decide) a ha']
  exact ver _ _ x y

/-- The isolate is on the seed arm. Its fan tile is 64; every eastern
north tooth has tile 72 (6 after transposition), with its line continuing
into the next tile row. Even the final aligned tile is included. -/
theorem scored_seed (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (p : GridVertex n n) (w : View) (s f : Bool) (i : Nat),
      (∀ t,P t≠t → (Bonds F).Adj t (P t)) ∧ (∀ a,patchSlack F a=0) ∧
      (∀ t,t≠p → starSlack F P t=0) ∧ (Bonds F).IsIsolated p ∧ rim F w s f ∧ coord p=L7.view w n 2 ((i:Int)+1) ∧
      4≤ i ∧ i+5≤33+42*u ∧ i%6=4 ∧ tile F w 1 i=64 ∧
      ∀ j, i<j → j<33+42*u → j%3=1 → tile F w 1 j=72 ∧ lane (tile F w 4 j) 0=1 ∧
        (i+3<j → lane (tile F w 4 j) 3=1) := by
  obtain ⟨P,p,step,arr,good,iso,loc,full',zero⟩ := isolated_star_of_score u F acy score one
  have hn : 35≤35+42*u := by omega
  have geo (x) := star_geometry hn F P step x (good (.inl x))
  obtain ⟨v,f,g,h,k⟩ := pair_rim hn F (corners_marked u F acy score)
    (fun x => (geo x).1) (fun x => (geo x).2.1) (TwoGap.Words.physicalWord_ok hn F P good) one
  push_cast at loc
  obtain ⟨w,s,t,i,side,pos,lo,hi,ph⟩ := near_arm u F acy P step p loc zero v f g h k
  have off : depthAt (35+42*u) (coord p)≠0 := by
    rw [pos]; cases w with | mk a b c => cases a <;> cases b <;> cases c <;>
      simp [L7.view,reflect,depthAt,depth] <;> omega
  obtain ⟨_,um,nb,_⟩ := (geo p).2.2.2 ⟨off,full'⟩
  have clean (a) : patchSlack F a=0 := zero (.inr a) (by simp)
  have res := suffix u s t (chartCol F w) (col_lt F w) (column_of_rim F w s t side)
    (physical u F acy clean w) i ⟨lo,hi,by omega⟩ (cross_empty u F p w i hi pos nb um)
  exact ⟨P,p,w,s,t,i,step,clean,(fun t h => zero (.inl t) (by simpa using h)),iso,side,by exact_mod_cast pos,lo,hi,ph,res⟩

theorem seed_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (p : GridVertex n n) (w : View) (s f : Bool) (i : Nat),
      (Bonds F).IsIsolated p ∧ rim F w s f ∧ coord p=L7.view w n 2 ((i:Int)+1) ∧
      4≤ i ∧ i+5≤33+42*u ∧ i%6=4 ∧ tile F w 1 i=64 ∧
      ∀ j, i<j → j<33+42*u → j%3=1 → tile F w 1 j=72 ∧ lane (tile F w 4 j) 0=1 ∧
        (i+3<j → lane (tile F w 4 j) 3=1) := by
  obtain ⟨_,p,w,s,t,i,_,_,_,H⟩ := scored_seed u F acy score one
  exact ⟨p,w,s,t,i,H⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
