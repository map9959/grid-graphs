import GridGraphs.ResidueTwoUpper.OneGap.FanBootScore

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero Stencil L7 FanSlab FanSeed FanBoot Frame BoundarySix.Connected

/-- Retain the orientation and its edge ownership at the same occurrence
as the north-fan seed. `scored_seed` alone forgets the ownership field. -/
structure Seed {u} (F : Finset (GridVertex (35+42*u) (35+42*u))) (P : GridVertex (35+42*u) (35+42*u) → _)
    (w : View) (q : Nat) : Prop where
  odd : q%2=1
  room : q+2≤11+14*u
  step : ∀ x, P x≠x → (Bonds F).Adj x (P x)
  owners : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)
  good : ∀ x, Frame.allGood F P x
  clean : ∀ a, patchSlack F a=0
  zero : ∀ p, coord p≠L7.view w (35+42*u:Nat) 2 (2+3*q:Nat) → starSlack F P p=0
  sink : ∀ p, coord p=L7.view w (35+42*u:Nat) 2 (2+3*q:Nat) → P p=p
  west : WestTeeth u q F w
  paid : square F w 1 (1+3*q)=64
  east : ∀ j, q<j → j<11+14*u → square F w 1 (1+3*j)=72

set_option maxHeartbeats 1000000 in
theorem located_seed_from_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    ∃ P w q, Seed F P w q ∧ (∃ s f, rim F w s f) ∧
      ∃ d, (Bonds F).IsIsolated d ∧ coord d=L7.view w (35+42*u:Nat) 2 (2+3*q:Nat) := by
  obtain ⟨P,p,step,arr,good,iso,loc,full',zero⟩ := isolated_star_of_score u F acy score one
  have hn : 35≤35+42*u := by omega
  have geo (x) := star_geometry hn F P step x (good (.inl x))
  obtain ⟨v,f,g,h,k⟩ := pair_rim hn F (corners_marked u F acy score)
    (fun x => (geo x).1) (fun x => (geo x).2.1) (TwoGap.Words.physicalWord_ok hn F P good) one
  push_cast at loc
  obtain ⟨w,s,t,i,side,pos,lo,hi,ph⟩ := near_arm u F acy P step p loc zero v f g h k
  let q := (i-1)/3
  have qi : i=1+3*q := by dsimp [q]; omega
  have odd : q%2=1 := by omega
  have fits : q+2≤11+14*u := by omega
  have eq : coord p=L7.view w (35+42*u:Nat) 2 (2+3*q:Nat) := by rw [pos]; congr 1 <;> push_cast <;> omega
  have off : depthAt (35+42*u) (coord p)≠0 := by
    rw [pos]; cases w with | mk a b c => cases a <;> cases b <;> cases c <;>
      simp [L7.view,reflect,depthAt,depth] <;> omega
  obtain ⟨_,um,nb,fix⟩ := (geo p).2.2.2 ⟨off,full'⟩
  have clean (a) : patchSlack F a=0 := zero (.inr a) (by simp)
  have zs (x) (ne : coord x≠L7.view w (35+42*u:Nat) 2 (2+3*q:Nat)) : starSlack F P x=0 :=
    zero (.inl x) (fun same => ne (Sum.inl.inj same ▸ eq))
  have cr : tile F w 1 i &&& 186=0 := by
    let a := onSite (s:=35+42*u-2) (L7.view w (33+42*(u:Int)) 1 i) (by
      rw [show 35+42*u-2=33+42*u by omega]
      exact_mod_cast inside_view (n:=33+42*u) (r:=1) (j:=i) w (by omega) (by omega))
    have ha : coord a=L7.view w (33+42*(u:Int)) 1 i := coord_onSite ..
    have ha' : coord a=L7.view w ((35+42*(u:Int))-2) 1 i := by rw [ha]; congr 2 <;> ring
    have cen : coord p=coord a+(1,1) := by rw [ha',view_center,pos]; rfl
    obtain ⟨x,y⟩ := PatchFilter.packed_center F a p cen
    rw [nb] at y; simp [um] at x
    have ver : ∀ (v : View) (m : Fin 512), bit m 4=0 → PatchFilter.cnb m=0 → encode m v &&& 186=0 := by decide +kernel
    unfold tile; rw [←window_encode u F w 1 i (by decide) a ha']
    exact ver _ _ x y
  have res := suffix u s t (chartCol F w) (col_lt F w) (column_of_rim F w s t side)
    (physical u F acy clean w) i ⟨lo,hi,by omega⟩ cr
  have paid : square F w 1 (1+3*q)=64 := (tile_eq F w (by omega)).symm.trans (qi ▸ res.1)
  refine ⟨P,w,q,⟨odd,fits,step,arr,good,clean,zs,?_,?_,paid,?_⟩,⟨s,t,side⟩,⟨p,iso,eq⟩⟩
  · intro a ha; exact coord_injective (ha.trans eq.symm) ▸ fix
  · apply Teeth.west_teeth u q odd fits F acy score one w s t side P step clean _ paid
    intro x ne; apply zs x; simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using ne
  · intro j lo' hj; rw [←tile_eq F w (by omega)]
    exact (res.2 (1+3*j) (by omega) (by omega) (by omega)).1

theorem seed_from_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    ∃ P w q, Seed F P w q := by
  obtain ⟨P,w,q,S,_,_⟩ := located_seed_from_score u F acy score one
  exact ⟨P,w,q,S⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
