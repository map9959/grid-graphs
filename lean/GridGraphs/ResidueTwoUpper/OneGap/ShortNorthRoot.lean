import GridGraphs.ResidueTwoUpper.OneGap.ShortFront
import GridGraphs.ResidueTwoUpper.OneGap.FanLineFront

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot GridGraphs.ResidueTwoUpper.Exceptional.Frame

variable {u q : Nat}
local notation "N" => 35+42*u
local notation "K" => 11+14*u

theorem plateau {F : Finset (GridVertex N N)} {w P} (S : Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (room : max 3 (q+1)+16≤K) :
    Plateau F w 1 4 (max 3 (q+1)+12) K := by
  intro j hj hj' i hi hi'
  let v := min (i-12) (K-16)
  have h₁ : q<v := by dsimp [v]; omega
  have h₂ : 3≤v := by dsimp [v]; omega
  have h₃ : v+16≤K := by dsimp [v]; omega
  have h₄ : v+12 ≤ i ∧ i < v+16 := by dsimp [v]; omega
  let a : Fin 4 := ⟨j-1,by omega⟩
  let b : Fin 4 := ⟨i-(v+12),by omega⟩
  have E : a.val+1=j ∧ v+12+b.val=i := by dsimp [a,b]; omega
  simpa only [E.1,E.2] using block u q v S acy h₁ h₂ h₃ a b

private theorem north_rim {F : Finset (GridVertex N N)} {w P} (S : Seed F P w q)
    (i : Nat) (lo : 1 ≤ i) (hi : i < K) : marked F (L7.view w (N:Nat) 0 (1+3*i:Nat)) := by
  let p := FanSeed.atDepth w 0 (1+3*i) (by omega : 0 < N) (by omega : 1+3*i < N)
  have pos : coord p=L7.view w (N:Nat) 0 (1+3*i:Nat) := coord_onSite ..
  rw [←pos,marked_at]
  apply decide_eq_true
  apply (star_geometry (by omega : 35≤N) F P S.step p (S.good (.inl p))).1
  rw [pos]
  cases w with | mk a b k => cases a <;> cases b <;> cases k <;>
    simp [straight,depthAt,depth,L7.view,reflect] <;> omega

private theorem east_bit {F : Finset (GridVertex N N)} {w P} (S : Seed F P w q)
    (i : Nat) (lo : q < i) (hi : i < K) (b : Fin 3) (hb : 1 ≤ b.val) :
    marked F (L7.view w (N:Nat) (1+b.val:Nat) (1+3*i:Nat)) := by
  let t : Fin 9 := ⟨3*b.val,by have := b.isLt; omega⟩
  have h := (unpack (fun s : Fin 9 =>
    marked F (L7.view w (N:Nat) (1+s.val/3:Nat) (1+3*i+s.val%3:Nat)))).2 t
  change lane (square F w 1 (1+3*i)) t=_ at h
  rw [S.east i lo hi] at h
  have tab : ∀ k : Fin 3, 1≤k.val → lane 72 (3*k.val)=1 := by decide
  have e : t.val/3=b.val ∧ t.val%3=0 := by dsimp [t]; omega
  simp only [e.1,e.2,Nat.add_zero] at h
  have h' : 1=(marked F _).toNat := (tab b hb).symm.trans h
  exact Bool.toNat_eq_one.mp h'.symm

/-- The path to the north foot only uses the plateau and the original seed. -/
theorem line_from_three {F : Finset (GridVertex N N)} {w P i} (S : Seed F P w q)
    (root : q < i) (en : i<K) (pl : ∀ j, 1≤j → j≤3 → square F w (1+3*j) (1+3*i)=73) :
    RootLine F w i 4 := by
  intro r hr
  by_cases z : r=0
  · subst r; exact Bool.or_eq_true_iff.mpr (.inl (north_rim S i (by omega) en))
  by_cases small : r<4
  · have rpos : 1 ≤ r := by omega
    interval_cases r
    · exact Bool.or_eq_true_iff.mpr (.inr (east_bit S i root en 1 (by decide)))
    · exact Bool.or_eq_true_iff.mpr (.inl (east_bit S i root en 1 (by decide)))
    · exact Bool.or_eq_true_iff.mpr (.inl (east_bit S i root en 2 (by decide)))
  apply Bool.or_eq_true_iff.mpr; left
  have b := plateau_bit (pl ((r-1)/3) (by omega) (by omega)) 0 ⟨(r-1)%3,by omega⟩
  change (marked F (L7.view w (N:Nat) (1+3*((r-1)/3)+(r-1)%3:Nat) (1+3*i+0:Nat))).toNat=1 at b
  rw [show 1+3*((r-1)/3)+(r-1)%3=r by omega] at b
  simpa using b

theorem front_of_plateau {F : Finset (GridVertex N N)} {w P f} (S : Seed F P w q)
    (feet : q<f) (pl : Plateau F w 1 4 f K) : Front F w q K 4 f := by
  refine ⟨fun j lo hi i st en => pl j (by omega) hi i st en,
    fun _ st _ le => by omega,?_⟩
  intro i st en root
  exact line_from_three S root en (fun j lo hi => pl j lo (by omega) i st en)

/-- The short seed gives a genuinely rooted suffix at row four. -/
theorem front {F : Finset (GridVertex N N)} {w P} (S : Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (room : max 3 (q+1)+16≤K) :
    Front F w q K 4 (max 3 (q+1)+12) :=
  front_of_plateau S (by omega) (plateau S acy room)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
