import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryChart
import GridGraphs.ResidueTwoUpper.OneGap.ShortSeed

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
open ResidueZero Stencil L7 FanSlab FanSweep

abbrev maskAtTile {u} (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) (y i : Nat) :=
  square F w (1+3*y) (1+3*i)

private theorem clip {B L i n : Nat} (hi : i≤L+8) :
    edge (min B (L+12)+n) i=edge (B+n) i := by
  unfold edge; split_ifs <;> first | rfl | omega

set_option maxHeartbeats 900000 in
theorem tile_step {u q F P w} (S : Short.Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {seed L j z x B : Nat} (mode : Mode (seed==1) L j)
    (north : seed=1 → z=0) (bulk : seed≠1 → 2≤z)
    (loc : q+2=x+B+3*(z+j)) (lo : L≤B) (nz : L=3 → L<B)
    (left : 2≤x) (fit : x+L+10≤11+14*u) (height : z+8≤11+14*u)
    (prev : seed≠1 → ∀ a≤1, ∀ k≤L+8,
      maskAtTile F w (z+a) (x+k)=edge (B+(6-3*a)) k)
    (ahead : L<B → ∀ k, L<k → k≤L+8 → maskAtTile F w (z+j) (x+k)=edge B k) :
    maskAtTile F w (z+j) (x+L)=edge B L := by
  let b := min B (L+12)
  let M := fun r c => square F w (1+3*z+r) (1+3*x+c)
  have bounds {ss l y} (m : Mode ss l y) : 2≤y ∧ y≤3 := by cases m <;> decide
  have jlim := bounds mode
  let T : Path (box L 7) := {
    last:=3*(L+7), col:=id, M:=M, start:=rfl, stop:=rfl, bound:=fun _ h => h,
    next:=fun c h => by simp [pred,box],
    across:=fun r hr c hc => by simpa [M,Nat.add_assoc] using square_meet F w (1+3*z+r) (1+3*x+c) false,
    down:=fun r hr c hc => by simpa [M,Nat.add_assoc] using square_meet F w (1+3*z+r) (1+3*x+c) true }
  have init : Kept T (chart (seed==1) L 7 j b) := by
    intro r hr c hc
    change r≤15 at hr; change c≤3*(L+7) at hc
    have lim : c/3≤L+8 := by omega
    have align (a : Nat) (rr : r=3*a) (cc : c%3=0) :
        M r c=maskAtTile F w (z+a) (x+c/3) := by
      dsimp [M,maskAtTile]; congr 1 <;> omega
    have reg : ((seed==1 && r==0 && c==3*(b+3*j-2)) ||
        accepts (if seed==1 then rowTag r else 5+(r+1)%3) (5+(c+1)%3) (M r c))=true := by
      by_cases coin : seed=1 ∧ r=0 ∧ c=3*(b+3*j-2)
      · simp [coin.1,coin.2.1,coin.2.2]
      apply Bool.or_eq_true_iff.mpr; right
      have tag : rowTag (3*z+r)=(if seed==1 then rowTag r else 5+(r+1)%3) := by
        by_cases e : seed=1
        · simp [e,north e]
        · have := bulk e; simp [e,rowTag,show ¬3*z+r<5 by omega]; omega
      have col : realTag u (3*x+c)=5+(c+1)%3 := by unfold realTag; split_ifs <;> omega
      have A := accept_bulk u (3*z+r) (3*x+c) (by omega) (by omega) F acy P S.step w S.clean (by
        intro p hp; apply S.zero p; rw [hp]; intro e
        have pair : 3*z+r=0 ∧ 3*x+c=3*q := by
          cases w with | mk aa bb sw => cases aa <;> cases bb <;> cases sw <;>
            simp [L7.view,reflect] at e <;> omega
        have zz : z=0 := by omega
        have sn : seed=1 := by by_contra h; have := bulk h; omega
        apply coin; exact ⟨sn,by omega,by dsimp [b]; omega⟩)
      rw [tag,col] at A; simpa only [M,Nat.add_assoc] using A
    have pin : pins (seed==1) L j b r c (M r c) := by
      unfold pins
      split
      · rfl
      rename_i phase
      have cc : c%3=0 := by simpa using phase
      split
      · rename_i e
        rw [align j e.1 cc,ahead (by dsimp [b] at e; omega) _ e.2.2 lim]
        have h := clip (B:=B) (n:=0) lim; simpa [b] using h.symm
      split
      · rename_i se
        have sn := beq_iff_eq.mp se
        by_cases rr : r=0
        swap
        · simp [rr]
        subst r
        have p := align 0 rfl cc
        rw [north sn] at p; simp only [Nat.add_zero] at p
        simp only [bne_self_eq_false,Bool.false_or,p]
        split
        · rename_i lt
          have mark := S.west (x+c/3) (by dsimp [b] at lt; have := north sn; omega)
          have bit := (unpack (fun t : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+t.val/3:Nat)
            (1+3*(x+c/3)+t.val%3:Nat)))).2 4
          change lane (maskAtTile F w 0 (x+c/3)) 4=_ at bit
          apply beq_iff_eq.mpr
          rw [bit]; change (marked F (L7.view w (35+42*u:Nat) 2 (1+3*(x+c/3)+1:Nat))).toNat=1
          rw [show 1+3*(x+c/3)+1=2+3*(x+c/3) by omega,mark]; rfl
        · split
          · rename_i hit
            apply beq_iff_eq.mpr
            rw [show x+c/3=q by dsimp [b] at hit; have := north sn; omega]; exact S.paid
          · apply beq_iff_eq.mpr; apply S.east <;> dsimp [b] at * <;> have := north sn <;> omega
      · rename_i se
        have sn : seed≠1 := by simpa using se
        by_cases rr : r≤3 ∧ r%3=0
        · rw [align (r/3) (by omega) cc,prev sn _ (by omega) _ lim]
          have eq := clip (B:=B) (n:=6-3*(r/3)) lim
          rw [show b+6-r=b+(6-3*(r/3)) by omega]
          simp [b,eq]
        · simp only [Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne,beq_iff_eq]; omega
    have bd : M r c<512 := (unpack _).1
    exact chart_mem (by omega) hc bd reg pin
  have cert := replay mode (b:=b) (by dsimp [b]; omega) (by dsimp [b]; omega) (by dsimp [b]; intro h; have := nz h; omega)
  have live := flat_sound (h:=16) (w:=3*(L+7)+1) M
    (fun r c hr hc => T.down r (by change r<15; omega) c (by change c≤3*(L+7); omega))
    (fun r c hr hc => T.across r (by change r≤15; omega) c (by change c<3*(L+7); omega))
    (if seed==1 && j==3 then 100 else 36) _
    (fun r hr c hc => init r (by change r≤15; omega) c (by change c≤3*(L+7); omega))
  have hit := beq_iff_eq.mp (List.all_eq_true.mp cert _ (live (3*j) (by omega) (3*L) (by omega)))
  change M (3*j) (3*L)=edge b L at hit
  simpa only [M,maskAtTile,show 1+3*z+3*j=1+3*(z+j) by omega,show 1+3*x+3*L=1+3*(x+L) by omega,
    b,show edge (min B (L+12)) L=edge B L from clip (n:=0) (by omega)] using hit
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
