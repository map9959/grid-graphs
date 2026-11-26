import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryStep
import GridGraphs.ResidueTwoUpper.OneGap.FanLineFront

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.NorthCut161
open ResidueZero Stencil L7 FanSlab FanSeed Short FanSweep EastBoundary BoundarySix.Connected

/-- One north strip, open at the bottom. Its columns use the actual
west and east prices; its only planted marks come from the seed. -/
private def prices := Array.ofFn fun a : Fin 8 => Array.ofFn fun c : Fin 13 =>
  (List.range 512).filter (accepts a.val c.val)
private def seeds (q r c m : Nat) :=
  r != 0 || c%3 != 0 || (if c/3<q then lane m 4==1 else m==(if c/3=q then 64 else 72))
def grid (q : Nat) := FanSweep.build ⟨33,156,[]⟩ fun r c =>
  (if r=0 ∧ c=3*q then List.range 512 else (prices[rowTag r]!)[realTag 3 c]!).filter (seeds q r c)
/-- These are the first sufficient rounds for the complete row-9 audits.
One pass earlier, tile (8,52) still admits mask 9 in both strips. -/
private def rounds (q : Nat) := if q=51 then 177 else 183
private def strip (q : Nat) := EastBoundary.Kernel.prune 34 157 (rounds q) (grid q)
def domain (q j i : Nat) := cell (strip q) (3*j) (3*i)

theorem admitted {F P w q} (S : Seed (u:=3) F P w q) (acy : (Bonds F).IsAcyclic)
    {j i} (jh : j≤11) (ih : i≤52) : maskAtTile F w j i∈domain q j i := by
  let M := fun r c => square F w (1+r) (1+c)
  have keep (r : Nat) (hr : r<34) (c : Nat) (hc : c<157) : M r c∈EastBoundary.Kernel.get (grid q) r c := by
    have bd : M r c<512 := (unpack _).1
    have pin : seeds q r c (M r c) := by
      by_cases rr : r=0
      swap
      · simp [seeds,rr]
      subst r
      by_cases cc : c%3=0
      swap
      · simp [seeds,cc]
      have eq : M 0 c=maskAtTile F w 0 (c/3) := congrArg₂ (square F w) rfl (by omega)
      simp only [seeds,bne_self_eq_false,cc,Bool.false_or,eq]
      split
      · rename_i lt
        apply beq_iff_eq.mpr
        have h := (unpack (fun s : Fin 9 => marked F (L7.view w (161:Nat) (1+s.val/3:Nat)
          (1+3*(c/3)+s.val%3:Nat)))).2 4
        change lane (maskAtTile F w 0 (c/3)) 4=(marked F (L7.view w _ 2 (1+3*(c/3)+1:Nat))).toNat at h
        rw [h,show 1+3*(c/3)+1=2+3*(c/3) by omega,S.west _ lt]; rfl
      · split
        · rename_i e; rw [e]; exact beq_iff_eq.mpr S.paid
        · exact beq_iff_eq.mpr (S.east _ (by omega) (by omega))
    by_cases special : r=0 ∧ c=3*q
    · obtain ⟨rfl,rfl⟩ := special
      simp [EastBoundary.Kernel.get,grid,FanSweep.build,hc,bd,pin]
    · have A := accept_bulk 3 r c (by omega) (by omega) F acy P S.step w S.clean (by
        intro v loc; apply S.zero; rw [loc]; intro e
        cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at e <;> omega)
      have rt : rowTag r<8 := by unfold rowTag; split <;> omega
      have ct : realTag 3 c<13 := by unfold realTag; split_ifs <;> omega
      have valid : accepts (rowTag r) (realTag 3 c) (M r c) := A
      simp [EastBoundary.Kernel.get,grid,FanSweep.build,hr,hc,special,prices,rt,ct,bd,valid,pin]
  have live := flat_sound M (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+c) true)
    (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+c) false) (rounds q) _ keep
  exact live _ (by omega) _ (by omega)

private def valid (q y j i m : Nat) : Prop := ∀ a b : Fin 3,
  3*j+b.val≤3*y+1 → lane m (3*b.val+a.val)=1 → NorthFanLines.mark q i j a.val b.val
private instance (q y j i m) : Decidable (valid q y j i m) := by unfold valid NorthFanLines.mark; infer_instance
private def audit (q y f : Nat) :=
  let g := strip q
  let D := fun j i => cell g (3*j) (3*i)
  ((List.range y).all fun j => j==0 || (List.range (52-q)).all fun c =>
    (D j (q+1+c)).all (·==73)) &&
  ((List.range (y+1)).all fun j => (List.range (q+2-f)).all fun c =>
    (D j (f-1+c)).all fun m => decide (valid q y j (f-1+c) m)) &&
  (D y (f-1)).all (fun m => m==73 || m==129) && (D y f).all (fun m => m==9 || m==73)

private theorem checked : audit 49 9 26 := by native_decide

theorem read49 {F w P} (S : Seed (u:=3) F P w 49) (acy : (Bonds F).IsAcyclic) :
    (∀ j i, 1≤j → j<9 → 49 < i → i<53 → maskAtTile F w j i=73) ∧
    (∀ j i a b : Nat, j≤9 → 25 ≤ i → i≤49 → a<3 → b<3 → 3*j+b≤28 →
      marked F (L7.view w (161:Nat) (1+3*j+b:Nat) (1+3*i+a:Nat))=true → NorthFanLines.mark 49 i j a b) ∧
    (maskAtTile F w 9 25=73 ∨ maskAtTile F w 9 25=129) ∧
    (maskAtTile F w 9 26=9 ∨ maskAtTile F w 9 26=73) := by
  have tab := checked
  simp only [audit,Bool.and_eq_true] at tab
  refine ⟨?_,?_,?_,?_⟩
  · intro j i jl jh il ih
    have p := List.all_eq_true.mp tab.1.1.1 j (List.mem_range.mpr jh)
    have row := (Bool.or_eq_true_iff.mp p).resolve_left (by simp; omega)
    have ck := List.all_eq_true.mp row (i-50) (List.mem_range.mpr (by omega))
    rw [show 49+1+(i-50)=i by omega] at ck
    exact beq_iff_eq.mp (List.all_eq_true.mp ck _ (admitted S acy (by omega) (by omega)))
  · intro j i a b jh il ih al bl cut hm
    have ck := List.all_eq_true.mp (List.all_eq_true.mp tab.1.1.2 j (List.mem_range.mpr (by omega)))
      (i-25) (List.mem_range.mpr (by omega))
    rw [show 26-1+(i-25)=i by omega] at ck
    have good : valid 49 9 j i (maskAtTile F w j i) := of_decide_eq_true
      (List.all_eq_true.mp ck _ (admitted S acy (by omega) (by omega)))
    apply good ⟨a,al⟩ ⟨b,bl⟩ cut
    let idx : Fin 9 := ⟨3*b+a,by omega⟩
    have val := (unpack (fun s : Fin 9 => marked F (L7.view w (161:Nat)
      (1+3*j+s.val/3:Nat) (1+3*i+s.val%3:Nat)))).2 idx
    change lane (maskAtTile F w j i) idx=_ at val
    simpa only [idx,show (3*b+a)/3=b by omega,show (3*b+a)%3=a by omega,hm,show true.toNat=1 by rfl] using val
  · simpa only [Bool.or_eq_true,beq_iff_eq] using List.all_eq_true.mp tab.1.2 _
      (admitted S acy (j:=9) (i:=25) (by decide) (by decide))
  · simpa only [Bool.or_eq_true,beq_iff_eq] using List.all_eq_true.mp tab.2 _
      (admitted S acy (j:=9) (i:=26) (by decide) (by decide))

/-- Each dangling line has its own physical two-column seal. At the
cut the upper-component test inspects only through site row 29,
leaving the last site-row of the western tile unrestricted. -/
theorem seals49 {F w P} (S : Seed (u:=3) F P w 49) (acy : (Bonds F).IsAcyclic)
    {t : Nat} (lo : 26≤t) (hi : t≤49) : Seal F w 49 t 9 := by
  have collar := (read49 S acy).2.1
  apply dangling_through_cut _ 49 9 t (by decide) (by omega) (by omega) hi
  intro j jh i a b cut _ it ti _ al bl
  exact collar j i a b jh (by omega) (by omega) al bl cut

private def audit51 :=
  let g := strip 51
  let D := fun j i => cell g (3*j) (3*i)
  ((List.range 8).all fun j => (D (1+j) 52).all (·==73)) &&
  ((List.range 10).all fun j => (List.range 26).all fun c =>
    (D j (26+c)).all fun m => decide (valid 51 9 j (26+c) m)) &&
  (D 9 26).all (fun m => m==9 || m==73)

private theorem checked51 : audit51 := by native_decide

theorem read51 {F w P} (S : Seed (u:=3) F P w 51) (acy : (Bonds F).IsAcyclic) :
    (∀ j, 1≤j → j<9 → maskAtTile F w j 52=73) ∧
    (∀ t, 27≤t → t≤51 → Seal F w 51 t 9) ∧
    (maskAtTile F w 9 26=9 ∨ maskAtTile F w 9 26=73) := by
  have tab := checked51
  simp only [audit51,Bool.and_eq_true] at tab
  refine ⟨?_,?_,?_⟩
  · intro j jl jh
    have ck := List.all_eq_true.mp tab.1.1 (j-1) (List.mem_range.mpr (by omega))
    rw [show 1+(j-1)=j by omega] at ck
    exact beq_iff_eq.mp (List.all_eq_true.mp ck _ (admitted S acy (by omega) (by decide)))
  · intro t tl rt
    apply dangling_through_cut _ 51 9 t (by decide) (by omega) (by omega) rt
    intro j jh i a b cut _ it ti _ al bl hm
    have ck := List.all_eq_true.mp (List.all_eq_true.mp tab.1.2 j (List.mem_range.mpr (by omega)))
      (i-26) (List.mem_range.mpr (by omega))
    rw [show 26+(i-26)=i by omega] at ck
    have h : valid 51 9 j i (maskAtTile F w j i) := of_decide_eq_true
      (List.all_eq_true.mp ck _ (admitted S acy (by omega) (by omega)))
    apply h ⟨a,al⟩ ⟨b,bl⟩ cut
    let idx : Fin 9 := ⟨3*b+a,by omega⟩
    have v := (unpack (fun s : Fin 9 => marked F (L7.view w (161:Nat)
      (1+3*j+s.val/3:Nat) (1+3*i+s.val%3:Nat)))).2 idx
    change lane (maskAtTile F w j i) idx=_ at v
    simpa only [idx,show (3*b+a)/3=b by omega,show (3*b+a)%3=a by omega,hm,show true.toNat=1 by rfl] using v
  · simpa only [Bool.or_eq_true,beq_iff_eq] using List.all_eq_true.mp tab.2 _
      (admitted S acy (j:=9) (i:=26) (by decide) (by decide))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.NorthCut161
