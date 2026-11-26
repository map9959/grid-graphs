import GridGraphs.ResidueTwoUpper.OneGap.FanPortBits
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
open L7 FanSlab

theorem mask_label (m : Nat) (f : Dir) : mask (label m f)=m := by
  unfold mask label; simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]; rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by decide),Nat.div_eq_of_lt (portBits f).1,Nat.zero_add]
theorem port_label (m : Nat) (f : Dir) (d : Fin 4) : out (label m f) d=three (fun k => f (idx d k)==d) := by
  rw [←(portBits f).2 d]; unfold label out; fin_cases d <;> simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow] <;> norm_num <;> omega

theorem label_mem (M : Ink) (f : Dir) (h : ∀ i : Fin 9,
    (i.val%3≠0 → Own (f i==2) (f (Fin.ofNat 9 (i.val-1))==0) (M i) (M (Fin.ofNat 9 (i.val-1)))) ∧
    (3≤ i.val → Own (f i==3) (f (Fin.ofNat 9 (i.val-3))==1) (M i) (M (Fin.ofNat 9 (i.val-3))))) : label (bits M) f∈labels (bits M) := by
  apply real_label; · intro i _; exact (f _).isLt
  intro i hi; let t : Fin 9 := ⟨i,hi⟩; have ht : Fin.ofNat 9 i=t := Fin.ext (Nat.mod_eq_of_lt hi)
  have mb (j : Nat) (hj : j<9) : (bits M).testBit j=M (Fin.ofNat 9 j) := by simpa [Fin.ofNat,Nat.mod_eq_of_lt hj] using maskbits M ⟨j,hj⟩
  have hbe : ∀ a b : Fin 4, (a.val==b.val)=(a==b) := by decide
  have b0 (a : Fin 4) := hbe a 0; have b1 (a : Fin 4) := hbe a 1; have b2 (a : Fin 4) := hbe a 2; have b3 (a : Fin 4) := hbe a 3
  change ∀ a : Fin 4, (a.val==0)=(a==0) at b0; change ∀ a : Fin 4, (a.val==1)=(a==1) at b1
  change ∀ a : Fin 4, (a.val==2)=(a==2) at b2; change ∀ a : Fin 4, (a.val==3)=(a==3) at b3
  unfold tileOK; apply Bool.and_eq_true_iff.mpr; constructor
  · by_cases west : i%3=0
    · simp [west]
    apply Bool.or_eq_true_iff.mpr; right; unfold clash; change Own (lift f i==2) (digit f i (i-1)==0) _ _=true
    rw [(digits f t).1 west,mb _ hi,mb _ (by omega)]; simpa only [lift,ht,b0,b1,b2,b3] using (h t).1 west
  · by_cases north : i<3
    · simp [north]
    apply Bool.or_eq_true_iff.mpr; right; unfold clash; change Own (lift f i==3) (digit f i (i-3)==1) _ _=true
    rw [(digits f t).2 (by change 3≤ i; omega),mb _ hi,mb _ (by omega)]; simpa only [lift,ht,b0,b1,b2,b3] using (h t).2 (by change 3≤ i; omega)

private theorem edgeBits : ∀ M : Ink, ∀ d : Fin 4, edge (bits M) d=three (fun k => M (idx d k)) := by native_decide
private theorem match3 : ∀ a b m n : Fin 3 → Bool, (∀ k, Own (a k) (b k) (m k) (n k)) →
  ((three a &&& three b)==0 && (three a ||| three b)==(three m ||| three n))=true := by native_decide

theorem meet_label (M L : Ink) (f g : Dir) (d e : Fin 4) (en : e.val=d.val+2)
    (law : ∀ k, Own (f (idx d k)==d) (g (idx e k)==e) (M (idx d k)) (L (idx e k))) :
    meets d.val (label (bits M) f) (label (bits L) g) := by
  unfold meets; dsimp only; rw [←en,port_label,port_label,mask_label,mask_label,edgeBits,edgeBits]; exact match3 _ _ _ _ law
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
