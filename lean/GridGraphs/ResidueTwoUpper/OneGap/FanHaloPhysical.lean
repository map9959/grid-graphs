import GridGraphs.ResidueTwoUpper.OneGap.FanHalo
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port.Halo
open FanSlab L7
private theorem bitLookup : ∀ f : Ink, ∀ i : Fin 9, (bits f).testBit i.val=f i := by native_decide
private theorem keys {m n d e s t : Nat} (ovEq : ov d m=ov e n) (hm : m<512) (hn : n<512) (hs : s<4) (ht : t<4)
    (own : Own (s==d) (t==e) ((n.testBit 4)) (n.testBit ([5,7,3,1][e]!))) : key false (tag m s) d=key true (tag n t) e := by
  have enc (a b : Nat) (h : a<512) : ms (tag a b)=a ∧ dr (tag a b)=b := by
    simp only [ms,dr,tag,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]; omega
  have law : ∀ a b m n : Bool, Own a b m n → a=((m || n) != b) := by decide
  unfold key; simp only [enc m s hm,enc n t hn,Bool.false_eq_true,if_false,if_true,ovEq,law _ _ _ _ own]

/-- A 12 by 12 physical mark-and-arrow patch; only its 10 by 10
complete centers are read. This has no catalogue/lift assumption. -/
theorem impossible (p : Pattern) (bad : p∈banned) (M : Marks) (A : Arrows)
    (east : ∀ r<12, ∀ c<11, Across M A r c) (south : ∀ r<11, ∀ c<12, Down M A r c)
    (price : ∀ r<10, ∀ c<10, accepts (5+(r+1)%3) (5+(c+1)%3) (bits (ink M r c)))
    (outEdge : ∀ r<10, ∀ c<10, active (bits (ink M r c)) (A (r+1) (c+1)).val)
    (fixed : ∀ y<6, ∀ x<6, M (3+y) (3+x)=(maskOf p y x).testBit (3*(y%3)+x%3)) : False := by
  let m (r c : Nat) := bits (ink M r c); let dr' (r c : Nat) := (A (r+1) (c+1)).val
  let X (r c : Fin 10) := tag (m r c) (dr' r c)
  have mb (r c : Nat) : m r c<512 := (unpack _).1
  have db (r c : Nat) : dr' r c<4 := (A _ _).isLt
  have decode (r c : Fin 10) : ms (X r c)=m r c ∧ dr (X r c)=dr' r c := by
    dsimp only [X,tag,ms,dr]; simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]; have h := mb r c; omega
  have val (r c : Nat) (i : Fin 9) : (m r c).testBit i.val=M (r+i.val/3) (c+i.val%3) := bitLookup _ _
  have BE : ∀ (a : Fin 4) (k : Fin 4), (a.val==k.val)=(a==k) := by decide
  have e0 (a : Fin 4) : (a.val==0)=(a==0) := BE a 0
  have e1 (a : Fin 4) : (a.val==1)=(a==1) := BE a 1
  have e2 (a : Fin 4) : (a.val==2)=(a==2) := BE a 2
  have e3 (a : Fin 4) : (a.val==3)=(a==3) := BE a 3
  have he (a : Fin 4) : ∀ b : Fin 4, (a.val==b.val)=(a==b) := by revert a; decide
  have glue : ∀ f g : Ink, ∀ d : Fin 2,
      (∀ t : Fin 6, f ⟨if d.val=0 then 3*(t.val/2)+t.val%2+1 else 3+t.val,by have := t.isLt; split <;> omega⟩=
        g ⟨if d.val=0 then 3*(t.val/2)+t.val%2 else t.val,by have := t.isLt; split <;> omega⟩) → ov d (bits f)=ov (d.val+2) (bits g) := by native_decide
  apply excludes p bad; refine ⟨X,?_,?_,?_⟩
  · intro r c; rw [(decode r c).1,(decode r c).2]; refine ⟨db ..,price _ r.isLt _ c.isLt,outEdge _ r.isLt _ c.isLt,?_⟩
    apply List.all_eq_true.mpr; intro k _; dsimp only; by_cases inside : 3≤r.val+k.val/3 ∧ 3≤c.val+k.val%3 ∧ r.val+k.val/3<9 ∧ c.val+k.val%3<9
    · have h := fixed (r.val+k.val/3-3) (by omega) (c.val+k.val%3-3) (by omega)
      apply Bool.or_eq_true_iff.mpr; right; apply beq_iff_eq.mpr; rw [val]; simpa only [show 3+(r.val+k.val/3-3)=r.val+k.val/3 by omega,show 3+(c.val+k.val%3-3)=c.val+k.val%3 by omega] using h
    · simp; omega
  · intro r c t eq
    have B := east (r.val+1) (by omega) (c.val+1) (by omega)
    have h := glue (ink M r c) (ink M r t) 0 (by intro k; unfold ink; congr 1 <;> have := k.isLt <;> simp <;> omega)
    have h1 := val r t 4; have h2 := val r t 3; have h3 := val r c 4; have h4 := val r c 5
    change (m r t).testBit 4=M (r.val+1) (t.val+1) at h1; change (m r t).testBit 3=M (r.val+1) (t.val+0) at h2
    change (m r c).testBit 4=M (r.val+1) (c.val+1) at h3; change (m r c).testBit 5=M (r.val+1) (c.val+2) at h4
    have both : ∀ a b m n : Bool, Own a b m n → Own b a m n ∧ Own a b n m := by decide
    obtain ⟨v,z⟩ := both _ _ _ _ B; constructor
    · apply keys h (mb ..) (mb ..) (db ..) (db ..); change Own _ _ ((m r t).testBit 4) ((m r t).testBit 3)=true
      rw [h1,h2]; dsimp only [dr']; simpa only [show (0:Fin 2).val=0 from rfl,show (1:Fin 2).val=1 from rfl,Nat.reduceAdd,Across,←eq,Nat.add_zero,e0,e1,e2,e3,Nat.add_assoc] using z
    · apply keys h.symm (mb ..) (mb ..) (db ..) (db ..); change Own _ _ ((m r c).testBit 4) ((m r c).testBit 5)=true
      rw [h3,h4]; dsimp only [dr']; simpa only [show (0:Fin 2).val=0 from rfl,show (1:Fin 2).val=1 from rfl,Nat.reduceAdd,Across,←eq,Nat.add_zero,e0,e1,e2,e3,Nat.add_assoc] using v
  · intro r s c eq
    have B := south (r.val+1) (by omega) (c.val+1) (by omega)
    have h := glue (ink M r c) (ink M s c) 1 (by intro k; unfold ink; congr 1 <;> have := k.isLt <;> simp <;> omega)
    have h1 := val s c 4; have h2 := val s c 1; have h3 := val r c 4; have h4 := val r c 7
    change (m s c).testBit 4=M (s.val+1) (c.val+1) at h1; change (m s c).testBit 1=M (s.val+0) (c.val+1) at h2
    change (m r c).testBit 4=M (r.val+1) (c.val+1) at h3; change (m r c).testBit 7=M (r.val+2) (c.val+1) at h4
    have both : ∀ a b m n : Bool, Own a b m n → Own b a m n ∧ Own a b n m := by decide
    obtain ⟨v,z⟩ := both _ _ _ _ B; constructor
    · apply keys h (mb ..) (mb ..) (db ..) (db ..); change Own _ _ ((m s c).testBit 4) ((m s c).testBit 1)=true
      rw [h1,h2]; dsimp only [dr']; simpa only [show (0:Fin 2).val=0 from rfl,show (1:Fin 2).val=1 from rfl,Nat.reduceAdd,Down,←eq,Nat.add_zero,e0,e1,e2,e3,Nat.add_assoc] using z
    · apply keys h.symm (mb ..) (mb ..) (db ..) (db ..); change Own _ _ ((m r c).testBit 4) ((m r c).testBit 7)=true
      rw [h3,h4]; dsimp only [dr']; simpa only [show (0:Fin 2).val=0 from rfl,show (1:Fin 2).val=1 from rfl,Nat.reduceAdd,Down,←eq,Nat.add_zero,e0,e1,e2,e3,Nat.add_assoc] using v
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port.Halo
