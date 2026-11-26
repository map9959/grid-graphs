import GridGraphs.ResidueTwoUpper.TwoGapNorthBits

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
open ResidueZero Stencil Words

theorem columnOK {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 0 1 1) {j : Nat} (hj : j<35+42*u)
    {i : Nat} (hi : i≤j) (delta : j ≤ i+1) :
    X F j∈opts[tag u i+(j-i)]! := by
  let z := tag u i+(j-i)
  have lim : z<35 := by dsimp [z,tag]; split_ifs <;> omega
  change X F j∈(Array.ofFn fun j : Fin 35 => (List.range 64).filter (column j))[z]!
  simp [lim,List.mem_filter,X_lt,column,List.all_eq_true]
  intro r hr
  let v : GridVertex (35+42*u) (35+42*u) := (⟨r,by omega⟩,⟨j,hj⟩)
  have inside (b : Bool) (p : preset z r=some b.toNat) :
      (rimDatum (11+14*(u:Int)) 0 j r).1=some b := by
    have cmp (n : Nat) (hn : n≤3) : (z=n ↔ j=n) ∧ (34-z=n ↔ 34+42*u-j=n) := by
      dsimp [z,tag]; split_ifs <;> omega
    have clip (z0 : Nat) (hz : z0<35) (j0 : Nat)
        (eq : ∀ n≤3, z0=n ↔ j0=n) : TwoGap.clip (j0:Int)=TwoGap.clip (z0:Int) := by
      have := eq 0 (by decide); have := eq 1 (by decide); have := eq 2 (by decide); have := eq 3 (by decide)
      unfold TwoGap.clip; omega
    have X := clip z lim j (fun n h => (cmp n h).1)
    have Y := clip (34-z) (by omega) (34+42*u-j) (fun n h => (cmp n h).2)
    have T : TwoGap.clip (3*(11+14*(u:Int))+1-r)=4 := by unfold TwoGap.clip; omega
    have S : TwoGap.clip ((34:Int)-r)=4 := by unfold TwoGap.clip; omega
    have y : TwoGap.clip (3*(11+14*(u:Int))+1-j)=TwoGap.clip ((34:Int)-z) := by
      convert Y using 2 <;> omega
    have base : ∀ (z : Fin 35) (r : Fin 6) (b : Bool), preset z r=some b.toNat →
        (rimDatum 11 0 z r).1=some b := by native_decide
    have ok := base ⟨z,lim⟩ ⟨r,hr⟩ b p
    dsimp only [rimDatum] at ok ⊢; norm_num only at ok
    rw [X,y,T]; rw [S] at ok
    split <;> split at ok <;> first | exact ok | contradiction
  rw [X_bit F _ r hr]
  have E : marked F ((r:Int),(j:Int))=decide (v∈F) := marked_at F v
  rw [E]
  cases h : preset z r with
  | none => rfl
  | some k =>
    have k01 : k=0 ∨ k=1 := by unfold preset at h; split_ifs at h <;> simp only [Option.some.injEq,reduceCtorEq] at h <;> omega
    rcases k01 with rfl|rfl
    · have t := chart_marks F acy score canon v 0 false (inside false h); simp [t]
    · have t := chart_marks F acy score canon v 0 true (inside true h); simp [t]

private theorem belt_check : ∀ (f : Fin 4 → Fin 6 → Bool),
    beltFull (pack (f 0)) (pack (f 1)) (pack (f 2)) (pack (f 3)) →
    ∀ i : Fin 14, let p := belt i; let q := belt (i+1)
      f p.2 ⟨p.1,by omega⟩ || f q.2 ⟨q.1,by omega⟩ := by
  -- Instead of enumerating 2^24 masks, test the six small pairwise
  -- implications used on the fourteen perimeter edges separately.
  intro f full i
  have lanes (x : Fin 6 → Bool) (r : Fin 6) : bit (pack x) r=(x r).toNat :=
    (by native_decide : ∀ x : Fin 6 → Bool, ∀ r : Fin 6, bit (pack x) r=(x r).toNat) x r
  have ends : ∀ m : Fin 64, ((m.val ||| (m.val>>>1)) &&& 15)=15 →
      ∀ r : Fin 4, bit m r=1 ∨ bit m (r.val+1)=1 := by native_decide
  have sides : ∀ a b : Fin 64, ((a.val ||| b.val) &&& 17)=17 →
      (bit a 0=1 ∨ bit b 0=1) ∧ (bit a 4=1 ∨ bit b 4=1) := by native_decide
  have bound : ∀ x : Fin 6 → Bool, pack x<64 := by native_decide
  simp only [beltFull,Bool.and_eq_true,beq_iff_eq] at full
  obtain ⟨⟨⟨⟨l,r⟩,ab⟩,bc⟩,cd⟩ := full
  have V (j : Fin 4) (e : ((pack (f j) ||| (pack (f j)>>>1)) &&& 15)=15) (k : Fin 4) :
      f j ⟨k.val,by omega⟩=true ∨ f j ⟨k.val+1,by omega⟩=true := by
    have h := ends ⟨_,bound (f j)⟩ e k
    change bit (pack (f j)) k.val=1 ∨ bit (pack (f j)) (k.val+1)=1 at h
    rwa [lanes _ ⟨k.val,by omega⟩,lanes _ ⟨k.val+1,by omega⟩,Bool.toNat_eq_one,Bool.toNat_eq_one] at h
  have H (j k : Fin 4) (e : ((pack (f j) ||| pack (f k)) &&& 17)=17) :
      (f j 0=true ∨ f k 0=true) ∧ (f j 4=true ∨ f k 4=true) := by
    have h := sides ⟨_,bound (f j)⟩ ⟨_,bound (f k)⟩ e
    change (bit (pack (f j)) 0=1 ∨ bit (pack (f k)) 0=1) ∧ (bit (pack (f j)) 4=1 ∨ bit (pack (f k)) 4=1) at h
    simp only [lanes _ ⟨0,by decide⟩,lanes _ ⟨4,by decide⟩,Bool.toNat_eq_one] at h
    exact h
  have A := H 0 1 ab; have B := H 1 2 bc; have C := H 2 3 cd
  have L0 := V 0 l 0; have L1 := V 0 l 1; have L2 := V 0 l 2; have L3 := V 0 l 3
  have R0 := V 3 r 0; have R1 := V 3 r 1; have R2 := V 3 r 2; have R3 := V 3 r 3
  fin_cases i <;> simp only [Bool.or_eq_true] <;> first
    | exact A.1 | exact B.1 | exact C.1 | exact R0 | exact R1 | exact R2 | exact R3
    | exact C.2.symm | exact B.2.symm | exact A.2.symm | exact L3.symm | exact L2.symm | exact L1.symm | exact L0.symm

theorem no_belt {n j} (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic) (hn : 5≤n)
    (hj : j+1<n) : beltFull (X F (j-2:Int)) (X F (j-1:Int)) (X F j) (X F (j+1:Int))=false := by
  by_cases low : j<2
  · rw [X_off F (Or.inl (by omega))]; rfl
  let f (c : Fin 4) (r : Fin 6) := marked F (r,(j:Int)-2+c.val)
  have eq (c : Fin 4) : pack (f c)=X F ((j:Int)-2+c.val) := rfl
  apply Bool.eq_false_iff.mpr
  intro h
  have b : beltFull (pack (f 0)) (pack (f 1)) (pack (f 2)) (pack (f 3)) := by
    simp only [eq]; norm_num; convert h using 2 <;> ring
  obtain ⟨i,p,q⟩ := rectangle_missing hn (j:=j-2) (by omega) F acy
  have site (k : Fin 14) :
      f (belt k).2 ⟨(belt k).1.val,by omega⟩=decide (place hn (j:=j-2) (by omega) (belt k)∈F) := by
    rw [←marked_at]; unfold f; congr 1; ext <;> dsimp [place,coord] <;> omega
  have hit := belt_check f b i
  change (f (belt i).2 _ || f (belt (i+1)).2 _)=true at hit
  simp only [site,decide_eq_false p,decide_eq_false q,Bool.false_or,Bool.false_eq_true] at hit

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
