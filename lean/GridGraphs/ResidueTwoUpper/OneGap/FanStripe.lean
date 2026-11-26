import GridGraphs.ResidueTwoUpper.OneGap.DefectSites

/-! The bulk forward-stripe rule using a 7×5 physical rectangle. Only
zero patch charges in that rectangle are needed. Row triples are checked
as soon as all three rows are chosen. The lookup has nine 512-bit words. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil

private def catalogue : Array Nat := #[
  0x5000000000000000f000000000000031100001313000003dd000000000000005500000000000500df00001311000033cc01011313010533cc,
  0x5000000000000000b000000000000000000000111000023cc0000000000000051000000000005009300000131000003cc01010111010503cc,
  0x5000000000000000f000000110000000300001333000003cc000000000000005500000000000500df00001311000013cf01011333010513cc,
  0x100000000000000050000000000000308000012130000030c00000000000000310000000000050055000012110000330001010013010533cc,
  0x17000000000000001f000000110000030000001333000003ce000000000000005700000000000500df00001311000033dc01011333010533cc,
  0x10000000000000023000000110000004000001233000003000000000000000005000000000005000f000012110000134401010033010513cc,
  0x17000000000000001f0000000000000300000013130000033c000000000000005700000000000500df000013110000334401011313010533fc,
  0x17000000000000001b0000000200001000000000130000000c00000000000000530000000000050093000000000000134401011313010513cc,
  0x17000000000000001f0000001100000000000013330000030c000000000000005700000000000500df000013110000136601011333010513ee]
def stripeAllowed (i j m : Nat) := catalogue[3*(i%3)+j%3]!.testBit m
private abbrev allowed := stripeAllowed

private theorem check_table : ∀ (r c : Fin 3) (m : Fin 512), maskOK m →
    twoOrbitPatch 23 (6+(r.val:Int),6+(c.val:Int)) m=0 → allowed r c m := by native_decide

abbrev R := Fin 32
def chunk (v : R) (j : Nat) := (v.val >>> j)%8
def block (a b c : R) (j : Nat) := chunk a j + 8*chunk b j + 64*chunk c j
private def legal (i : Nat) (a b c : R) := decide (∀ j : Fin 3, allowed (1+i) j (block a b c j))

private theorem scan : ∀ a : R, chunk a 1=7 → ∀ b : R, chunk b 1=0 →
    ∀ c : R, chunk c 1=0 → legal 0 a b c →
    ∀ d : R, legal 1 b c d → ∀ e : R, legal 2 c d e →
    ∀ f : R, legal 3 d e f → ∀ g : R, legal 4 e f g → block d e f 1=7 := by native_decide

def encodeRow (w : Fin 5 → Bool) : R :=
  Fin.ofNat 32 ((List.ofFn fun i : Fin 5 => (w i).toNat <<< i.val).sum)
theorem row_bit : ∀ (w : Fin 5 → Bool) (i : Fin 5),
    bit (encodeRow w) i=(w i).toNat := by decide +kernel
theorem block_bits : ∀ (a b c : R) (j : Fin 3) (q : Fin 9),
    bit (block a b c j) q = bit (if q.val<3 then a else if q.val<6 then b else c)
      (j.val+q.val%3) := by native_decide

theorem bulk_stripe_allowed (u : Nat) (r c : Nat)
    (hr : 6≤r ∧ r+7≤33+42*u) (hc : 6≤c ∧ c+7≤33+42*u) (m : Fin 512)
    (ok : maskOK m) (zero : twoOrbitPatch (35+42*(u:Int)) (r,c) m=0) :
    allowed r c m := by
  let j := 4+14*(u:Int)
  have eq : 35+42*(u:Int)-2=21+3*j := by dsimp [j]; ring
  have loc := patchLocation_transport (b:=21) (by decide) (j:=j) (by dsimp [j]; positivity)
    ((r:Int),(c:Int))
  have pt : representative 21 j ((r:Int),(c:Int))=((6:Int)+(r%3:Nat),(6:Int)+(c%3:Nat)) := by
    ext <;> simp [representative,rep,j] <;> split_ifs <;> omega
  have w : twoOrbitPatch 23 ((6:Int)+(r%3:Nat),(6:Int)+(c%3:Nat)) m=0 := by
    simpa only [twoOrbitPatch,eq,loc,pt,show (23:Int)-2=21 by decide] using zero
  have ck := check_table ⟨r%3,by omega⟩ ⟨c%3,by omega⟩ m ok w
  simpa [allowed,stripeAllowed] using ck

theorem stripe_from_masks (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (r c : Nat)
    (hr : 6≤r ∧ r+11≤33+42*u) (hc : 6≤c ∧ c+9≤33+42*u)
    (phase : r%3=1 ∧ c%3=0)
    (ok : ∀ i : Fin 5, ∀ j : Fin 3, stripeAllowed (r+i.val) (c+j.val)
      (physicalMask F (r+i.val) (c+j.val) (by have := i.isLt; omega) (by have := j.isLt; omega)))
    (source : physicalMask F r (c+1) (by omega) (by omega)=7) :
    physicalMask F (r+3) (c+1) (by omega) (by omega)=7 := by
  let n := 35+42*u
  let row (i : Nat) := encodeRow (fun a => marked F ((r+i:Nat),(c+a.val:Nat)))
  have decode (i : Fin 5) (j : Fin 3) :
      (physicalMask F (r+i.val) (c+j.val) (by have := i.isLt; omega)
        (by have := j.isLt; omega)).val = block (row i) (row (i+1:Nat)) (row (i+2:Nat)) j := by
    let m := physicalMask F (r+i.val) (c+j.val) (by have := i.isLt; omega)
      (by have := j.isLt; omega)
    have eqbit (q : Fin 9) := patch_bit F (r+i.val) (c+j.val) (by have := i.isLt; omega)
      (by have := j.isLt; omega) q
    have eqbits (q : Fin 9) : bit m q = bit (block (row i) (row (i+1:Nat)) (row (i+2:Nat)) j) q := by
      rw [block_bits]
      let k : Fin 5 := ⟨j.val+q.val%3,by have := j.isLt; omega⟩
      have extract (s : Nat) : bit (row s) k = (marked F ((r+s:Nat),(c+k.val:Nat))).toNat :=
        row_bit _ k
      change bit m q=bit _ k
      rcases lt_or_ge q.val 3 with h|h
      · rw [if_pos h,extract,eqbit]
        congr 2 <;> ext <;> simp [offset,k] <;> omega
      · rw [if_neg (by omega : ¬q.val<3)]
        split_ifs <;> rw [extract,eqbit] <;> congr 2 <;> ext <;> simp [offset,k] <;> omega
    have bound : block (row i) (row (i+1:Nat)) (row (i+2:Nat)) j <512 := by
      unfold block chunk; omega
    have inj : ∀ a b : Fin 512, (∀ q : Fin 9, bit a q=bit b q) → a=b := by native_decide
    exact congrArg Fin.val (inj m ⟨_,bound⟩ eqbits)
  have step (i : Fin 5) : legal i (row i) (row (i+1:Nat)) (row (i+2:Nat)) := by
    apply decide_eq_true
    intro j
    have hb := ok i j
    rw [decode] at hb
    unfold allowed
    unfold stripeAllowed at hb ⊢
    rwa [show (r+i.val)%3=(1+i.val)%3 by omega,show (c+j.val)%3=j.val%3 by omega] at hb
  have seed := decode 0 1
  change (physicalMask F r (c+1) _ _).val = block (row 0) (row 1) (row 2) 1 at seed
  rw [source] at seed
  change 7=block _ _ _ _ at seed
  unfold block chunk at seed
  have end' := scan (row 0) (by unfold chunk; omega) (row 1) (by unfold chunk; omega)
    (row 2) (by unfold chunk; omega) (step 0) _ (step 1) _ (step 2) _ (step 3) _ (step 4)
  exact Fin.ext ((decode 3 1).trans end')

/-- A zero-price tube makes the aligned stripe advance three physical rows. -/
theorem forward_stripe (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (r c : Nat)
    (hr : 6≤r ∧ r+11≤33+42*u) (hc : 6≤c ∧ c+9≤33+42*u)
    (phase : r%3=1 ∧ c%3=0)
    (zero : ∀ i : Fin 5, ∀ j : Fin 3,
      patchSlack F (⟨r+i,by have := i.isLt; omega⟩,⟨c+j,by have := j.isLt; omega⟩)=0)
    (source : physicalMask F r (c+1) (by omega) (by omega)=7) :
    physicalMask F (r+3) (c+1) (by omega) (by omega)=7 := by
  apply stripe_from_masks u F r c hr hc phase _ source
  intro i j
  have hi := i.isLt; have hj := j.isLt
  have cast : ((35+42*u:Nat):Int)=35+42*(u:Int) := by push_cast; ring
  have z := zero i j
  change twoOrbitPatch ((35+42*u:Nat):Int) ((r+i.val:Nat),(c+j.val:Nat)) _=0 at z
  rw [cast] at z
  exact bulk_stripe_allowed u _ _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ _ (physical_mask_ok F acy ..) z

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
