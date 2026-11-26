import GridGraphs.NoPitch.Budget.PatchPairs19
import GridGraphs.NoPitch.Budget.LetterRows19

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset FaceRows
attribute [local irreducible] chart19
def spFamily (i : Nat) := 344 ≤ i && i ≤ 1163
def localQ (q : Q) (d : Fin 4) : Option Q :=
  let r : Int := q.1.val+(if d=1 then 1 else if d=3 then -1 else 0)
  let c : Int := q.2.val+(if d=0 then 1 else if d=2 then -1 else 0)
  if h : 0≤r ∧ 0≤c ∧ r.toNat<3 ∧ c.toNat<3 then some (⟨_,h.2.2.1⟩,⟨_,h.2.2.2⟩) else none
def cellWord (q : Q) (f : Bool) (bits : Fin 4 → Bool) :=
  let ds := (List.finRange 4).filter fun d => (localQ q d).isSome
  ((f::ds.map bits).zipIdx.map fun (b,j) => b.toNat*2^j).sum
def cellEvent (T : Table) (p : P) (q : Q) (g : Fin 8) (f : Bool) (bits : Fin 4 → Bool) :=
  let z := small 3 g q
  event T (small 17 g p) (small 19 g (site p q)) (3*z.1.val+z.2.val) (cellWord z f bits)
def patchBits (a : Nine) (q : Q) (g : Fin 8) (d : Fin 4) :=
  (localQ (small 3 g q) d).any (fun z => a (small 3 (invers g) z))
def rotatedBits (bits : Fin 4 → Bool) (g : Fin 8) (d : Fin 4) := bits (dirView (invers g) d)
def viewSum (f : Fin 8 → Terms) := (List.finRange 8).flatMap f
def cellPatch (T : Table) (p : P) (q : Q) (a : Nine) :=
  viewSum fun g => cellEvent T p q g (a q) (patchBits a q g)
def cellStar (T : Table) (p : P) (q : Q) (f : Bool) (bits : Fin 4 → Bool) :=
  viewSum fun g => cellEvent T p q g f (rotatedBits bits g)
def offsets := ((List.finRange 3).flatMap fun u => (List.finRange 3).map (u,·))
def originAt (x : X) (q : Q) : Option P :=
  if h : q.1.val≤x.1.val ∧ q.2.val≤x.2.val ∧ x.1.val-q.1.val<17 ∧ x.2.val-q.2.val<17 then
    some (⟨_,h.2.2.1⟩,⟨_,h.2.2.2⟩) else none
def nearby (T : Table) (x : X) (q : Q) (f : Bool) (bits : Fin 4 → Bool) :=
  ((originAt x q).map fun p => cellStar T p q f bits).getD []
def patchSP (T : Table) (p : P) (a : Nine) := offsets.flatMap fun q => cellPatch T p q a
def starSP (T : Table) (x : X) (f : Bool) (bits : Fin 4 → Bool) :=
  offsets.flatMap fun q => nearby T x q f bits
def spCheck (D : Chart) :=
  let w := contribution D (index D) (prices D spFamily)
  let T := tagMap starPatchTokens 344
  decide (∀ p a, legal a → balanced (w (patchCode p a) ++ patchSP T p a)) &&
  decide (∀ x f bits o, permissible x bits f o → (∀ d, bits d → (probe x d.val).isSome) →
    balanced (w (localStar x f bits o) ++ negTerms (starSP T x f bits)))
private theorem spReplay : spCheck chart19 := by native_decide

private theorem actual (T : Table) (F : Finset X) (p : P) (q : Q) :
    cellPatch T p q (patchMask F p)=cellStar T p q (decide (site p q∈F)) (bitsAt F (site p q)) := by
  unfold cellPatch cellStar; apply congrArg viewSum; funext g
  unfold cellEvent
  have geom : ∀ (p : P) (q : Q) (g : Fin 8) (d : Fin 4), ∀ z∈localQ (small 3 g q) d,
      probe (site p q) (dirView (invers g) d).val=some (site p (small 3 (invers g) z)) := by native_decide
  have eq (d : Fin 4) (m : (localQ (small 3 g q) d).isSome) :
      patchBits (patchMask F p) q g d=rotatedBits (bitsAt F (site p q)) g d := by
    cases h : localQ (small 3 g q) d with
    | none => simp [h] at m
    | some z =>
      simp only [patchBits,h,rotatedBits,bitsAt,geom p q g d z (by simp [h]),Option.any_some]
      rfl
  have word : cellWord (small 3 g q) ((patchMask F p) q) (patchBits (patchMask F p) q g)=
      cellWord (small 3 g q) (decide (site p q∈F)) (rotatedBits (bitsAt F (site p q)) g) := by
    have e := List.map_congr_left (l:=(List.finRange 4).filter fun d => (localQ (small 3 g q) d).isSome)
      (fun d hd => eq d (List.mem_filter.mp hd).2)
    unfold cellWord; dsimp only; rw [e]; rfl
  dsimp only; rw [word]

private theorem offsets_sum (i : Nat) (f : Q → Terms) :
    coeff i (offsets.flatMap f)=∑ q, coeff i (f q) := by
  have h : offsets.Nodup ∧ offsets.toFinset=univ := by decide +kernel
  rw [flatCoeff,←List.sum_toFinset _ h.1,h.2]

private theorem conservation (T : Table) (F : Finset X) (i : Nat) :
    (∑ x, coeff i (starSP T x (decide (x∈F)) (bitsAt F x)))=
      ∑ p, coeff i (patchSP T p (patchMask F p)) := by
  simp only [starSP,patchSP,offsets_sum]
  rw [sum_comm (s:=univ (α:=X)) (t:=univ (α:=Q)),sum_comm (s:=univ (α:=P)) (t:=univ (α:=Q))]
  apply sum_congr rfl; intro q _
  have left : ∀ (p : P) (q : Q), originAt (site p q) q=some p := by native_decide
  have right : ∀ (x : X) (q : Q), ∀ p∈originAt x q, site p q=x := by native_decide
  let f (x : X) := coeff i (nearby T x q (decide (x∈F)) (bitsAt F x))
  let e (p : P) := site p q
  have inj : Function.Injective e := by
    intro p b h
    have z := congrArg (fun x => originAt x q) h
    simpa only [e,left,Option.some.injEq] using z
  have z : ∑ x, f x=∑ x ∈ univ.image e, f x := by
    symm; apply sum_subset (subset_univ _); intro x _ no
    cases o : originAt x q with
    | none => simp [f,nearby,o,coeff]
    | some p => exact False.elim (no (mem_image.mpr ⟨p,mem_univ _,right x q p (by simp [o])⟩))
  change ∑ x, f x=_
  rw [z,sum_image inj.injOn]; simp only [f,e,nearby,left,Option.map_some,Option.getD_some,actual]

private theorem sp_rows (D : Chart) (ok : spCheck D) (sup : supported D spFamily)
    (F : Finset X) (acy : (G F).IsAcyclic) (i : Fin D.rows.size) (h : spFamily i) :
    lhs D (physicalVector D F (out F)) i=0 := by
  let T := tagMap starPatchTokens 344
  have st (x : X) : lookupPrice D i (index D) (Keys.star F (out F) x)=
      coeff i (starSP T x (decide (x∈F)) (bitsAt F x)) := by
    have bound (d : Fin 4) (hd : bitsAt F x d) : (probe x d.val).isSome := by
      cases e : probe x d.val <;> simp_all [bitsAt]
    have z := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).2 x _ _ _ (physical_perm F acy x) bound
    have a := zero_of_balanced _ z i
    rw [coeff_append,coeff_neg,sig_price _ _ _ h,star_agrees] at a
    exact eq_of_sub_eq_zero a
  have pa (p : P) : lookupPrice D i (index D) (patch F p)= -coeff i (patchSP T p (patchMask F p)) := by
    have z := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).1 p _ (patch_legal F acy p)
    have a := zero_of_balanced _ z i; rw [coeff_append,sig_price _ _ _ h] at a
    exact eq_neg_of_add_eq_zero_left a
  rw [star_patch_lhs sup F _ i h]
  simp only [st,pa,sum_neg_distrib,conservation,add_neg_cancel]

theorem sp_rows19 (F : Finset X) (acy : (G F).IsAcyclic) (i : Fin chart19.rows.size) (h : spFamily i) :
    2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0 := by
  have info : ∀ i : Fin chart19.rows.size, spFamily i → chart19.rows[i].rhs=⟨0,0,0⟩ := by native_decide
  have sup : supported chart19 spFamily := by native_decide
  rw [sp_rows _ spReplay sup F acy i h,info i h]; rfl

end GridGraphs.NoPitch.LocalBoard19
