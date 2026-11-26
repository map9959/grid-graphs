import GridGraphs.ResidueTwoUpper.TwoGapFrontierSurvival

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open Finset ResidueZero Stencil Catalogue Words
variable {u : Nat}

def bands (u : Nat) := 11+14*u
def leftCol (q : Nat) := 3*q-2
def tabNo (k j : Nat) := if j=0 then 0 else if j=1 then 1 else if j<k-3 then 2 else if j=k-3 then 3 else 4
def toothNo (k j : Nat) := if j=0 then 495 else if j+1=k then 511 else 0
noncomputable def physicalWordAt (F : Finset (Board u)) (q j : Nat) := stripWord (maskField F) q j

private theorem line_pack (w : Word) (r : Fin 3) :
    line w r = packed9 (fun i => (if i.val<3 then w.1 else if i.val<6 then w.2.1 else w.2.2).testBit
      (3*(i.val%3)+r.val)) := by
  unfold line packed9
  have b (n i : Nat) : ((n >>> i)%2)=(n.testBit i).toNat := by
    simp [Nat.testBit_eq_decide_div_mod_eq,Nat.shiftRight_eq_div_pow]
    by_cases h : n/2^i%2=1 <;> simp [h] <;> omega
  simp only [b]
  rfl

private theorem mark_word (F : Finset (Board u)) {q j : Nat} (qlo : 3≤q) (qhi : q+4≤bands u)
    (hj : j<bands u) (r : Fin 3) :
    line (physicalWordAt F q j) r = wordRow F (leftCol q) (3*j+r.val+1) := by
  rw [line_pack]
  unfold wordRow
  apply congrArg packed9; funext i
  let a : Fin 9 := ⟨3*(i.val%3)+r.val,by have := r.isLt; omega⟩
  have atTile (b : Int) (col : Int) (e : (1+3*b+(a.val/3:Nat):Int)=col) :
      (tile (maskField F) b j).testBit a.val =
        marked F ((3*j+r.val+1:Nat),col) := by
    unfold tile; rw [packed_bits]
    change marked F _ = marked F _
    apply congrArg (marked F)
    ext <;> dsimp [shiftAt,site,a] at e ⊢ <;> have := r.isLt <;> omega
  have col := (leftCol q+i.val : Nat)
  have rc := row_rc (u:=u) (leftCol q) (3*j+r.val+1) (by dsimp [bands,Size] at *; omega)
    (by dsimp [leftCol,bands,Size] at *; omega) i
  rw [←marked_at]
  have phys : coord (rowSite u (leftCol q) (3*j+r.val+1) i)=
      (((3*j+r.val+1:Nat):Int),((leftCol q+i.val:Nat):Int)) := by
    apply Prod.ext <;> dsimp [coord] <;> exact_mod_cast (by first | exact (Prod.mk.inj rc).1 | exact (Prod.mk.inj rc).2)
  rw [phys]
  change (if i.val<3 then tile (maskField F) (q-1) j else if i.val<6 then tile (maskField F) q j else
    tile (maskField F) (q+1) j).testBit a.val = _
  split_ifs <;> apply atTile <;> dsimp [leftCol,a] <;> push_cast <;> omega

private theorem teeth_decode (d l t : Nat) (W : StepWindow u l t)
    {q j : Nat} (dq : d=2+3*q) (lq : l=leftCol q) (qlo : 3≤q) (hj : j<bands u)
    (r : Fin 3) (eq : t=3*j+r.val) :
    pinMask (u:=u) d l (t+1) = if r.val=1 then toothNo (bands u) j else 0 := by
  unfold pinMask
  have Q : packed9 (fun i => decide (i.val≠4))=495 ∧
      packed9 (fun _ => true)=511 ∧ packed9 (fun _ => false)=0 := by decide
  by_cases north : t+1=2
  · have rr : r.val=1 := by have := r.isLt; omega
    have jj : j=0 := by have := r.isLt; omega
    have f : (fun i : Fin 9 => decide ((t+1=2 ∧ l+i.val≠d) ∨ t+1=high u-2))=
        (fun i => decide (i.val≠4)) := by
      funext i; apply decide_eq_decide.mpr; dsimp [leftCol,high] at *; omega
    rw [f,Q.1,rr,jj]; rfl
  · by_cases south : t+1=high u-2
    · have rr : r.val=1 ∧ j+1=bands u := by dsimp [high,bands] at *; have := r.isLt; omega
      have jn : j≠0 := by dsimp [bands] at *; omega
      simp [south,rr,jn,toothNo,Q.2.1]
    · simp only [north,south,false_and,or_self,decide_false,Q.2.2]
      unfold toothNo; split_ifs <;> dsimp [high,bands] at * <;> omega

theorem physical_push {q j : Nat} (F : Finset (Board u)) {P} (C : North.Chart F P (2+3*q))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    (qlo : 3≤q) (qhi : q+4≤bands u) (hj : j<bands u) {s : Frontier}
    (rep : Represents F (2+3*q) (leftCol q) (3*j) s) :
    ∃ s', push s (physicalWordAt F q j) (toothNo (bands u) j)=some s' ∧
      Represents F (2+3*q) (leftCol q) (3*(j+1)) s' := by
  have run (r : Fin 3) {t} (e : t=3*j+r.val) {st : Frontier} (m : Represents F (2+3*q) (leftCol q) t st) :
      ∃ z, advance st (line (physicalWordAt F q j) r) (if r.val=1 then toothNo (bands u) j else 0)=some z ∧
        Represents F (2+3*q) (leftCol q) (t+1) z := by
    have W : StepWindow u (leftCol q) t := by constructor <;> dsimp [leftCol,high,bands] at * <;> have := r.isLt <;> omega
    rw [mark_word F qlo qhi hj r,←e,←teeth_decode _ _ _ W rfl rfl qlo hj r e]
    exact physical_advance F C acy score canon W m
  obtain ⟨a,ha,ma⟩ := run 0 (by rfl) rep
  obtain ⟨b,hb,mb⟩ := run 1 (by rfl) ma
  obtain ⟨c,hc,mc⟩ := run 2 (by rfl) mb
  refine ⟨c,?_,by simpa [Nat.mul_add] using mc⟩
  unfold push
  change advance s (line (physicalWordAt F q j) 0) 0=some a at ha
  change advance a (line (physicalWordAt F q j) 1) (toothNo (bands u) j)=some b at hb
  change advance b (line (physicalWordAt F q j) 2) 0=some c at hc
  rw [ha]; change (advance a _ _ >>= _) = _; rw [hb]; exact hc

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
