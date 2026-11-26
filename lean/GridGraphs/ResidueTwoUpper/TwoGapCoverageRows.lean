import GridGraphs.ResidueTwoUpper.TwoGapCoverageLogic

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Catalogue ResidueZero Stencil

def patchW (p : Pos) := (List.finRange 9).map fun b => mark (plus3 p b)
def starW (p : Pos) := mark p :: (List.finRange 4).map fun d => mark (shift p d.val)
private theorem pack_eq : ∀ f : Fin 9 → Bool,
    ((List.ofFn f).foldr (fun b a => b.toNat+2*a) 0)=packed9 f := by native_decide
private theorem nb_eq : ∀ f : Fin 4 → Bool,
    ((List.ofFn f).foldr (fun b a => b.toNat+2*a) 0)=code f := by native_decide
private theorem bits_map {α} (a : Wire → Bool) (f : α → Wire) (xs : List α) :
    bits a (xs.map f)=((xs.map (a ∘ f)).foldr (fun b v => b.toNat+2*v) 0) := by
  induction xs <;> simp_all [bits]
@[simp] theorem patch_bits (l p) : bits (value l) (patchW p)=patchAt l p := by
  rw [patchW,bits_map,←List.ofFn_eq_map]; apply pack_eq
@[simp] theorem star_bits (l p) : bits (value l) (starW p)=(l.mark p).toNat+2*nbrAt l p := by
  rw [starW,bits,bits_map,←List.ofFn_eq_map,val_mark,nb_eq]; rfl

-- Only valid masks invoke the physical orbit prices. Hoist these tables:
-- every occurrence with the same representative uses the same predicate.
def pGood (p : Pos) (m : Nat) := maskOK m && twoOrbitPatch 23 p m == 0
def sGood (p : Pos) (z : Bool) (o m : Nat) := starOK 23 p (m%2) (m/2) o &&
  twoOrbitStar 23 p (m%2) (m/2) o == (if z then full else 0)
def patchTable := Array.ofFn fun r : Fin 21 => Array.ofFn fun c : Fin 21 =>
  Array.ofFn fun m : Fin 512 => pGood (r.val,c.val) m
def starTable := Array.ofFn fun r : Fin 23 => Array.ofFn fun c : Fin 23 =>
  Array.ofFn fun o : Fin 5 => Array.ofFn fun m : Fin 32 =>
    let p : Pos := (r.val,c.val)
    if starOK 23 p (m.val%2) (m.val/2) o then
      let v := twoOrbitStar 23 p (m.val%2) (m.val/2) o
      if v=0 then 1 else if v=full then 2 else 0
    else 0
def patchOK (p : Pos) (m : Nat) :=
  if 0≤p.1 ∧ p.1<21 ∧ 0≤p.2 ∧ p.2<21 ∧ m<512 then
    ((patchTable[p.1.toNat]!)[p.2.toNat]!)[m]! else pGood p m
def starOK' (p : Pos) (z : Bool) (o m : Nat) :=
  if 0≤p.1 ∧ p.1<23 ∧ 0≤p.2 ∧ p.2<23 ∧ o<5 ∧ m<32 then
    (((starTable[p.1.toNat]!)[p.2.toNat]!)[o]!)[m]! == (if z then 2 else 1)
  else sGood p z o m
private theorem patch_ok (p : Pos) (m) : patchOK p m=pGood p m := by
  unfold patchOK; split_ifs with h
  · simp [patchTable,Array.getElem?_ofFn,
      show p.1.toNat<21 by omega,show p.2.toNat<21 by omega,h.2.2.2.2,
      Int.toNat_of_nonneg h.1,Int.toNat_of_nonneg h.2.2.1]
  · rfl
private theorem star_ok (p : Pos) (z o m) : starOK' p z o m=sGood p z o m := by
  unfold starOK'; split
  · rename_i h
    simp [starTable,show p.1.toNat<23 by omega,show p.2.toNat<23 by omega,h.2.2.2.2.1,h.2.2.2.2.2,
      Int.toNat_of_nonneg h.1,Int.toNat_of_nonneg h.2.2.1,sGood]
    cases z <;> split_ifs <;> simp_all [full]
  · rfl
def dirRows (p : Pos) (o : Nat) (r : Rows) : Rows :=
  if h : o<4 then guarded (arrow p ⟨o,h⟩) true r else
    guarded (arrow p 0) false (guarded (arrow p 1) false (guarded (arrow p 2) false (guarded (arrow p 3) false r)))
theorem dir_sound (l : Field) (p : Pos) {o} (ho : o<5) (hp : l.dir p<5) (r : Rows)
    (ok : l.dir p=o → Holds (value l) r) : Holds (value l) (dirRows p o r) := by
  unfold dirRows; split_ifs
  · simpa using ok
  · simp only [holds_guarded,val_arrow,decide_eq_false_iff_not]
    intros; apply ok; omega
def starRows (s : Pos → Stamp) (p : Pos) := (List.range 5).flatMap fun o =>
  dirRows p o (truth (starW p) fun m =>
    (if rootAt s p then o==4 else o != 4 || m==0) && starOK' (starPos s p) (exitAt s p) o m)
def patchRows (s : Pos → Stamp) (p : Pos) := truth (patchW p) (patchOK (patchPos s p))

theorem star_sound {s l} (L : Local s l) (p : Pos) (h : core s p) :
    Holds (value l) (starRows s p) := by
  obtain ⟨lt,ok,fix,price⟩ := L.star p h
  apply (holds_flat ..).mpr
  intro o ho
  apply dir_sound _ _ (List.mem_range.mp ho) lt
  rintro rfl
  rw [holds_truth,star_bits,star_ok]
  have mf : (l.mark p).toNat≤1 := by cases l.mark p <;> decide
  have md : ((l.mark p).toNat+2*nbrAt l p)%2=(l.mark p).toNat := by omega
  have dv : ((l.mark p).toNat+2*nbrAt l p)/2=nbrAt l p := by omega
  simp only [sGood,md,dv,ok,price,beq_self_eq_true,Bool.and_true,Bool.true_and]
  split at fix <;> simp_all
  by_cases e : l.dir p=4
  · obtain ⟨a,b⟩ := fix e; simp [a,b]
  · simp [e]
theorem patch_sound {s l} (L : Local s l) (p : Pos) (h : halo p) (b : ∀ i : Fin 9, onB s (plus3 p i)) :
    Holds (value l) (patchRows s p) := by
  obtain ⟨v,w⟩ := L.patch p h b
  simp [patchRows,holds_truth,patch_ok,pGood,v,w]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
