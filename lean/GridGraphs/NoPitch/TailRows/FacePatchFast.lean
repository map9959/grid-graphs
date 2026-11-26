import GridGraphs.NoPitch.TailRows.FacePatchChecks

namespace GridGraphs.NoPitch.TailRows.FacePatch
open PitchCut Keys Wired FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset

/-- Factor the rotated nine-bit word from its rotated origin label. The
replay computes the former once per legal mask, the latter once per origin. -/
def word (a : Nine) : Vector Nat 8 := Vector.ofFn fun g =>
  (List.range 9).foldl (fun m j =>
    let q := small 3 (invers g) (Fin.ofNat 3 (j/3),Fin.ofNat 3 j)
    m+(a q).toNat*2^j) 0

def origin {k} (p : PatchPos k) : Vector Nat 8 := Vector.ofFn fun g => pack (patchFine p g)*512

def combine (x y : Vector Nat 8) := 8*(minimum fun g => x[g]+y[g])+4

theorem combine_eq {k} (p : PatchPos k) (a : Nine) : combine (origin p) (word a)=patchCode p a := by
  simp only [combine,origin,word,Fin.getElem_fin,Vector.getElem_ofFn,patchCode,patchFine]

def nineOf (m : Fin 512) : Nine := fun q => m.val.testBit (3*q.1.val+q.2.val)
def masks := (List.finRange 512).map nineOf
private theorem exhaust : ∀ a : Nine, a∈masks := by native_decide
def words := (masks.filter legal).map word

@[noinline] def wordScan (w : Lookup) (found : Nat → Bool) (xs : List (Vector Nat 8))
    (x y : Vector Nat 8) (seam : Bool) := xs.all fun v =>
  let key := combine x v
  found key && balanced (w key ++ negTerms (if seam then [] else w (combine y v)))

@[noinline] def fastPatches (w : Lookup) (found : Nat → Bool) (b : Nat) :=
  decide (∀ p : PatchPos b, wordScan w found words (origin p)
    (origin (proxy b (patchBand p) (p.1.val%3) (p.2.val%3))) (FacePatch.missing p))

theorem patches_sound (w found b) (ok : fastPatches w found b) : patchScan w found b := by
  unfold patchScan; simp only [decide_eq_true_eq]; intro p a legalA
  have mem : word a∈words := List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨exhaust a,legalA⟩,rfl⟩
  have h := List.all_eq_true.mp (of_decide_eq_true ok p) _ mem
  simpa only [combine_eq,FacePatch.missing,stamp,Bool.or_eq_true,beq_iff_eq] using h

@[noinline] def fastTags (D : Chart) (b : Nat) (tags : Array Nat) :=
  let s := tagged tags; let m := index D; let w := contribution D m (prices D s)
  let found := fun key => (locate D m key).isSome
  support D s && fastPatches w found b && faceScan w found b

def fastCert (D : Chart) (b : Nat) := fastTags D b (supportMasks D)
theorem fast_sound (D b) (ok : fastCert D b) : cert D b := by
  simp only [fastCert,fastTags,cert,checkTags,Bool.and_eq_true] at ok ⊢
  exact ⟨⟨ok.1.1,patches_sound _ _ _ ok.1.2⟩,ok.2⟩

end GridGraphs.NoPitch.TailRows.FacePatch
