import GridGraphs.ResidueZero.PhysicalStar
import GridGraphs.ResidueZero.PhysicalPatch
import GridGraphs.ResidueZero.Normalization

/-! The two event keys for each actual patch incidence and each shared
two-column/two-row overlap coincide. Equalities include all eight views. -/
namespace GridGraphs.ResidueZero

private def small (q : Fin 9) : Tile :=
  (⟨q.val/3,by have := q.isLt; omega⟩,⟨q.val%3,by omega⟩)

theorem patch_bit {n : Nat} (F : Finset (GridVertex n n)) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) (q : Fin 9) :
    bit (physicalMask F r c hr hc) q =
    (marked F (((r:Int),(c:Int))+offset q)).toNat := by
  let u := small q
  have site : coord (place r c hr hc u) = ((r:Int),(c:Int))+offset q := by
    ext <;> simp [coord,u,small,place,offset]
  have idx : 3*u.1.val+u.2.val=q := by change 3*(q.val/3)+q.val%3=q.val; omega
  rw [←site,marked_at]
  have h := Finset.ext_iff.mp (physicalMask_tiles F r c hr hc) u
  simp [tileMarks,idx] at h
  have bound : bit (physicalMask F r c hr hc) q < 2 := Nat.mod_lt _ (by decide)
  by_cases b : place r c hr hc u ∈ F <;> simp [b] at h ⊢ <;> omega

def patchQ (g : Nat) (q : Fin 9) : Fin 9 :=
  let v := symmetry 3 g (small q)
  ⟨3*v.1.val+v.2.val,by have := v.1.isLt; have := v.2.isLt; omega⟩

private def stepQ (q : Fin 9) (d : Fin 4) : Option (Fin 9) :=
  let u := shift (offset q) d
  if h : posIdx u < 9 ∧ inside 3 u then some ⟨_,h.1⟩ else none

private theorem patch_event_finite :
    ∀ (m : Fin 512) (q : Fin 9) (nb : Fin 16),
      (∀ (d : Fin 4) (a : Fin 9), stepQ q d=some a → bit nb d=bit m a) →
      ∀ g : Fin 8, localEvent (patchQ g q) (bit m q) (rotBits g nb) =
        localEvent (patchQ g q) (bit (rotMask g m) (patchQ g q))
          (patchNbr (rotMask g m) (patchQ g q)) := by native_decide

private theorem stepQ_pos {q a : Fin 9} {d : Fin 4} (h : stepQ q d=some a) :
    shift (offset q) d = offset a := by
  have check : ∀ (q a : Fin 9) (d : Fin 4), stepQ q d=some a → shift (offset q) d=offset a := by
    native_decide
  exact check q a d h

private theorem shift_add (u v : Pos) (d : Nat) : shift (u+v) d = u+shift v d := by
  unfold shift; split <;> ext <;> simp <;> ring

/-- An incident star and patch contribute opposite prices on the same
star/patch event, even when the event is read in a reflected view. -/
theorem physical_incidence_key {n : Nat} (F : Finset (GridVertex n n)) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) (q : Fin 9) (g : Fin 8) :
    let p : Pos := ((r:Int),(c:Int))+offset q
    let m := physicalMask F r c hr hc
    localEvent (patchQ g q) (marked F p).toNat (rotBits g (neighbours F p)) =
      localEvent (patchQ g q) (bit (rotMask g m) (patchQ g q)) (patchNbr (rotMask g m) (patchQ g q)) := by
  dsimp only
  rw [←patch_bit F r c hr hc q]
  refine patch_event_finite (physicalMask F r c hr hc) q
    ⟨neighbours F (((r:Int),(c:Int))+offset q),code_lt _⟩ ?_ g
  intro d a step
  rw [neighbours_bit F _ d,patch_bit F r c hr hc a,shift_add,stepQ_pos step]

private def commonStrip (d : Fin 2) (m m' : Nat) := ∀ q q' : Fin 9,
  offset q=shift (offset q') d → bit m q=bit m' q'

private instance (d : Fin 2) (m m' : Nat) : Decidable (commonStrip d m m') := by
  unfold commonStrip; infer_instance

private theorem strip_finite : ∀ (d : Fin 2) (m m' : Fin 512),
    commonStrip d m m' → ∀ g : Fin 8,
    overlapBits (rotMask g m) (turn g d) =
    overlapBits (rotMask g m') (turn g (d+2)) := by native_decide

/-- Shared strip key for adjacent physical patch origins. The overlap
is read row-major from each patch, after any one common square symmetry. -/
theorem physical_overlap_key {n : Nat} (F : Finset (GridVertex n n))
    {r c r' c' : Nat} (hr : r+3≤n) (hc : c+3≤n)
    (hr' : r'+3≤n) (hc' : c'+3≤n) (d : Fin 2)
    (next : ((r':Int),(c':Int)) = shift ((r:Int),(c:Int)) d) (g : Fin 8) :
    overlapBits (rotMask g (physicalMask F r c hr hc)) (turn g d) =
    overlapBits (rotMask g (physicalMask F r' c' hr' hc')) (turn g (d+2)) := by
  apply strip_finite d _ _ _ g
  intro q q' eq
  rw [patch_bit F _ _ hr hc,patch_bit F _ _ hr' hc',eq,next]
  congr 2
  fin_cases d <;> ext <;> simp [shift] <;> ring

end GridGraphs.ResidueZero
