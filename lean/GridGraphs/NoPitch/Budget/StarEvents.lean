import GridGraphs.NoPitch.Budget.DecodedCorner

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset Keys GridGraphs.NoPitch.Dual
variable {k : Nat}

def bitsAt (F : Finset (Site k)) (x : Site k) (d : Fin 4) := (probe x d.val).any (fun z => decide (z∈F))

theorem sampled_bits (F : Finset (Site k)) (x : Site k) (d : Fin 4) :
    sampled x (bitsAt F x) d.val=neighbor F x d.val := by
  cases p : probe x d.val <;> simp [sampled,neighbor,bitsAt,p]

theorem bits_allowed (F : Finset (Site k)) (acy : (G F).IsAcyclic) (x : Site k) :
    allowed x (bitsAt F x) := by
  intro d e hd he
  cases a : probe x d.val with
  | none => simp
  | some u =>
    cases b : probe x e.val with
    | none => simp
    | some v =>
      simp [bitsAt,a,b] at hd he
      simp [diagonal]
      intro r; constructor <;> intro c
      · exact CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy u v hd he r (.inl c)
      · exact CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy u v hd he r (.inr c)

theorem probe_adj (x y : Site k) (d : Fin 4) (h : probe x d.val=some y) :
    (gridGraph (N k) (N k)).Adj x y := by
  unfold probe at h
  simp only [Option.dite_none_right_eq_some,Option.some.injEq] at h
  obtain ⟨bound,eq⟩ := h
  have r := congrArg (fun z : Site k => z.1.val) eq
  have c := congrArg (fun z : Site k => z.2.val) eq
  dsimp only at r c
  clear eq
  change adjacent _ _ _ _
  have small := d.isLt
  generalize d.val=v at r c bound small
  interval_cases v <;> norm_num [adjacent,Fin.ext_iff] at * <;> omega

theorem adj_probe (x y : Site k) (h : (gridGraph (N k) (N k)).Adj x y) :
    ∃ d : Fin 4, probe x d.val=some y := by
  have shift := ResidueZero.shift_out h
  let d := ResidueZero.outDir x y
  have small : d<4 := by unfold d ResidueZero.outDir; rw [if_neg h.ne]; split_ifs <;> decide
  refine ⟨⟨d,small⟩,?_⟩
  change ResidueZero.shift _ d=_ at shift
  unfold ResidueZero.shift ResidueZero.coord at shift
  have r := y.1.isLt; have c := y.2.isLt
  unfold N at r c
  change probe x d=some y
  unfold probe
  simp only [Prod.ext_iff] at shift
  interval_cases d <;> norm_num at shift ⊢ <;>
    refine ⟨by omega,Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩ <;> dsimp <;> omega

def baseBit (x : Site k) (f : Bool) (bits : Fin 4 → Bool) (d : Fin 4) :=
  (probe x d.val).any fun y => (f && decide (onRim x)) || (bits d && decide (onRim y))

theorem baseBit_iff (F : Finset (Site k)) (x : Site k) (d : Fin 4) :
    baseBit x (decide (x∈F)) (bitsAt F x) d ↔ ∃ y, probe x d.val=some y ∧ (base F).Adj x y := by
  cases p : probe x d.val with
  | none => simp [baseBit,p]
  | some y =>
    simp only [baseBit,bitsAt,p,Option.any_some,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq,Option.some.injEq,exists_eq_left']
    change _ ↔ _ ∧ (x∈skeleton F ∨ y∈skeleton F)
    simp only [skeleton,mem_filter,onRim,and_iff_right (probe_adj x y d p)]

def oldBit (x : Site k) (f : Bool) (bits : Fin 4 → Bool) :=
  decide (isJoint x ∨ ∃ d, baseBit x f bits d)

theorem oldBit_iff (F : Finset (Site k)) (x : Site k) :
    oldBit x (decide (x∈F)) (bitsAt F x) ↔ x∈oldSites F := by
  unfold oldBit
  rw [decide_eq_true_eq]
  simp only [oldSites,joints,mem_filter,mem_univ,true_and,isJoint]
  apply or_congr_right
  constructor
  · rintro ⟨d,h⟩; obtain ⟨y,_,a⟩ := (baseBit_iff ..).mp h; exact ⟨_,a⟩
  · rintro ⟨y,a⟩; obtain ⟨d,h⟩ := adj_probe x y a.1
    exact ⟨_,(baseBit_iff ..).mpr ⟨_,h,a⟩⟩

def sinkBit (x : Site k) (o : Option (Fin 4)) := decide (isJoint x) && o.isNone
def exitBit (x : Site k) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) :=
  oldBit x f bits && o.any (fun d => !(baseBit x f bits d))

theorem sinkBit_iff (F : Finset (Site k)) (x : Site k) : sinkBit x (out F x) ↔ x∈sinks F := by
  unfold sinkBit
  rw [Bool.and_eq_true,decide_eq_true_eq]
  simp [sinks,isJoint,joints,out_none]

theorem exitBit_iff (F : Finset (Site k)) (x : Site k) :
    exitBit x (decide (x∈F)) (bitsAt F x) (out F x) ↔ x∈exits F := by
  simp only [exitBit,Bool.and_eq_true,oldBit_iff,exits,mem_filter]
  cases o : out F x with
  | none => simp [(out_none F x).mp o]
  | some d =>
    have p := out_points F x d (by simp [o])
    have ne : parent F x≠x := fun h => by rw [(out_none F x).mpr h] at o; contradiction
    simp [ne,Bool.eq_false_iff,baseBit_iff,p]

def toward (x : Site k) : Fin 4 :=
  if x.2.val%3=0 then (if x.1.val%3=1 then 3 else 1) else if x.2.val%3=1 then 2 else 0
def pathBit (x : Site k) (f : Bool) (bits : Fin 4 → Bool) : Nat :=
  if onRim x ∧ ¬isJoint x then
    (bits (toward x+2)).toNat*(if f then 1 else 2*(bits (toward x)).toNat) else 0

end GridGraphs.NoPitch.Budget
