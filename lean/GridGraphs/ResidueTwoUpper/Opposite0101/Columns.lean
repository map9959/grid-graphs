import GridGraphs.ResidueTwoUpper.Opposite0101.Corner

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero

def pack7 (x : Fin 7 → Bool) := ((List.ofFn fun r => (x r).toNat <<< r.val)).sum
private theorem pack7_ok : ∀ x : Fin 7 → Bool, pack7 x<128 ∧
    ∀ r : Fin 7, bit (pack7 x) r=(x r).toNat ∧ (pack7 x).testBit r=x r := by native_decide

def point (v : Bool) (r j : Nat) : Pos := xy v (r:Int) (j:Int)
def cols {n} (F : Finset (GridVertex n n)) (v : Bool) (j : Nat) :=
  pack7 fun r => marked F (point v r j)
theorem small_col {n} (F : Finset (GridVertex n n)) (v j) : cols F v j<128 := (pack7_ok _).1
theorem read_col {n} (F : Finset (GridVertex n n)) (v j) (r : Nat) (hr : r<7) :
    bit (cols F v j) r=(marked F (point v r j)).toNat := ((pack7_ok _).2 ⟨r,hr⟩).1

theorem shared {n} (F : Finset (GridVertex n n)) (r : Fin 7) :
    crossRow (frontCols (cols F false) 7) r=cols F true r := by
  unfold crossRow
  change _=((List.ofFn fun k : Fin 7 => (marked F (point true k r)).toNat <<< k.val)).sum
  -- Both are the bit sum of the same physical row.
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hI
    have bound : i<7 := by simpa using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,prefix_at _ bound]
    rw [read_col F false i r r.isLt]; rfl

theorem colOK_physical {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : TwoGap.Words.packed (TwoGap.Words.signature (by omega) F)=TwoGap.Words.code4 0 1 0 1)
    (v : Bool) (j : Nat) (hj : j<35+42*u) : colOK v (idx u j) (cols F v j)=true := by
  have eq (r : Nat) : armBit v 35 r (idx u j)=armBit v (35+42*u) r j := by
    have B := (idx_pair hj).1
    have a (i : Nat) (hi : i≤2) : (idx u j=i ↔ j=i) ∧ (idx u j+i=35 ↔ j+i=35+42*u) := by
      unfold idx; split_ifs <;> omega
    simp only [armBit,if_neg (Nat.not_le.mpr B),if_neg (Nat.not_le.mpr hj),ne_eq,
      (a 0 (by decide)).1,(a 1 (by decide)).1,(a 2 (by decide)).1,
      (a 1 (by decide)).2,(a 2 (by decide)).2]
  simp only [colOK,List.all_eq_true,List.mem_range]
  intro r hr
  rw [eq]; split
  · rfl
  · rename_i b h
    have ph := armBit_physical F acy score canon v hr hj h
    have co : coord (vertex v r j (by omega) hj)=point v r j := by cases v <;> rfl
    rw [←marked_at,co] at ph
    exact beq_iff_eq.mpr (((pack7_ok _).2 ⟨r,hr⟩).2.trans ph)

def prev {n} (F : Finset (GridVertex n n)) (v : Bool) (j : Nat) :=
  if j=0 then 0 else cols F v (j-1)
def next {n} (F : Finset (GridVertex n n)) (v : Bool) (j : Nat) :=
  if j+1=n then 0 else cols F v (j+1)

theorem nb_physical {n} (F : Finset (GridVertex n n)) (v : Bool) (r j : Nat) (hr : r<6)
    (hj : j<n) : nbr v r (prev F v j) (cols F v j) (next F v j) =
      neighbours F (point v r j) := by
  let m := fun a b : Int => marked F (xy v a b)
  have outside (x y : Int) (h : x<0 ∨ n≤x ∨ y<0 ∨ n≤y) : m x y=false := by
    apply Bool.eq_false_iff.mpr
    intro yes; have b := marked_inside yes
    cases v <;> simp [inside,xy] at b <;> omega
  have E : bit (next F v j) r=(m r ((j:Int)+1)).toNat := by
    unfold next; split
    · rw [outside _ _ (by omega)]; simp [bit]
    · exact read_col F v (j+1) r (by omega)
  have W : bit (prev F v j) r=(m r ((j:Int)-1)).toNat := by
    unfold prev; split
    · rw [outside _ _ (by omega)]; simp [bit]
    · rw [read_col _ _ _ _ (by omega)]
      simp only [point,m,show ((j-1:Nat):Int)=(j:Int)-1 by omega]
  have U : (if r=0 then 0 else bit (cols F v j) (r-1))=(m ((r:Int)-1) j).toNat := by
    split
    · rw [outside _ _ (by omega)]; rfl
    · rw [read_col _ _ _ _ (by omega)]
      simp only [point,m,show ((r-1:Nat):Int)=(r:Int)-1 by omega]
  have D := read_col F v j (r+1) (by omega)
  have codeEq : ∀ x : Fin 4 → Bool, code x =
    (x 0).toNat+2*(x 1).toNat+4*(x 2).toNat+8*(x 3).toNat := by decide +kernel
  simp only [nbr,E,W,U,D,neighbours,codeEq]
  cases v <;> rfl

theorem mask_physical {n} (F : Finset (GridVertex n n)) (v : Bool) (r j : Nat)
    (hr : r<5) (hj : 1 ≤ j) (bound : j+1 < n) (hn : 7 ≤ n) :
    let a : origins n := xy v ⟨r,by omega⟩ ⟨j-1,by omega⟩
    pmask v r (prev F v j) (cols F v j) (next F v j) = maskAt F a := by
  dsimp only
  let a : origins n := xy v ⟨r,by omega⟩ ⟨j-1,by omega⟩
  have decode : ∀ m : Fin 512, ((List.range 9).map (fun q => bit m q <<< q)).sum = m := by native_decide
  rw [←decode (maskAt F a)]
  unfold pmask
  congr 1
  apply List.map_congr_left
  intro q hq
  have Q : q<9 := List.mem_range.mp hq
  have B := patch_bit F a.1 a.2 (by have := a.1.isLt; omega) (by have := a.2.isLt; omega) ⟨q,Q⟩
  change bit (maskAt F a) q=_ at B
  rw [B]; congr 1
  have go (dx dy : Nat) (h : dx<3 ∧ dy<3) :
      bit (if dx=0 then prev F v j else if dx=1 then cols F v j else next F v j) (r+dy)=
      (marked F (point v (r+dy) (j-1+dx))).toNat := by
    obtain ⟨hx,hy⟩ := h
    interval_cases dx <;> simp [prev,next,show j≠0 by omega,show j+1≠n by omega,
      show j-1+1=j by omega,show j-1+2=j+1 by omega,read_col,show r+dy<7 by omega]
  cases v <;> simp only [Bool.false_eq_true,if_false,if_true]
  · rw [go _ _ (by omega)]
    congr 2
  · rw [go _ _ (by omega)]
    congr 2

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
