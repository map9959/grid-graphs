import GridGraphs.ResidueTwoUpper.TwoGapNorthAtoms

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
open ResidueZero Stencil Words

def pack (f : Fin 6 → Bool) := ((List.finRange 6).map fun r => (f r).toNat <<< r.val).sum
private theorem pack_check : ∀ f : Fin 6 → Bool, pack f<64 ∧ ∀ r : Fin 6, bit (pack f) r=(f r).toNat := by native_decide
-- Signed columns: marks outside the strip ends are zero.
def X {n} (F : Finset (GridVertex n n)) (j : Int) := pack fun r => marked F (r,j)
theorem X_bit {n} (F : Finset (GridVertex n n)) (j : Int) (r : Nat) (hr : r<6) :
    bit (X F j) r=(marked F (r,j)).toNat := (pack_check _).2 ⟨r,hr⟩
theorem X_lt {n} (F : Finset (GridVertex n n)) (j : Int) : X F j<64 := (pack_check _).1
theorem X_off {n} (F : Finset (GridVertex n n)) {j : Int} (out : j<0 ∨ n≤j) : X F j=0 := by
  have zero : (fun r : Fin 6 => marked F (r,j))=fun _ => false := by
    funext r; apply Bool.eq_false_iff.mpr; intro m; have h := marked_inside m
    simp only [inside,Bool.and_eq_true,decide_eq_true_eq] at h; omega
  unfold X; rw [zero]; decide

theorem local_nb {u j r : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u))) (hr : r<5) :
    nbAt (X F (j-1:Int)) (X F j) (X F (j+1:Int)) r=neighbours F (r,j) := by
  let nb := neighbours F ((r:Int),(j:Int))
  have form : ∀ z : Fin 16, z.val=bit z 0+2*bit z 1+4*bit z 2+8*bit z 3 := by native_decide
  refine Eq.trans ?_ (form ⟨nb,code_lt _⟩).symm
  change nbAt (X F (j-1:Int)) (X F j) (X F (j+1:Int)) r = bit nb 0+2*bit nb 1+4*bit nb 2+8*bit nb 3
  have B (d : Fin 4) : bit nb d=(marked F (shift (r,j) d)).toNat := neighbours_bit .. 
  unfold nbAt
  rw [B ⟨0,by decide⟩,B ⟨1,by decide⟩,B ⟨2,by decide⟩,B ⟨3,by decide⟩]
  simp only [shift,X_bit F _ r (show r<6 by omega),X_bit F _ _ (show r+1<6 by omega)]
  split_ifs with h
  · subst r
    have no : marked F ((0:Int)-1,j)=false := by apply Bool.eq_false_iff.mpr; intro m; have := marked_inside m; norm_num [inside] at this
    simpa using no
  · rw [X_bit F _ (r-1) (by omega),Nat.cast_sub (by omega : 1≤r)]; rfl

private theorem window_bit (a b c : Fin 64) (r : Fin 4) (q : Fin 9) :
    bit (window a b c r) q=bit (if q.val%3=0 then a.val else if q.val%3=1 then b.val else c.val) (r.val+q.val/3) := by
  have spread (t : Nat) : pack3 t r=pack3 ((t>>>r.val)%8) 0 := by
    have tr (i : Nat) (hi : i<3) : bit ((t>>>r.val)%8) i=bit t (r.val+i) := by
      rw [show bit t (r.val+i)=bit (t>>>r.val) i by simp [bit,Nat.shiftRight_add]]
      interval_cases i <;> simp [bit,Nat.shiftRight_eq_div_pow] <;> omega
    simp [pack3,tr 0 (by decide),tr 1 (by decide),tr 2 (by decide)]
  have basic : ∀ x y z : Fin 8, ∀ i : Fin 9, bit (window x y z 0) i=
      bit (if i.val%3=0 then x.val else if i.val%3=1 then y.val else z.val) (i.val/3) := by native_decide
  let low (t : Fin 64) : Fin 8 := ⟨(t.val>>>r.val)%8,by omega⟩
  have H := basic (low a) (low b) (low c) q
  simp only [low,window,←spread] at H
  unfold window; rw [H]; split_ifs <;> rename_i h
  all_goals apply (by native_decide : ∀ (t : Fin 64) (i : Fin 4) (j : Fin 9),
    bit ((t.val>>>i.val)%8) (j.val/3)=bit t (i.val+j.val/3))

theorem patch_pass {u d j} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : Chart F P d) (acy : (Bonds F).IsAcyclic) (hj : j<35+42*u) :
    patchPass (tag u j) (X F (j-1:Int)) (X F j) (X F (j+1:Int)) := by
  by_cases end' : j=0 ∨ j+1=35+42*u
  · rcases end' with h|h
    · subst j; simp [patchPass,tag]
    · simp [patchPass,show tag u j=34 by unfold tag; split_ifs <;> omega]
  have jt : 1≤tag u j ∧ tag u j≤33 := by unfold tag; split_ifs <;> omega
  have ⟨v,_,_,zero⟩ := C.sole
  unfold patchPass
  simp only [show (tag u j==0)=false by simp; omega,show (tag u j==34)=false by simp; omega,
    Bool.false_or,List.all_eq_true,List.mem_range]
  intro r hr
  let n := 35+42*u
  let a : origins n := (⟨r,by dsimp [n]; omega⟩,⟨j-1,by dsimp [n]; omega⟩)
  let m := maskAt F a
  let W := window (X F (j-1:Int)) (X F j) (X F (j+1:Int)) r
  have E (q : Fin 9) := window_bit ⟨X F (j-1:Int),X_lt ..⟩ ⟨X F j,X_lt ..⟩ ⟨X F (j+1:Int),X_lt ..⟩ ⟨r,hr⟩ q
  have get (q : Fin 9) : bit W q=bit m q := by
    have p := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega) (by have := a.2.isLt; omega) q
    change bit m q=(marked F (coord a+offset q)).toNat at p
    rw [p,E]
    have Q := q.isLt
    split_ifs <;> rw [X_bit _ _ _ (by omega)] <;> congr 2 <;>
      ext <;> dsimp [coord,offset,a] <;> omega
  have bound : W<512 := by
    have spread (t r : Nat) : pack3 t r≤73 := by
      unfold pack3 bit; omega
    dsimp [W,window]; have := spread (X F (j-1:Int)) r; have := spread (X F j) r
    have := spread (X F (j+1:Int)) r; omega
  have eq : W=m.val := congrArg Fin.val ((by native_decide : ∀ a b : Fin 512,
    (∀ q : Fin 9, bit a q=bit b q) → a=b) ⟨W,bound⟩ m get)
  have cost := zero (.inr a) (fun h => by cases h)
  have pa : coord a=((r:Int),(j:Int)-1) := by ext <;> dsimp [coord,a] <;> omega
  change twoOrbitPatch (35+42*(u:Int)) (coord a) m=0 at cost
  rw [pa,patch_transport u j r hj hr] at cost
  have legal := physical_mask_ok F acy a.1 a.2 (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)
  change maskOK m=true at legal
  change (((pt[tag u j-1]!)[r]!)[W]!)=true
  rw [eq]
  have lim := m.isLt
  simpa [pt,patch,lim,hr,show tag u j-1<33 by omega,Nat.cast_sub jt.1] using And.intro legal cost

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
