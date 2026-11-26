import GridGraphs.ResidueTwoUpper.TwoGapCornerTeeth

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
open ResidueZero Stencil Words BoundarySix.Connected

def pack9 (f : Fin 9 → Nat) := (List.ofFn fun i : Fin 9 => f i <<< i.val).sum
def submask (c : Corner) (w m : Nat) (r k : Fin 3) :=
  pack9 fun q => cell c w m (row c r q) (col c k q)

theorem mask_physical {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner)
    (cm : ∀ x, isCorner x → x∈F) (line : ∀ x, Frame.straight n (coord x) → x∈F)
    (emp : ∀ x, Frame.depthAt n (coord x)=1 → x∉F) (r k : Fin 3) :
    submask c (physicalWord hn F c) (maskAt F (origin (by omega) c 2 2)) r k=
      maskAt F (origin (by omega) c r k) := by
  have bits (q : Fin 9) := (cell_physical hn F c cm line emp (row c r q) (col c k q)).trans
    (bit_site hn F c r k q).symm
  have packed : ∀ z : Fin 512, pack9 (fun q => bit z q)=z.val := by native_decide
  unfold submask; simp only [bits,packed]

def cn (m : Nat) := bit m 5 + 2*bit m 7 + 4*bit m 3 + 8*bit m 1
private def domain (c : Corner) (r k : Fin 3) (m : Nat) : Bool :=
  let p := coord (origin (n:=23) (by decide) c r k)
  maskOK m && twoOrbitPatch 23 p m==0 &&
    (List.range 5).any (fun o => starOK 23 (p+(1,1)) (bit m 4) (cn m) o &&
      twoOrbitStar 23 (p+(1,1)) (bit m 4) (cn m) o==0)

def separated (c : Corner) (m : Nat) : Bool :=
  decide (∀ r k : Fin 3, r.val+k.val≤2 →
    innerBit c m (2+r.val) (2+k.val)=(if r.val+k.val=0 then 1 else 0))

-- Materialize each base-site table only once. The criterion does not
-- constrain the perimeter exit or even require arrow agreement.
private def tab := Array.ofFn fun c : Fin 4 => Array.ofFn fun r : Fin 3 =>
  Array.ofFn fun k : Fin 3 => Array.ofFn fun m : Fin 512 => domain (cornerNo c) r k m
private theorem localCheck : ∀ (i : Fin 4) (m : Fin 512) (closedSide : Bool),
    let w := if closedSide then 3 else 12
    (∀ r k : Fin 3, (((tab[i.val]!)[r.val]!)[k.val]!)[(submask (cornerNo i) w m r k)%512]!) →
    separated (cornerNo i) m := by native_decide

private theorem centerBits {n} (F : Finset (GridVertex n n)) (a : origins n)
    (v : GridVertex n n) (eq : coord v=coord a+(1,1)) :
    bit (maskAt F a) 4=(decide (v∈F)).toNat ∧ cn (maskAt F a)=neighbours F (coord v) := by
  have bits (q : Fin 9) := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega)
    (by have := a.2.isLt; omega) q
  change ∀ (q : Fin 9), bit (maskAt F a) q=(marked F (coord a+offset q)).toNat at bits
  constructor
  · exact (bits 4).trans (by rw [←marked_at F v,eq]; rfl)
  · have b (d : Fin 4) (q : Fin 9) (e : shift (coord a+(1,1)) d=coord a+offset q) :
        bit (neighbours F (coord v)) d=bit (maskAt F a) q := by rw [neighbours_bit,bits,eq,e]
    have pack : ∀ z : Fin 16, z.val=bit z 0+2*bit z 1+4*bit z 2+8*bit z 3 := by decide +kernel
    refine Eq.trans ?_ (pack ⟨neighbours F (coord v),code_lt _⟩).symm
    change cn _=bit (neighbours F (coord v)) 0+2*_+4*_+8*_
    unfold cn
    rw [b ⟨0,by decide⟩ ⟨5,by decide⟩ (by ext <;> simp [shift,offset] <;> ring),b ⟨1,by decide⟩ ⟨7,by decide⟩ (by ext <;> simp [shift,offset] <;> ring),
        b ⟨2,by decide⟩ ⟨3,by decide⟩ (by ext <;> simp [shift,offset]),b ⟨3,by decide⟩ ⟨1,by decide⟩ (by ext <;> simp [shift,offset])]

private theorem accept {u : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (P : GridVertex (35+42*u) (35+42*u) → _)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (v : PerimeterVertex (35+42*u))
    (zero : ∀ x : occurrence (35+42*u), x≠.inl v.1 → weightAt F P x=0)
    (c : Corner) (r k : Fin 3) :
    domain c r k (maskAt F (origin (by omega) c r k)) := by
  let n := 35+42*u
  let a := origin (n:=n) (by dsimp [n]; omega) c r k
  let A := origin (n:=23) (by decide) c r k
  let p : GridVertex n n := (⟨a.1.val+1,by have := a.1.isLt; omega⟩,⟨a.2.val+1,by have := a.2.isLt; omega⟩)
  have notbd : ¬IsGridBoundary p := by
    have R := a.1.isLt; have K := a.2.isLt; dsimp [p,IsGridBoundary]; omega
  have eq : coord p=coord a+(1,1) := by ext <;> simp [p,coord]
  have K := centerBits F a p eq
  let j : Int := 4+14*u
  have N : (n:Int)=23+3*j := by dsimp [n,j]; omega
  have re : representative 23 j (coord p)=coord A+(1,1) := by
    have R := r.isLt; have C := k.isLt
    rcases c with ⟨x,y⟩; cases x <;> cases y <;> ext <;>
      dsimp [representative,rep,origin,loc,p,a,A,n,j,coord] <;> split_ifs <;> omega
  have loc := starLocation_transport (b:=23) (by decide) (j:=j) (by dsimp [j]; positivity) (coord p)
  simp only [re] at loc
  have price := zero (.inl p) (fun h => notbd (Sum.inl.inj h ▸ v.2))
  have pp := zero (.inr a) (fun h => by cases h)
  change twoOrbitPatch (35+42*(u:Int)) (coord a) _=0 at pp
  rw [transported] at pp
  change twoOrbitStar n (coord p) _ _ _=0 at price
  rw [N] at price
  have ok := starOK_physical F acy p (P p) (fun h => step _ h.symm)
  change starOK n (coord p) _ _ _=true at ok
  rw [N] at ok
  have ins (d : Nat) : inside (23+3*j) (shift (coord p) d)=inside 23 (shift (coord A+(1,1)) d) := by
    have e := congrArg (fun l : StarLocation => (l.neighbour d).isSome) (loc 0)
    simp only [starLocation,image,located] at e; split_ifs at e <;> simp_all <;> rename_i h1 h2 <;> exact h1.trans h2.symm
  unfold domain
  simp only [Bool.and_eq_true,beq_iff_eq,List.any_eq_true]
  refine ⟨⟨physical_mask_ok F acy ..,pp⟩,outDir p (P p),List.mem_range.mpr (outDir_lt ..),?_⟩
  rw [K.1,K.2]
  exact ⟨by simpa only [starOK,ins] using ok,by simpa only [twoOrbitStar,loc] using price⟩

/-- Behind every open corner, the tooth is the only mark in the inward
triangle of radius two. In particular there is no crop path from this
tooth to a different tooth through marks at depth at least two. -/
theorem open_triangle {u : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (c : Corner)
    (opened : physicalWord (by omega) F c=3 ∨ physicalWord (by omega) F c=12)
    (r k : Fin 3) (h : r.val+k.val≤2) :
    site (by omega) c ⟨2+r.val,by omega⟩ ⟨2+k.val,by omega⟩∈F ↔ r.val+k.val=0 := by
  have hn : 35≤35+42*u := by omega
  obtain ⟨P,d,step,_,_,zero,good,cases'⟩ := Frame.frame_of_score u F acy score
  obtain ⟨_,v,_,rfl⟩ := cases'.resolve_left (by omega)
  obtain ⟨i,rfl⟩ : ∃ i, c=cornerNo i := by rcases c with ⟨x,y⟩; cases x <;> cases y <;> decide
  let c := cornerNo i
  let w := physicalWord hn F c
  let m := maskAt F (origin (by omega) c 2 2)
  have cm := corners_marked u F acy score
  have line (x) := (Frame.star_geometry hn F P step x (good (.inl x))).1
  have emp (x) := (Frame.star_geometry hn F P step x (good (.inl x))).2.1
  have entries (r k : Fin 3) :
      (((tab[i.val]!)[r.val]!)[k.val]!)[(submask c w m r k)%512]! := by
    rw [mask_physical hn F c cm line emp]
    simpa [tab,Nat.mod_eq_of_lt (maskAt F (origin (by omega) c r k)).isLt,c]
      using accept F acy P step v zero c r k
  have fit : separated c m := by
    rcases opened with a|a
    · change w=3 at a; rw [a] at entries; exact localCheck i m true entries
    · change w=12 at a; rw [a] at entries; exact localCheck i m false entries
  have test := of_decide_eq_true fit r k h
  have value := cell_physical hn F c cm line emp ⟨2+r.val,by omega⟩ ⟨2+k.val,by omega⟩
  change cell c w m (2+r.val) (2+k.val)=_ at value
  simp [cell,show ¬(2+r.val=1 ∨ 2+k.val=1) by omega] at value
  rw [value] at test
  split_ifs at test with e
  · simpa [e] using test
  · exact iff_of_false (by simpa using test) e

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
