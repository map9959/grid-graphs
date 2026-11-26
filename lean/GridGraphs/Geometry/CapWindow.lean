import GridGraphs.Geometry.CapLatticeArrows
import GridGraphs.Geometry.CapRowBill

namespace GridGraphs.CapSite
open GridGraphs.CapBill

/-- Sampling the right cap reverses the horizontal axis only. Row zero
remains the pitch row in either chart. -/
structure Camera where
  base : Int
  mirror : Bool

def Camera.atP (c : Camera) (y x : Int) : Pt :=
  (y, if c.mirror then c.base-x else c.base+x)

private theorem pinj (c : Camera) : Function.Injective (fun p : Pt => c.atP p.1 p.2) := by
  intro a b eq
  apply Prod.ext (Prod.mk.inj eq).1
  have x := (Prod.mk.inj eq).2
  split_ifs at x <;> omega

variable {r h : Nat} (F : Finset (Cell r h)) (c : Camera)
noncomputable def markBit (y x : Int) : Bool := by classical exact decide (onBoard F (c.atP y x))
noncomputable def toward (y x dy dx : Int) : Bool := by
  classical exact decide (sends F (c.atP y x) (c.atP (y+dy) (x+dx)))

theorem toward_iff (y x dy dx : Int) : toward F c y x dy dx ↔
    sends F (c.atP y x) (c.atP (y+dy) (x+dx)) := by classical simp [toward]

private theorem unique_dir {y x a b d e : Int} (f : toward F c y x a b)
    (g : toward F c y x d e) : a=d ∧ b=e := by
  have eq := sends_unique ((toward_iff ..).mp f) ((toward_iff ..).mp g)
  have z := pinj c (a₁:=(y+a,x+b)) (a₂:=(y+d,x+e)) eq
  obtain ⟨e₁,e₂⟩ := Prod.mk.inj z; omega

/-- At a physical vertex there can be at most one outgoing vertical or
horizontal arrow, in either reading direction. -/
theorem four_slots (y x : Int) :
    one (toward F c y x (-1) 0) + one (toward F c y x 0 (-1)) +
    one (toward F c y x 0 1) + one (toward F c y x 1 0) ≤ 1 := by
  have uniq := @unique_dir _ _ F c y x
  cases u : toward F c y x (-1) 0 <;> cases l : toward F c y x 0 (-1) <;>
    cases e : toward F c y x 0 1 <;> cases d : toward F c y x 1 0 <;>
    first | decide | grind

theorem opposite {y x dy dx : Int} (p : Padded F) (z : 0≤y) (z' : 0≤y+dy)
    (dir : (dy=0 ∧ (dx=1 ∨ dx= -1)) ∨ (dx=0 ∧ (dy=1 ∨ dy= -1))) :
    ((markBit F c y x || markBit F c (y+dy) (x+dx)) && !toward F c y x dy dx) =
      toward F c (y+dy) (x+dx) (-dy) (-dx) := by
  classical
  have near : unitEdge (c.atP y x) (c.atP (y+dy) (x+dx)) := by
    unfold unitEdge Camera.atP; cases c.mirror <;> simp_all <;> omega
  have edge := oriented_bond p z z' near
  have no := @sends_not_reverse _ _ F (c.atP y x) (c.atP (y+dy) (x+dx))
  apply Bool.eq_iff_iff.mpr
  simp [markBit,toward]
  tauto

def pack : Nat → (Nat → Bool) → Nat
  | 0,_ => 0
  | n+1,f => Nat.bit (f 0) (pack n (fun i => f (i+1)))

theorem packed (n : Nat) (f : Nat → Bool) (i : Nat) :
    bit (pack n f) i = if i<n then f i else false := by
  induction n generalizing f i with
  | zero => simp [pack,bit]
  | succ n ih =>
    cases i with
    | zero => simp [pack,bit]
    | succ i => simpa [pack,bit,Nat.testBit_bit_succ] using ih (fun j => f (j+1)) i

theorem pack_lt (n : Nat) (f : Nat → Bool) : pack n f < 2^n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,Nat.bit_val,pow_succ]
    have := ih (fun i => f (i+1)); cases f 0 <;> simp <;> omega

noncomputable def maskAt (y : Int) := pack 5 (fun i => markBit F c y i)
noncomputable def usedAt (y : Int) (i : Nat) := toward F c y (i+1) (-1) 0 ||
  toward F c y (i+1) 0 (-1) || toward F c y (i+1) 0 1
noncomputable def stateAt (y : Nat) :=
  maskAt F c y + 32*((maskAt F c ((y:ℤ)-1)) &&& 14) +
    1024*(pack 3 (usedAt F c y)) + 8192*one (decide (y=0))
noncomputable def rowAt (y : Nat) : Row :=
  ⟨maskAt F c (y+1), pack 3 (fun i => toward F c y (i+1) 1 0),
    pack 4 (fun i => toward F c (y+1) i 0 1)⟩

@[simp] theorem old_state (y : Nat) : old (stateAt F c y)=maskAt F c y := by
  have := pack_lt 5 (fun i => markBit F c y i)
  change maskAt F c y<32 at this; unfold old stateAt; omega

@[simp] theorem sent_state (y : Nat) : sent (stateAt F c y)=pack 3 (usedAt F c y) := by
  have b := pack_lt 5 (fun i => markBit F c y i)
  change maskAt F c y<32 at b
  have a : maskAt F c ((y:ℤ)-1) &&& 14 ≤ 14 := Nat.and_le_right
  have d := pack_lt 3 (usedAt F c y); change _<8 at d
  unfold sent stateAt; omega

theorem actual_busy (pad : Padded F) (y i : Nat) (hi : i<3) :
    busy (stateAt F c y) (rowAt F c y) i =
      one (toward F c (y+1) (i+1) (-1) 0) + one (toward F c (y+1) (i+1) 0 (-1)) +
        one (toward F c (y+1) (i+1) 0 1) := by
  have up := opposite F c (y:=(y:ℤ)) (x:=(i:ℤ)+1) (dy:=1) (dx:=0) pad (by omega)
    (by omega) (by simp)
  have left := opposite F c (y:=(y:ℤ)+1) (x:=(i:ℤ)) (dy:=0) (dx:=1) pad (by omega)
    (by omega) (by simp)
  have right := opposite F c (y:=(y:ℤ)+1) (x:=(i:ℤ)+1) (dy:=0) (dx:=1) pad (by omega)
    (by omega) (by simp)
  have sound : toward F c ((y:ℤ)+1) ((i:ℤ)+1) 0 1 = true →
      (markBit F c ((y:ℤ)+1) ((i:ℤ)+1) || markBit F c ((y:ℤ)+1) ((i:ℤ)+2)) = true := by
    intro out
    have mem := (sends_forced ((toward_iff ..).mp out)).2
    simpa [markBit,add_assoc] using mem
  simp only [add_zero,Int.neg_zero,Int.reduceNeg] at up left
  simp only [busy,vertical,horizontal,rowAt,old_state,maskAt,packed,
    if_pos hi,if_pos (show i<4 by omega),if_pos (show i+1<4 by omega),
    if_pos (show i<5 by omega),if_pos (show i+1<5 by omega),
    if_pos (show i+(1:Nat)+1<5 by omega),Nat.cast_add,Nat.cast_one]
  rw [up,left]
  congr 1
  have both := Bool.and_eq_right_iff_imp.mpr sound
  simpa [add_assoc] using congrArg one both

private theorem forced_bits {y x dy dx : Int} (out : toward F c y x dy dx) :
    markBit F c y x || markBit F c (y+dy) (x+dx) := by
  classical
  simpa only [markBit,Bool.or_eq_true,decide_eq_true_eq] using
    (sends_forced ((toward_iff ..).mp out)).2

theorem diag_bits (pad : Padded F) {y z x w : Int} (dy : y+1=z ∨ z+1=y)
    (dx : x+1=w ∨ w+1=x) (a : markBit F c y x) (b : markBit F c z w) : False := by
  classical
  simp only [markBit,decide_eq_true_eq] at a b
  obtain ⟨v,hv,vp⟩ := a
  obtain ⟨u,hu,up⟩ := b
  obtain ⟨y₁,x₁⟩ := Prod.mk.inj vp
  obtain ⟨y₂,x₂⟩ := Prod.mk.inj up
  apply no_diagonal_marks pad hv hu
  · omega
  · split_ifs at x₁ x₂ <;> omega

private theorem no_diag_mask (pad : Padded F) (y : Nat) :
    maskAt F c (y+1) &&& ((maskAt F c y <<< 1) ||| (maskAt F c y >>> 1))=0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,
    Nat.zero_testBit]
  change (bit (maskAt F c _) i && ((decide (i≥1) && bit (maskAt F c _) (i-1)) ||
    bit (maskAt F c _) (1+i)))=false
  simp only [maskAt,packed]
  split_ifs <;> try simp only [Bool.and_false,Bool.false_and,Bool.false_or,Bool.or_false]
  all_goals apply Bool.eq_false_iff.mpr; intro h
  all_goals simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  all_goals rcases h with ⟨m,h⟩
  all_goals first
    | exact diag_bits F c pad (Or.inr rfl) (Or.inr (by omega)) m h.2
    | exact diag_bits F c pad (Or.inr rfl) (Or.inl (by omega)) m h
    | rcases h with ⟨ge,a⟩|a
      · exact diag_bits F c pad (Or.inr rfl) (Or.inr (by omega)) m a
      · exact diag_bits F c pad (Or.inr rfl) (Or.inl (by omega)) m a

theorem four_directions {y x : Int} (existsOut : ∃ q, sends F (c.atP y x) q) :
    toward F c y x (-1) 0 ∨ toward F c y x 0 (-1) ∨ toward F c y x 0 1 ∨ toward F c y x 1 0 := by
  obtain ⟨⟨a,b⟩,out⟩ := existsOut
  have near := (sends_forced out).1
  have eq : (a,b)=c.atP (y+ -1) (x+0) ∨ (a,b)=c.atP (y+0) (x+ -1) ∨
      (a,b)=c.atP (y+0) (x+1) ∨ (a,b)=c.atP (y+1) (x+0) := by
    simp only [unitEdge,Camera.atP,Prod.mk.injEq] at near ⊢
    split_ifs at near ⊢ <;> omega
  simp only [toward_iff]
  rcases eq with e|e|e|e <;> rw [e] at out <;> tauto

private theorem blank_rule (pad : Padded F) {y x : Int} (pos : 0<y)
    (blankSite : markBit F c y x=false)
    (noUp : toward F c y x (-1) 0=false) (noLeft : toward F c y x 0 (-1)=false)
    (noRight : toward F c y x 0 1=false) (noDown : toward F c y x 1 0=false) :
    markBit F c (y-1) x=false ∧ markBit F c (y+1) x=false ∧
    markBit F c y (x-1)=false ∧ markBit F c y (x+1)=false := by
  classical
  have noSend : ¬∃ q, sends F (c.atP y x) q := by
    intro out; have := four_directions F c out; simp_all
  have nm : ¬onBoard F (c.atP y x) := by simpa [markBit] using blankSite
  have notNear (a b : Int) (near : unitEdge (c.atP y x) (c.atP a b)) (z : 0≤a) :
      markBit F c a b=false := by
    simp only [markBit,decide_eq_false_iff_not]; intro m
    have bond := (oriented_bond pad (p:=c.atP y x) (q:=c.atP a b) (by exact pos.le) z near).mpr
      (Or.inr m)
    exact noSend (blank_has_sender nm bond)
  refine ⟨notNear (y-1) x ?_ (by omega),notNear (y+1) x ?_ (by omega),
    notNear y (x-1) ?_ (by omega),notNear y (x+1) ?_ (by omega)⟩ <;>
    simp only [unitEdge,Camera.atP] <;> split_ifs <;> grind

theorem state_first (y : Nat) : first (stateAt F c y)=decide (y=0) := by
  have b := pack_lt 5 (fun i => markBit F c y i); change maskAt F c y<32 at b
  have d := pack_lt 3 (usedAt F c y); change _<8 at d
  have a : maskAt F c ((y:ℤ)-1) &&& 14 ≤ 14 := Nat.and_le_right
  unfold first stateAt; by_cases z : y=0 <;> simp only [z,decide_true,decide_false,one,
    ite_true] <;> apply Bool.eq_iff_iff.mpr <;> simp; omega

theorem state_prev (y : Nat) :
    previous (stateAt F c y)= maskAt F c ((y:ℤ)-1) &&& 14 := by
  have b := pack_lt 5 (fun i => markBit F c y i); change maskAt F c y<32 at b
  have a : maskAt F c ((y:ℤ)-1) &&& 14 ≤ 14 := Nat.and_le_right
  unfold previous stateAt; omega

private theorem iso_read (y i : Nat) (hi : i<3) : isolated (stateAt F c y) (rowAt F c y) i =
    !(markBit F c y ((i:ℤ)+1) || markBit F c ((y:ℤ)-1) ((i:ℤ)+1) ||
      markBit F c ((y:ℤ)+1) ((i:ℤ)+1) || markBit F c y i || markBit F c y ((i:ℤ)+2)) := by
  have middle (n : Nat) : bit (n &&& 14) (i+1)=bit n (i+1) := by
    simp only [bit,Nat.testBit_and,show (14 : Nat).testBit (i+1)=true by interval_cases i <;> decide,
      Bool.and_true]
  simp [isolated,state_prev,middle,rowAt,maskAt,packed,show i+1<5 by omega,
    show i<5 by omega,show i+2<5 by omega]

/-- A real parent orientation satisfies the strip's vertex tests at every
row, independent of its neighboring strip. The two geometric boundary
premises describe only the left guard and the terminal spoke. -/
theorem row_laws (pad : Padded F) (k y : Nat)
    (guard : k<2 → (rowAt F c y).mask%4=0)
    (top : y=0 → (rowAt F c y).down=2*(k%2)) :
    LocalLaws k (stateAt F c y) (rowAt F c y) := by
  refine ⟨pack_lt _ _,pack_lt _ _,pack_lt _ _,guard,?_,?_,?_,?_,?_,?_⟩
  · simpa [rowAt] using no_diag_mask F c pad y
  · rw [state_first]; simpa using top
  · intro i hi
    simp only [rowAt,packed,if_pos hi,horizontal,maskAt,if_pos (show i<5 by omega),
      if_pos (show i+1<5 by omega),Nat.cast_add,Nat.cast_one]
    simpa using (forced_bits F c (y:=y+1) (x:=i) (dy:=0) (dx:=1))
  · intro i hi
    simp only [rowAt,packed,if_pos hi,vertical,old_state,maskAt,if_pos (show i+1<5 by omega),
      sent_state,Nat.cast_add,Nat.cast_one]
    intro down
    have mark := forced_bits F c down
    have slots := four_slots F c y ((i:ℤ)+1)
    refine ⟨by simpa using mark,?_⟩
    unfold usedAt
    cases u : toward F c y ((i:ℤ)+1) (-1) 0 <;> cases l : toward F c y ((i:ℤ)+1) 0 (-1) <;>
      cases r : toward F c y ((i:ℤ)+1) 0 1 <;> simp_all [one]
  · intro i hi
    simp only [state_first,decide_eq_false_iff_not,sent_state,packed,if_pos hi,
      rowAt,old_state,maskAt,if_pos (show i+1<5 by omega),Nat.cast_add,Nat.cast_one]
    intro nz used d m
    have non := blank_rule F c pad (by omega : 0<(y:ℤ)) m
    simp only [usedAt,Bool.or_eq_false_iff] at used
    have h := non used.1.1 used.1.2 used.2 d
    change isolated (stateAt F c y) (rowAt F c y) i=true
    rw [iso_read F c y i hi]
    simpa [m,h.1,h.2.1,show (i:ℤ)+1-1=i by omega] using
      (show markBit F c y i=false ∧ markBit F c y ((i:ℤ)+2)=false by simpa [add_assoc] using h.2.2)
  · intro i hi
    rw [actual_busy F c pad y i hi]
    have := four_slots F c (y+1) (i+1); omega

end GridGraphs.CapSite
