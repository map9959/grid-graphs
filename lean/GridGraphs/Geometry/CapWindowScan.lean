import GridGraphs.Geometry.CapWindow

namespace GridGraphs.CapSite
open GridGraphs.CapBill
variable {r h : Nat} (F : Finset (Cell r h)) (c : Camera)

private theorem three_bits (f : Nat → Bool) :
    pack 3 f=one (f 0)+2*one (f 1)+4*one (f 2) := by
  simp only [pack,Nat.bit_val,one]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> decide

theorem state_advance (pad : Padded F) (y : Nat) :
    nextState (stateAt F c y) (rowAt F c y)=stateAt F c (y+1) := by
  have used (i : Nat) (hi : i<3) :
      busy (stateAt F c y) (rowAt F c y) i=one (usedAt F c (y+1) i) := by
    rw [actual_busy F c pad y i hi]
    have slots := four_slots F c (y+1) (i+1)
    unfold usedAt
    cases u : toward F c (y+1) (i+1) (-1) 0 <;> cases l : toward F c (y+1) (i+1) 0 (-1) <;>
      cases e : toward F c (y+1) (i+1) 0 1 <;> simp_all [one] <;> omega
  simp only [nextState,old_state,used 0 (by decide),used 1 (by decide),used 2 (by decide)]
  simp [stateAt,rowAt,three_bits,Nat.cast_add,one]

noncomputable def atStencil (y x : Int) : Stencil :=
  ⟨markBit F c y x,markBit F c y (x-1),markBit F c y (x+1),
   markBit F c (y-1) x,markBit F c (y+1) x⟩

theorem stencil_eq (y i : Nat) (hi : i<3) :
    stencil (stateAt F c y) (rowAt F c y) i = atStencil F c y ((i:ℤ)+1) := by
  have middle (m : Nat) : bit (m &&& 14) (i+1)=bit m (i+1) := by
    simp [bit,Nat.testBit_and,show (14 : Nat).testBit (i+1)=true by interval_cases i <;> decide]
  simp [stencil,atStencil,old_state,state_prev,middle,rowAt,maskAt,packed,
    show i<5 by omega, show i+1<5 by omega, show i+2<5 by omega,add_assoc]

theorem straight_at (pad : Padded F) (y x : Int) : Straight (atStencil F c y x) := by
  simp only [Straight,atStencil,Bool.or_eq_false_iff]
  by_cases l : markBit F c y (x-1) <;> by_cases e : markBit F c y (x+1) <;>
    by_cases u : markBit F c (y-1) x <;> by_cases d : markBit F c (y+1) x <;> simp_all
  all_goals first
    | exact diag_bits F c pad (Or.inr (by omega)) (Or.inl (by omega)) l u
    | exact diag_bits F c pad (Or.inl (by omega)) (Or.inl (by omega)) l d
    | exact diag_bits F c pad (Or.inr (by omega)) (Or.inr (by omega)) e u
    | exact diag_bits F c pad (Or.inl (by omega)) (Or.inr (by omega)) e d

private theorem input_straight (pad : Padded F) (y : Nat) :
    Straight (stencilIn (stateAt F c y) (rowAt F c y)) := by
  have prev := straight_at F c pad (y+1) 2
  simp [Straight,atStencil] at prev
  simpa [Straight,stencilIn,rowAt,maskAt,packed] using
    (prev.imp_right And.left)

theorem no_after (pad : Padded F) (y x : Int) (z : (h:ℤ)+1≤y) :
    markBit F c y x=false := by
  classical
  simp only [markBit,decide_eq_false_iff_not]
  rintro ⟨v,hv,eq⟩
  have := pad.bottom v hv
  have e := congrArg Prod.fst eq; change (v.1.val:ℤ)=y at e; omega

private theorem no_down_end (pad : Padded F) (x : Int) :
    toward F c h x 1 0=false := by
  apply Bool.eq_false_iff.mpr
  intro out
  have down := (toward_iff ..).mp out
  have vacant : ¬onBoard F (c.atP ((h:ℤ)+1) (x+0)) := by
    classical exact (of_decide_eq_false (no_after F c pad _ _ le_rfl))
  have exits := blank_has_sender vacant (Or.inr down)
  obtain u|l|e|d := four_directions F c exits
  · exact sends_not_reverse down (by simpa using (toward_iff ..).mp u)
  all_goals
    have mem := sends_forced ((toward_iff ..).mp (by first | exact l | exact e | exact d))
    rcases mem.2.resolve_left vacant with ⟨w,hw,eq⟩
    have := pad.bottom w hw
    have atY := congrArg Prod.fst eq
    dsimp [coord,Camera.atP] at atY
    omega

private theorem no_east_end (pad : Padded F) (x : Int) :
    toward F c ((h:ℤ)+1) x 0 1=false := by
  apply Bool.eq_false_iff.mpr; intro out
  have mem := (sends_forced ((toward_iff ..).mp out)).2
  classical
  have a := no_after F c pad ((h:ℤ)+1) x le_rfl
  have b := no_after F c pad ((h:ℤ)+1) (x+1) le_rfl
  simp_all [markBit]

private theorem pack_zero (n : Nat) (f : Nat → Bool) (z : ∀ i, f i=false) :
    pack n f=0 := by
  apply Nat.eq_of_testBit_eq
  intro i; change bit (pack n f) i=_
  rw [packed]; simp [z]

theorem stop_blank (pad : Padded F) : rowAt F c h=blank := by
  unfold rowAt maskAt
  rw [pack_zero _ _ (fun i => no_after F c pad _ i le_rfl),
    pack_zero _ _ (fun i => no_down_end F c pad _),pack_zero _ _ (fun i => no_east_end F c pad _)]
  rfl

noncomputable def scanRows (y : Nat) : Nat → List Row
  | 0 => []
  | n+1 => rowAt F c y :: scanRows (y+1) n

/-- Arbitrary-height physical extraction, for either horizontal reading
direction. The remaining arguments are solely the outer guard and top
row conditions; no constraints on a free row are assumed. -/
theorem scan_physical (pad : Padded F) (kind : Nat)
    (guard : ∀ y≤h, kind<2 → (rowAt F c y).mask%4=0)
    (top : (rowAt F c 0).down=2*(kind%2)) :
    ∀ y n, y+n=h → PhysicalStrip kind (stateAt F c y) (scanRows F c y n) := by
  intro y n
  induction n generalizing y with
  | zero =>
    intro endAt; simp at endAt; subst y
    rw [scanRows,PhysicalStrip,←stop_blank F c pad]
    refine ⟨row_laws F c pad _ _ (guard _ le_rfl) (by intro e; simpa only [e] using top),?_⟩
    intro i hi; rw [stencil_eq _ _ _ _ hi]; exact straight_at _ _ pad _ _
  | succ n ih =>
    intro size
    rw [scanRows,PhysicalStrip,state_advance _ _ pad]
    refine ⟨row_laws F c pad _ _ (guard _ (by omega)) (by rintro rfl; exact top),?_,
      input_straight F c pad y,ih _ (by omega)⟩
    intro i hi; rw [stencil_eq _ _ _ _ hi]; exact straight_at _ _ pad _ _

end GridGraphs.CapSite
