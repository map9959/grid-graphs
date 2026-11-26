import GridGraphs.Geometry.CapSiteTrace

namespace GridGraphs.CapSite

structure Stencil where
  marked : Bool
  west : Bool
  east : Bool
  north : Bool
  south : Bool
deriving DecidableEq

/-- Perpendicular marked neighbors are diagonal to one another. -/
def Straight (p : Stencil) := (p.west || p.east) = false ∨ (p.north || p.south) = false
instance (p : Stencil) : Decidable (Straight p) := by unfold Straight; infer_instance
def touches (p : Stencil) : Int := one p.west + (one p.east : Int) + one p.north + one p.south
def isIso (p : Stencil) := !(p.marked || p.west || p.east || p.north || p.south)

/-- Geometric site bill, measured on the current row exactly as in the
graph ledger (center flag, mark flag, and number of marked neighbors). -/
def geometry (center : Bool) (p : Stencil) : Int :=
  (if p.marked && center then 2-touches p else 0) +
  (if !p.marked && touches p==0 then (if center then 2 else 1) else 0) +
  one (!p.marked && !center && touches p==2)

def rowPart (center : Bool) (p : Stencil) : Nat :=
  (if center then 2 else 1)*one (isIso p) +
  one (!center && !p.marked && ((p.west && p.east) || (p.north && p.south)))

/-- Endpoints already paid when this center was read, before seeing
the next row. The south-facing bond is deferred across the row cut. -/
def potential (p : Stencil) : Int :=
  (if !p.marked then 0 else 2-(one p.west : Int)-one p.east-one p.north)
def entering (p : Stencil) : Nat :=
  if p.marked then if !(p.west || p.east || p.north) then 2 else one (p.west != p.east)
  else 0

private theorem centered (m l r u d : Bool) (ok : Straight ⟨m,l,r,u,d⟩) :
    geometry true ⟨m,l,r,u,d⟩ =
    rowPart true ⟨m,l,r,u,d⟩ + potential ⟨m,l,r,u,d⟩ - one (m && d) := by
  revert ok
  cases m <;> cases l <;> cases r <;> cases u <;> cases d <;> decide

private theorem offcenter (m l r u d : Bool) (ok : Straight ⟨m,l,r,u,d⟩) :
    geometry false ⟨m,l,r,u,d⟩ = rowPart false ⟨m,l,r,u,d⟩ := by
  revert ok
  cases m <;> cases l <;> cases r <;> cases u <;> cases d <;> decide

private theorem advance (m l r u : Bool) (ok : Straight ⟨m,l,r,u,false⟩) :
    (entering ⟨m,l,r,u,false⟩ : Int) = potential ⟨m,l,r,u,false⟩ - one (u && m) := by
  revert ok
  cases m <;> cases l <;> cases r <;> cases u <;> decide

def stencil (s : Nat) (a : Row) (i : Nat) : Stencil :=
  ⟨bit (old s) (i+1),bit (old s) i,bit (old s) (i+2),bit (previous s) (i+1),bit a.mask (i+1)⟩
def stencilIn (s : Nat) (a : Row) : Stencil :=
  ⟨bit a.mask 2,bit a.mask 1,bit a.mask 3,bit (old s) 2,false⟩
def phi (s : Nat) := potential (stencil s blank 1)
def rowGeom (s : Nat) (a : Row) :=
  geometry false (stencil s a 0)+geometry true (stencil s a 1)+geometry false (stencil s a 2)
def sinks (s : Nat) (a : Row) := one (freeSink s a 0)+one (freeSink s a 1)+one (freeSink s a 2)

private theorem site_parts (s : Nat) (a : Row) (i : Nat) :
    siteCost s a i = rowPart (decide (i=1)) (stencil s a i)+2*one (freeSink s a i) := by
  unfold siteCost rowPart stencil isIso isolated
  by_cases h : i=1
  · simp [h,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]
  · simp [h,bne_iff_ne.mpr h,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]

private theorem phi_next (s : Nat) (a : Row) (bound : a.mask<32) :
    phi (nextState s a) = potential (stencilIn s a) := by
  have h : old s &&& 14 ≤ 14 := Nat.and_le_right
  have m : old (nextState s a)=a.mask := by unfold old nextState; omega
  have u : previous (nextState s a)=old s &&& 14 := by unfold previous nextState; omega
  simp only [phi,potential,stencil,stencilIn,m,u]
  simp [bit,Nat.testBit_and,show Nat.testBit 14 2 = true by decide]

/-- Exact local conservation, independent of height. Summing cancels
`phi` between consecutive rows. It starts at 2 per tooth and vanishes
when the final blank row is fed. -/
theorem row_bill (s : Nat) (a : Row) (bound : a.mask<32)
    (oldOK : ∀ i, i<3 → Straight (stencil s a i)) (newOK : Straight (stencilIn s a)) :
    (cost s a : Int)+phi s = rowGeom s a + 2*sinks s a + phi (nextState s a) := by
  have h₀ := offcenter _ _ _ _ _ (oldOK 0 (by decide))
  have h₁ := centered _ _ _ _ _ (oldOK 1 (by decide))
  have h₂ := offcenter _ _ _ _ _ (oldOK 2 (by decide))
  change geometry false (stencil s a 0)=rowPart false (stencil s a 0) at h₀
  change geometry true (stencil s a 1)=(rowPart true (stencil s a 1) : Int)+phi s-
    one (bit (old s) 2 && bit a.mask 2) at h₁
  change geometry false (stencil s a 2)=rowPart false (stencil s a 2) at h₂
  have h₃ := advance _ _ _ _ newOK
  change (endpoint s a : Int)=potential (stencilIn s a)-one (bit (old s) 2 && bit a.mask 2) at h₃
  unfold cost sinks rowGeom
  simp only [site_parts,phi_next s a bound,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    show decide (0=1)=false by decide,
    show decide (2=1)=false by decide,h₀,h₁,h₂,h₃]
  norm_num only [decide_true]
  ring

def endPadding (s : Nat) : Nat :=
  one (!bit (old s) 1)+2*one (!bit (old s) 2)+one (!bit (old s) 3)

def stripGeom (s : Nat) : List Row → Int
  | [] => rowGeom s blank + endPadding s
  | a::as => rowGeom s a + stripGeom (nextState s a) as

def stripSinks (s : Nat) : List Row → Nat
  | [] => sinks s blank
  | a::as => sinks s a + stripSinks (nextState s a) as

def stripCost (s : Nat) : List Row → Nat
  | [] => finishCost s
  | a::as => cost s a + stripCost (nextState s a) as

/-- The input consists of one slice of the orientation, recording the
five marks, three downward and four rightward arrows at each step. -/
def LocalLaws (k s : Nat) (a : Row) : Prop :=
  a.mask<32 ∧ a.down<8 ∧ a.east<16 ∧
  (k<2 → a.mask%4=0) ∧ a.mask &&& ((old s <<< 1) ||| (old s >>> 1)) = 0 ∧
  (first s → a.down=2*(k%2)) ∧
  (∀ i<4, bit a.east i → horizontal a i) ∧
  (∀ i<3, bit a.down i → vertical s a i ∧ bit (sent s) i=false) ∧
  (∀ i<3, first s=false → bit (sent s) i=false → bit a.down i=false →
    bit (old s) (i+1)=false → isolated s a i) ∧
  (∀ i<3, busy s a i ≤ 1)

private theorem local_admissible {k s a} (h : LocalLaws k s a) : admissible k s a := by
  obtain ⟨_,_,_,guard,diagonal,firstDown,east,down,blanks,slots⟩ := h
  simp only [admissible,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',
    List.all_eq_true,List.mem_range,beq_iff_eq,decide_eq_true_eq,decide_eq_false_iff_not]
  refine ⟨⟨⟨⟨or_iff_not_imp_left.mpr (by simpa using guard),diagonal⟩,?_⟩,?_⟩,?_⟩
  · cases eq : first s <;> simp_all
  · intro i hi; cases eq : bit a.east i <;> simp_all
  · intro i hi
    refine ⟨⟨?_,?_⟩,slots i hi⟩
    · cases eq : bit a.down i <;> simp_all
    · by_cases f : first s <;> by_cases p : bit (sent s) i <;>
        by_cases d : bit a.down i <;> by_cases m : bit (old s) (i+1) <;> simp_all

/-- Row-by-row vertex laws, including stopping on the extra blank row. -/
def PhysicalStrip (k s : Nat) : List Row → Prop
  | [] => LocalLaws k s blank ∧ (∀ i<3, Straight (stencil s blank i))
  | a::as => LocalLaws k s a ∧ (∀ i<3, Straight (stencil s a i)) ∧
      Straight (stencilIn s a) ∧ PhysicalStrip k (nextState s a) as

theorem strip_conservation {k s as} (physical : PhysicalStrip k s as) :
    (stripCost s as : Int)+phi s = stripGeom s as + 2*stripSinks s as := by
  induction as generalizing s with
  | nil =>
    have h := row_bill s blank (by decide) physical.2 (by left; rfl)
    have eq : phi (nextState s blank) = 0 := (phi_next s blank (by decide)).trans rfl
    rw [eq] at h
    change (finishCost s : Int)+phi s = rowGeom s blank + endPadding s + 2*sinks s blank
    have fin : finishCost s = cost s blank + endPadding s := by
      unfold finishCost endPadding; omega
    rw [fin,Nat.cast_add]; omega
  | cons a as ih =>
    obtain ⟨bounds,straight,enter,rest⟩ := physical
    have h := row_bill s a bounds.1 straight enter
    have tail := ih rest
    simp only [stripCost,stripGeom,stripSinks,Nat.cast_add]; omega

theorem physical_rows {k s as} (physical : PhysicalStrip k s as) :
    Rows k s (stripCost s as) (as.map (letter · 0)) (as.map (letter · 3)) := by
  induction as generalizing s with
  | nil => exact .endRow (local_admissible physical.1)
  | cons a as ih =>
    obtain ⟨h,_,_,rest⟩ := physical
    exact .cons h.1 h.2.1 h.2.2.1 (local_admissible h) (ih rest)

theorem physical_strip_trace (ok : tablesOK) {k as} (hk : k<4)
    (physical : PhysicalStrip k initial as) :
    GridGraphs.Slit.Trace (trans k) 0 (stripCost initial as)
      (as.map (letter · 0)) (as.map (letter · 3)) ∧
    (stripCost initial as : Int) = stripGeom initial as-2+2*stripSinks initial as := by
  have h := strip_conservation physical
  have : phi initial=2 := by decide
  exact ⟨strip_trace ok hk (physical_rows physical), by omega⟩

end GridGraphs.CapSite
