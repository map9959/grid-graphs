import GridGraphs.ResidueTwoUpper.TwoGapTurnSheet

/-! Coordinate form of the two ownership clauses of `defect_window.window`.
For an edge away from the board boundary there are four candidate owners:
the two endpoints and the two incident cells. A boundary edge has one
incident cell. There is no owner literal for the outer face. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open SimpleGraph ResidueZero

def side (f : Pos) (d : Nat) : Pos × Bool :=
  if d=0 then ((f.1,f.2+1),true) else if d=1 then ((f.1+1,f.2),false)
  else if d=2 then (f,true) else (f,false)
def port (p : Pos) (d : Nat) : Pos × Bool :=
  if d=0 then (p,false) else if d=1 then (p,true) else
  if d=2 then ((p.1,p.2-1),false) else ((p.1-1,p.2),true)
def key {n} : GridEdge n n → Pos × Bool
  | .horizontal e => ((e.row.val,e.col.val),false)
  | .vertical e => ((e.row.val,e.col.val),true)

theorem key_inj {n} : Function.Injective (key (n:=n)) := by
  rintro (⟨r,c⟩|⟨r,c⟩) (⟨s,t⟩|⟨s,t⟩) e <;> simp_all [key,Fin.ext_iff]

theorem distinct_ports (p : Pos) :
    Function.Injective (fun d : Fin 4 => port p d) ∧ Function.Injective (fun d : Fin 4 => side p d) := by
  obtain ⟨r,c⟩ := p
  constructor <;> intro i j h <;> fin_cases i <;> fin_cases j <;> simp [port,side] at h ⊢ <;> omega

theorem port_inc {n} (e : GridEdge n n) (v : GridVertex n n) (h : endsAt e v) :
    ∃! d : Fin 4, key e=port (coord v) d := by
  have ex : ∃ d : Fin 4, key e=port (coord v) d := by
    cases e with
    | horizontal e =>
      rcases h with rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨2,by simp [key,port,coord,horizontalPrimalEndpoints]⟩
    | vertical e =>
      rcases h with rfl|rfl
      · exact ⟨1,rfl⟩
      · exact ⟨3,by simp [key,port,coord,verticalPrimalEndpoints]⟩
  obtain ⟨d,hd⟩ := ex
  exact ⟨d,hd,fun _ h' => (distinct_ports _).1 (h'.symm.trans hd)⟩

theorem side_inc {n} (e : GridEdge n n) (f : Cell n) (h : incident e (face f)) :
    ∃! d : Fin 4, key e=side (coord f) d := by
  have ex : ∃ d : Fin 4, key e=side (coord f) d := by
    rcases f with ⟨r,c⟩
    cases e with
    | horizontal e =>
      rcases h with h|h
      · change (if t : e.row.val=0 then .out else GridFace.cell ⟨e.row.val-1,by omega⟩ e.col)=GridFace.cell r c at h
        split at h <;> try contradiction
        obtain ⟨a,b⟩ := GridFace.cell.inj h
        refine ⟨1,?_⟩; simp [key,side,coord,←a,←b]; omega
      · change (if t : e.row.val+1=n then .out else GridFace.cell ⟨e.row.val,by omega⟩ e.col)=GridFace.cell r c at h
        split at h <;> try contradiction
        obtain ⟨a,b⟩ := GridFace.cell.inj h
        exact ⟨3,by simp [key,side,coord,←a,←b]⟩
    | vertical e =>
      rcases h with h|h
      · change (if t : e.col.val=0 then .out else GridFace.cell e.row ⟨e.col.val-1,by omega⟩)=GridFace.cell r c at h
        split at h <;> try contradiction
        obtain ⟨a,b⟩ := GridFace.cell.inj h
        refine ⟨0,?_⟩; simp [key,side,coord,←a,←b]; omega
      · change (if t : e.col.val+1=n then .out else GridFace.cell e.row ⟨e.col.val,by omega⟩)=GridFace.cell r c at h
        split at h <;> try contradiction
        obtain ⟨a,b⟩ := GridFace.cell.inj h
        exact ⟨2,by simp [key,side,coord,←a,←b]⟩
  obtain ⟨d,hd⟩ := ex
  exact ⟨d,hd,fun _ h' => (distinct_ports _).2 (h'.symm.trans hd)⟩

def cellDir (p : Pos) (dir : Nat) := if dir=0 then (p.1,p.2-1) else if dir=1 then (p.1-1,p.2) else p
def edgeBase (p : Pos) (vertical : Bool) := if vertical then (p.1+1,p.2) else (p.1,p.2+1)
def picks (ext fs : Pos → Nat → Bool) (p : Pos) (v : Bool) : Fin 4 → Bool :=
  if v then ![ext p 1, ext (edgeBase p true) 3,fs p 2,fs (cellDir p 0) 0]
  else ![ext p 0,ext (edgeBase p false) 2,fs p 3,fs (cellDir p 1) 1]

def zeroOrOne (active : Bool) (f : Fin 4 → Bool) : Prop :=
  (active=true ↔ ∃ i, f i=true) ∧ ∀ i j, f i=true → f j=true → i=j

/-- This form applies to all coordinate edges, and can therefore be
restricted to any clipped box. Outside-cell owner bits are false. -/
structure OwnerField (n : Nat) (mark : Pos → Bool) (ext fs : Pos → Nat → Bool) : Prop where
  sites : ∀ p, inside n p → zeroOrOne (!mark p && (List.range 4).all (fun d => !mark (shift p d))) (fun d => ext p d)
  cells : ∀ p, inside (n-1) p → zeroOrOne true (fun d => fs p d)
  outer : ∀ p, ¬inside (n-1) p → ∀ d, fs p d=false
  missing : ∀ p, inside n p → ∀ d : Fin 4, ¬inside n (shift p d) → ext p d=false
  edges : ∀ p v, inside n p → inside n (edgeBase p v) →
    zeroOrOne (!(mark p || mark (edgeBase p v))) (picks ext fs p v)

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
