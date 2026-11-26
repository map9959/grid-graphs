import Mathlib

/-! The unsigned weighted row language of `skeleton_floor_words.priced`.
All counts are on one ordered junction line, before any pooling by labels. -/
namespace GridGraphs.NoPitch

structure Letter where
  l : Bool
  z : Bool
  r : Bool
deriving DecidableEq, Fintype, Repr, Inhabited

inductive Mode | pre | on | gap | p0 | p1
deriving DecidableEq, Repr
open Mode
instance : Fintype Mode := ⟨{pre,on,gap,p0,p1},fun m => by cases m <;> decide⟩

structure State where
  mode : Mode
  prev : Option Letter
  hit : Bool
deriving DecidableEq, Fintype, Repr

def active (a : Letter) := a.l || a.r
def pureMode (s : State) := s.mode == p0 || s.mode == p1
def I (b : Bool) : Int := b.toNat
def realized (a b : Letter) := (a.r || b.l) && (a.r || a.z) && (b.l || b.z)
def raw (s : State) (a : Letter) : Int :=
  I (active a) + I (!(active a) && !a.z) - I a.l - I a.r +
  I (s.prev.any (realized · a))

def start (pureLine : Bool) : State := ⟨if pureLine then p0 else pre,none,false⟩

/-- Preserve the old right-midpoint bit until the matching left hit is known. -/
def advance (s : State) (a : Letter) : State :=
  let mode := if pureMode s then (if !a.z then p1 else s.mode)
    else if active a then on else if s.mode=pre then pre else gap
  ⟨mode,some a, s.prev.any (fun p => p.r && !(active a))⟩

def allows (s : State) (a : Letter) (last : Bool) :=
  if pureMode s then !(active a) && (!last || (advance s a).mode != p0)
  else !last || (advance s a).mode != pre

def debit (s : State) (a : Letter) (last : Bool) : Nat :=
  if pureMode s then (s.mode == p1 && !a.z).toNat
  else (match s.prev with
    | none => 0
    | some p =>
      let missing := (active p && !p.r).toNat + (active a && !a.l).toNat
      (missing - (!(realized p a)).toNat) +
        (!(active p) && !p.z && !(s.hit || a.l)).toNat +
        (s.mode == gap && active a && !(!p.z && s.hit && a.l)).toNat) +
    (last && !(active a) && !a.z && !(s.prev.any (·.r))).toNat

/-- A local invariant, including the impossible "pure and hit" states. -/
def good (s : State) : Bool := match s.prev with
  | none => (s.mode == pre || s.mode == p0) && !s.hit
  | some a => match s.mode with
    | on => active a && !s.hit
    | pre => !(active a) && !s.hit
    | gap => !(active a)
    | p1 => !(active a) && !s.hit
    | p0 => !(active a) && a.z && !s.hit

def potential (s : State) : Int := match s.prev with
  | none => 0
  | some a => match s.mode with
    | pre => -I (!a.z)
    | on => -I (!a.r)
    | gap => -1-I (!a.z && !s.hit)
    | p0 => 0
    | p1 => -1

private theorem transition : ∀ (s : State) (a : Letter) (last : Bool),
    good s → (s.prev.isNone → a.l=false) → (last → a.r=false) → allows s a last →
    good (advance s a) ∧
    potential s + debit s a last = raw s a + (if last then -1 else potential (advance s a)) := by
  decide +kernel

def run (s : State) : List Letter → Option Nat
  | [] => some 0
  | a::as => do
    guard (allows s a as.isEmpty)
    let n ← run (advance s a) as
    return debit s a as.isEmpty + n

/-- Budget before the mandatory one-unit allowance for this line. The
initial state's `prev=none` contributes no coarse edge. -/
def total (s : State) : List Letter → Int
  | [] => 0
  | a::as => raw s a + total (advance s a) as

def endsOK (s : State) : List Letter → Prop
  | [] => True
  | a::as => (s.prev.isNone → a.l=false) ∧ (as=[] → a.r=false) ∧ endsOK (advance s a) as

private theorem telescope {s : State} {w : List Letter} (gs : good s) (hw : endsOK s w)
    (hn : w≠[]) {n} (h : run s w = some n) :
    potential s+n = total s w-1 := by
  induction w generalizing s n with
  | nil => contradiction
  | cons a as ih =>
    simp only [run,Option.bind_apply,Option.bind_eq_some_iff,Option.pure_apply,
      Option.some.injEq] at h
    obtain ⟨_,allowed,b,hb,rfl⟩ := h
    have pass : allows s a as.isEmpty := by
      by_contra! no
      simp [guard,no] at allowed
    have e := transition s a as.isEmpty gs hw.1 (by simpa using hw.2.1) pass
    cases as with
    | nil => simp [run] at hb; subst b; simpa [total,sub_eq_add_neg] using e.2
    | cons c cs =>
      have tail := ih e.1 hw.2.2 (by simp) hb
      simp only [total,List.isEmpty_cons,Nat.cast_add] at tail ⊢
      simp at e
      omega

theorem run_price {w : List Letter} {p : Bool} {n : Nat} (nonempty : w≠[])
    (ends : endsOK (start p) w) (h : run (start p) w=some n) :
    (n : Int) = total (start p) w-1 := by
  have g : good (start p) := by cases p <;> decide
  simpa [potential,start] using telescope g ends nonempty h

def containsActive (w : List Letter) := w.any active
def containsVac (w : List Letter) := w.any (fun a => !a.z)

private def ready (s : State) (w : List Letter) :=
  if pureMode s then containsActive w=false ∧ (s.mode=p1 ∨ containsVac w=true)
  else s.mode≠pre ∨ containsActive w=true

private theorem extend_ready (s : State) (a : Letter) (w : List Letter)
    (h : ready s (a::w)) : allows s a w.isEmpty ∧ ready (advance s a) w := by
  rcases s with ⟨m,prev,hit⟩; rcases a with ⟨l,z,r⟩
  cases m <;> cases l <;> cases z <;> cases r <;>
    simp_all [ready,allows,containsActive,containsVac,pureMode,advance,active]
  all_goals cases w <;> simp_all

private theorem exists_run (s : State) (w : List Letter) (h : ready s w) :
    ∃ n, run s w=some n := by
  induction w generalizing s with
  | nil => exact ⟨_,rfl⟩
  | cons a as ih =>
    obtain ⟨pass,tail⟩ := extend_ready s a as h
    obtain ⟨n,hn⟩ := ih _ tail
    exact ⟨debit s a as.isEmpty+n,by simp [run,pass,hn]⟩

theorem noPitch_accepts (w : List Letter) (hp : containsActive w ∨ containsVac w) :
    ∃ n, run (start (!containsActive w)) w=some n := by
  apply exists_run
  cases ha : containsActive w <;> simp_all [ready,start,pureMode]

/-- Realized coarse edges are counted once, even for long words. -/
def pathsFrom (last : Option Letter) : List Letter → Int
  | [] => 0
  | a::as => I (last.any (realized · a)) + pathsFrom (some a) as

def localCredit (a : Letter) : Int := I (active a)+I (!active a && !a.z)-I a.l-I a.r

theorem total_eq (s : State) (w : List Letter) :
    total s w=(w.map localCredit).sum+pathsFrom s.prev w := by
  induction w generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [total,ih,pathsFrom,List.map_cons,List.sum_cons,raw,localCredit]
    simp only [advance]
    ring

end GridGraphs.NoPitch
