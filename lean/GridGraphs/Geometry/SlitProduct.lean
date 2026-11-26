import Mathlib

/-! Soundness of a finite directed-slit product check. The search used to
find candidates need not terminate at a fixed point: only a closed set
containing the initial state can certify an inclusion. -/
namespace GridGraphs.Slit

structure DFA where
  /-- Eight 9-bit successor IDs per row. Zero is the missing-edge sink. -/
  rows : Array Nat
  final : Array Bool
deriving Inhabited

def DFA.go (d : DFA) (q letter : Nat) := (d.rows[q]?.getD 0 >>> (9*letter)) % 512
def DFA.ends (d : DFA) (q : Nat) := d.final[q]?.getD false
def DFA.read (d : DFA) (q : Nat) (w : List Nat) := w.foldl d.go q

structure Local where
  /-- A row event packs left, right, target and bill (3,3,9,remaining bits). -/
  rows : Array (List Nat)
  /-- Zero for no stop; otherwise one plus the price of stopping. -/
  ends : Array Nat
deriving Inhabited

def Local.arcs (t : Local) (q : Nat) := t.rows[q]?.getD []
def Local.stop (t : Local) (q : Nat) := t.ends[q]?.getD 0
def left (e : Nat) := e%8
def right (e : Nat) := (e/8)%8
def target (e : Nat) := (e/64)%512
def bill (e : Nat) := e/32768

/-- A run on paired slit words, with an upper budget (unspent units allowed). -/
inductive Trace (t : Local) : Nat → Nat → List Nat → List Nat → Prop
  | stop {q z} : 0 < t.stop q → t.stop q ≤ z+1 → Trace t q z [] []
  | step {q z e u v} : e ∈ t.arcs q → bill e ≤ z →
      Trace t (target e) (z-bill e) u v →
      Trace t q z (left e :: u) (right e :: v)

abbrev Node := Nat × Nat × Nat × Nat
local instance {α β} [Ord α] [Ord β] : Ord (α × β) := lexOrd
def Node.a (s : Node) := s.1
def Node.q (s : Node) := s.2.1
def Node.b (s : Node) := s.2.2.1
def Node.z (s : Node) := s.2.2.2

structure Job where
  src : DFA
  localRel : Local
  dst : DFA
  /-- For a reflected intersection test, accept the complement of `dst`. -/
  compl : Bool
  budget : Nat

def Job.start (j : Job) : Node := ⟨1,0,1,j.budget⟩
def Job.next (j : Job) (s : Node) (e : Nat) : Node :=
  ⟨j.src.go s.a (left e),target e,j.dst.go s.b (right e),s.z-bill e⟩
def Job.successors (j : Job) (s : Node) : List Node :=
  ((j.localRel.arcs s.q).filter (fun e => decide (bill e ≤ s.z) &&
    j.src.go s.a (left e) != 0)).map (j.next s)
def Job.safe (j : Job) (s : Node) : Bool :=
  !(j.src.ends s.a && 0 < j.localRel.stop s.q && j.localRel.stop s.q ≤ s.z+1) ||
    (j.dst.ends s.b != j.compl)

def Job.closed (j : Job) (h : Std.TreeSet Node) :=
  h.contains j.start && h.toList.all fun s =>
    j.safe s && (j.successors s).all h.contains

/-- Only the left DFA's zero state is pruned; explicitly check that it
really is a permanent rejecting sink. -/
def DFA.validSink (d : DFA) := d.rows[0]?.getD 0 == 0 && !(d.ends 0)

private theorem sink_read (d : DFA) (h : d.validSink) (w : List Nat) :
    d.ends (d.read 0 w) = false := by
  simp [DFA.validSink] at h
  induction w with
  | nil => exact h.2
  | cons x xs ih =>
    simpa [DFA.read,DFA.go,h.1] using ih

theorem closed_sound (j : Job) (h : Std.TreeSet Node) (sink : j.src.validSink)
    (ok : j.closed h) {u v} (tr : Trace j.localRel 0 j.budget u v)
    (src : j.src.ends (j.src.read 1 u)) :
    (j.dst.ends (j.dst.read 1 v) != j.compl) = true := by
  simp only [Job.closed,Bool.and_eq_true,List.all_eq_true] at ok
  suffices ∀ {q z u v}, Trace j.localRel q z u v → ∀ a b,
      (⟨a,q,b,z⟩ : Node) ∈ h → j.src.ends (j.src.read a u) →
      (j.dst.ends (j.dst.read b v) != j.compl) = true from this tr 1 1 ok.1 src
  intro q z u v run
  induction run with
  | @stop q z pos bound =>
    intro a b mem hf
    change j.src.ends a = true at hf
    have hs := (ok.2 _ (Std.TreeSet.mem_toList.mpr mem)).1
    simpa [Job.safe,Node.a,Node.q,Node.b,Node.z,hf,pos,bound,DFA.read] using hs
  | @step q z e u v he cost tail ih =>
    intro a b mem hf
    have nz : j.src.go a (left e) ≠ 0 := by
      intro zero
      change j.src.ends (j.src.read (j.src.go a (left e)) u) = true at hf
      rw [zero,sink_read _ sink] at hf
      contradiction
    have child := (ok.2 _ (Std.TreeSet.mem_toList.mpr mem)).2
      (j.next ⟨a,q,b,z⟩ e) (List.mem_map.mpr ⟨e,List.mem_filter.mpr
        ⟨he,by simp [Node.a,Node.z,cost,nz]⟩,rfl⟩)
    exact ih _ _ child hf

/-- Candidate search only. Exhausting fuel can make `closed` fail but
cannot cause `closed_sound` to certify an invalid inclusion. -/
def discover (j : Job) : Nat → List Node → Std.TreeSet Node → Std.TreeSet Node
  | 0,_,h => h
  | _+1,[],h => h
  | gas+1,s::todo,h =>
    let (todo',h') := (j.successors s).foldl (fun (p : List Node × Std.TreeSet Node) n =>
      if p.2.contains n then p else (n::p.1,p.2.insert n)) (todo,h)
    discover j gas todo' h'

def Job.check (j : Job) : Bool :=
  j.src.validSink && j.closed (discover j 100000 [j.start] ({j.start} : Std.TreeSet Node))

theorem check_sound (j : Job) (ok : j.check) {u v}
    (tr : Trace j.localRel 0 j.budget u v) (src : j.src.ends (j.src.read 1 u)) :
    (j.dst.ends (j.dst.read 1 v) != j.compl) = true := by
  simp only [Job.check,Bool.and_eq_true] at ok
  obtain ⟨hs,hc⟩ := ok
  exact closed_sound j _ hs hc tr src

end GridGraphs.Slit
