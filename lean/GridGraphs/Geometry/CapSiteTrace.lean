import GridGraphs.Geometry.SlitData.Tables

/-! Sitewise semantics of the padded triple: each oriented bond has a
unique source; a vertex may send at most once. No connected-component
state is guessed by the strip verifier. -/
namespace GridGraphs.CapSite
open GridGraphs.Slit GridGraphs.Slit.Data

def bit (m i : Nat) := m.testBit i
def one (b : Bool) : Nat := if b then 1 else 0
def old (s : Nat) := s%32
def previous (s : Nat) := (s/32)%32
def sent (s : Nat) := (s/1024)%8
def first (s : Nat) := decide (s≥8192)
def initial := 4+1024*5+8192

structure Row where
  mask : Nat
  down : Nat
  east : Nat
deriving Inhabited, Repr

def vertical (s : Nat) (a : Row) (i : Nat) := bit (old s) (i+1) || bit a.mask (i+1)
def horizontal (a : Row) (j : Nat) := bit a.mask j || bit a.mask (j+1)
def isolated (s : Nat) (a : Row) (i : Nat) :=
  !(bit (old s) (i+1) || bit (previous s) (i+1) || bit a.mask (i+1) ||
    bit (old s) i || bit (old s) (i+2))

/-- Outgoing arrows already accounted for at the new site: up, left, right. -/
def busy (s : Nat) (a : Row) (i : Nat) :=
  one (vertical s a i && !bit a.down i) +
  one (horizontal a i && !bit a.east i) +
  one (horizontal a (i+1) && bit a.east (i+1))

def nextState (s : Nat) (a : Row) :=
  a.mask+32*(old s &&& 14)+1024*(busy s a 0+2*busy s a 1+4*busy s a 2)
def letter (a : Row) (j : Nat) := (a.mask/2^j)%4+4*one (bit a.east j)
def freeSink (s : Nat) (a : Row) (i : Nat) :=
  !(first s) && !(bit (sent s) i) && !(bit a.down i) && bit (old s) (i+1)

def siteCost (s : Nat) (a : Row) (i : Nat) :=
  (if i=1 then 2 else 1)*one (isolated s a i) +
  one (i != 1 && !bit (old s) (i+1) &&
    ((bit (old s) i && bit (old s) (i+2)) || (bit (previous s) (i+1) && bit a.mask (i+1)))) +
  2*one (freeSink s a i)
def endpoint (s : Nat) (a : Row) :=
  if bit a.mask 2 then
    if !(bit a.mask 1 || bit a.mask 3 || bit (old s) 2) then 2
    else one (bit a.mask 1 != bit a.mask 3)
  else 0
def cost (s : Nat) (a : Row) := siteCost s a 0+siteCost s a 1+siteCost s a 2+endpoint s a

def admissible (kind s : Nat) (a : Row) :=
  (!(kind<2) || a.mask%4==0) &&
  (a.mask &&& ((old s <<< 1) ||| (old s >>> 1)) == 0) &&
  (!(first s) || a.down == 2*(kind%2)) &&
  (List.range 4).all (fun i => !bit a.east i || horizontal a i) &&
  (List.range 3).all (fun i =>
    (!bit a.down i || (vertical s a i && !bit (sent s) i)) &&
    (first s || bit (sent s) i || bit a.down i || bit (old s) (i+1) || isolated s a i) &&
    decide (busy s a i ≤ 1))

def blank : Row := ⟨0,0,0⟩
def finishCost (s : Nat) := cost s blank +
  one (!bit (old s) 1)+2*one (!bit (old s) 2)+one (!bit (old s) 3)

def states (kind : Nat) := siteStates[kind]!
def trans (kind : Nat) := localTables[kind]!
def encode (u v q z : Nat) := u+8*v+64*q+32768*z

def rowCheck (k q s : Nat) (a : Row) :=
  !(admissible k s a) || (trans k |>.arcs q).any fun e =>
    left e == letter a 0 && right e == letter a 3 && bill e == cost s a &&
      (states k)[target e]? == some (nextState s a)

def stateCheck (k q : Nat) :=
  let s := (states k)[q]!
  (!(admissible k s blank) ||
    (0 < (trans k).stop q && (trans k).stop q ≤ finishCost s+1)) &&
  (List.range 32).all fun m => (List.range 8).all fun d => (List.range 16).all fun e =>
    rowCheck k q s ⟨m,d,e⟩

def tablesOK := (List.range 4).all fun k =>
  ((states k)[0]? == some initial) &&
  (List.range (states k).size).all (stateCheck k)

/-- Definition is in terms of marks, orientations, and vertex costs, with
no reference to any exported DFA state ID or any language acceptance. -/
inductive Rows (k : Nat) : Nat → Nat → List Nat → List Nat → Prop
  | endRow {s} : admissible k s blank → Rows k s (finishCost s) [] []
  | cons {s a z u v} : a.mask<32 → a.down<8 → a.east<16 → admissible k s a →
      Rows k (nextState s a) z u v →
      Rows k s (cost s a+z) (letter a 0::u) (letter a 3::v)

theorem rows_trace (ok : tablesOK) {k s z u v} (hk : k<4) (h : Rows k s z u v)
    {q} (hq : (states k)[q]? = some s) : Trace (trans k) q z u v := by
  simp only [tablesOK,List.all_eq_true,Bool.and_eq_true] at ok
  have all := (ok k (List.mem_range.mpr hk)).2
  induction h generalizing q with
  | endRow valid =>
    have hs := all q (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hq).1)
    simp only [stateCheck,Bool.and_eq_true] at hs
    have st := hs.1
    rw [getElem!_pos (states k) q (Array.getElem?_eq_some_iff.mp hq).1,
      (Array.getElem?_eq_some_iff.mp hq).2] at st
    simp [valid] at st
    exact .stop st.1 st.2
  | @cons s a z u v hm hd he valid tail ih =>
    have hs := all q (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hq).1)
    simp only [stateCheck,Bool.and_eq_true,List.all_eq_true] at hs
    have test := hs.2 a.mask (List.mem_range.mpr hm) a.down (List.mem_range.mpr hd)
      a.east (List.mem_range.mpr he)
    rw [getElem!_pos (states k) q (Array.getElem?_eq_some_iff.mp hq).1,
      (Array.getElem?_eq_some_iff.mp hq).2] at test
    simp [rowCheck,valid,List.any_eq_true] at test
    obtain ⟨e,mem,⟨⟨le,re⟩,price⟩,next⟩ := test
    rw [←le,←re]
    change bill e = cost s a at price
    exact .step mem (by omega) (by simpa [price] using ih next)

theorem strip_trace (ok : tablesOK) {k z u v} (hk : k<4) (h : Rows k initial z u v) :
    Trace (trans k) 0 z u v := by
  apply rows_trace ok hk h
  simpa using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok k (List.mem_range.mpr hk))).1

end GridGraphs.CapSite
