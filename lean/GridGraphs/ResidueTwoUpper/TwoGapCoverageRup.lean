import Std.Tactic.BVDecide.LRAT.Checker

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Std.Sat Std.Tactic.BVDecide

-- The persisted witness consists of a sparse core and learned clauses.
-- Reconstruct propagation hints, then pass them to Std's proved checker.
-- Signed literals use 2*(v+1) for positive, 2*(v+1)+1 for negative.
abbrev Learned := Array (Array Nat)

namespace Witness
abbrev Reader := StateM Nat
def readVar (buf : ByteArray) : Reader Nat := do
  let mut n := 0
  for j in [:10] do
    let i ← get
    set (i+1)
    let x := (buf[i]?.getD 0).toNat
    n := n + ((x%128) <<< (7*j))
    if x<128 then return n
  return n

def decode (buf : ByteArray) : Reader (Array Nat × Learned) := do
  let mut ids := #[]
  let mut last := 0
  for _ in [:← readVar buf] do
    last := last+(← readVar buf)
    ids := ids.push last
  let mut clauses := #[]
  for _ in [:← readVar buf] do
    let mut cl := #[]
    for _ in [:← readVar buf] do cl := cl.push (← readVar buf)
    clauses := clauses.push cl
  return (ids,clauses)
end Witness

/-- A reversible literal encoding for arbitrary witness bytes. Stream
in each direction instead of allocating lists of millions of chars. -/
def witnessLiteral (buf : ByteArray) : String := Id.run do
  let mut s := ""
  for b in buf do s := s.push (Char.ofNat b.toNat)
  return s

def witnessBytes (s : String) : ByteArray := Id.run do
  let mut buf := ByteArray.emptyWithCapacity s.utf8ByteSize
  for c in s do buf := buf.push c.toNat.toUInt8
  return buf

def coreCNF (f : CNF Nat) (ids : Array Nat) : CNF Nat :=
  ⟨ids.filterMap (fun i => f.clauses[i]?) ++ f.clauses.filter (fun c => c.length==1)⟩
theorem core_unsat {f : CNF Nat} {ids} (h : (coreCNF f ids).Unsat) : f.Unsat := by
  intro a; apply Bool.eq_false_iff.mpr; intro ok
  have v := h a
  have sat : (coreCNF f ids).eval a=true := by
    simp only [CNF.eval,Array.all_eq_true] at ok ⊢
    intro i hi
    have mem := Array.getElem_mem (xs:=(coreCNF f ids).clauses) hi
    have orig : (coreCNF f ids).clauses[i] ∈ f.clauses := by
      rcases Array.mem_append.mp mem with left|right
      · obtain ⟨j,_,hj⟩ := Array.mem_filterMap.mp left; exact Array.mem_of_getElem? hj
      · exact (Array.mem_filter.mp right).1
    obtain ⟨k,hk,eq⟩ := Array.mem_iff_getElem.mp orig
    rw [←eq]; exact ok k hk
  exact Bool.noConfusion (v.symm.trans sat)

structure DB where
  clauses : Array (Array Nat)
  occurs : Array (Array Nat)
  units : Array (Nat × Nat)
def insert (db : DB) (cl : Array Nat) : DB := Id.run do
  let idx := db.clauses.size
  let mut occ := db.occurs
  for x in cl do
    occ := occ.modify x (·.push idx)
  return ⟨db.clauses.push cl,occ,if cl.size=1 then db.units.push (cl[0]!,idx) else db.units⟩
def initial (f : CNF Nat) : DB := Id.run do
  let mut db : DB := ⟨#[#[]],Array.replicate (2*(f.numLiterals+1)) #[],#[]⟩
  for c in f.clauses do
    db := insert db ((c.map fun (v,b) => 2*(v+1)+(!b).toNat).eraseDups.toArray)
  return db

def hints (db : DB) (cl : Array Nat) : Array Nat := Id.run do
  let mut known := Array.replicate db.occurs.size false
  let mut queue := #[]
  let mut reason := #[]
  for (x,id) in db.units do
    if known[x^^^1]! then return #[id]
    if !known[x]! then
      known := known.set! x true
      queue := queue.push x
  for x in cl do
    if known[x]! then return #[]
    known := known.set! (x^^^1) true
    queue := queue.push (x^^^1)
  let mut k := 0
  for _ in [:db.occurs.size] do
    if k≥queue.size then break
    let w := queue[k]!
    k := k+1
    for id in db.occurs[w^^^1]! do
      let mut next := 0
      for x in db.clauses[id]! do
        if known[x]! then
          next := 1
          break
        if !known[x^^^1]! then
          if next != 0 then
            next := 1
            break
          next := x
      if next=0 then return reason.push id
      if next>1 then
        reason := reason.push id
        known := known.set! next true
        queue := queue.push next
  return #[]

def reconstruct (f : CNF Nat) (clauses : Learned) : Array LRAT.IntAction := Id.run do
  let mut db := initial f
  let mut out := #[]
  for cl in clauses do
    let h := hints db cl
    let id := db.clauses.size
    if cl.isEmpty then return out.push (.addEmpty id h)
    let ls := cl.map fun (n : Nat) => if n%2=0 then ((n/2:Nat):Int) else -((n/2:Nat):Int)
    out := out.push (.addRup id ls h)
    db := insert db cl
  return out
def rupCheck (f : CNF Nat) (ids : Array Nat) (learned : Learned) :=
  let small := coreCNF f ids
  LRAT.check (reconstruct small learned) small
theorem rup_sound {f ids learned} (h : rupCheck f ids learned) : f.Unsat :=
  core_unsat (LRAT.check_sound _ _ h)

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
