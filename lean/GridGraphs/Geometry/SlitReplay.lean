import GridGraphs.Geometry.SlitData.Tables

namespace GridGraphs.Slit.Replay
open Data

def bucket (n t : Nat) := layers[n]?.bind fun a => (a[t]?).join
def slab (n t : Nat) (z : Int) : Nat :=
  match bucket n t with
  | none => 0
  | some (lo,ids) =>
    if z < lo then 0 else if n=0 then 2 else if z≥5 then 1 else ids[(z-lo).toNat]?.getD 0

def phase (t : Nat) := if t < 2 then t else 2+(t-2)%10
def norm (t : Nat) : Int := (4*(t : Int))/5

private theorem norm_shift (t q : Nat) : norm (t+10*q) = norm t+8*q := by
  unfold norm
  push_cast
  rw [show 4*((t:ℤ)+10*q)=4*t+(8*q)*5 by ring,Int.add_mul_ediv_right _ _ (by decide)]

/-- Phase compression commutes with a single retention/waiver including
the normalization increment. No number of retained teeth is sampled. -/
theorem phase_step (t : Nat) (i : Nat) (hi : i≤1) :
    phase (phase t+i) = phase (t+i) ∧
      norm (phase t+i)-norm (phase t) = norm (t+i)-norm t := by
  constructor
  · unfold phase; split_ifs <;> omega
  · let q := (t-2)/10
    have h : t=phase t+10*q := by dsimp [q,phase]; split_ifs <;> omega
    conv_rhs => rw [h]
    rw [show phase t+10*q+i=phase t+i+10*q by omega,norm_shift,norm_shift]
    omega

structure Request where
  a : Nat
  loc : Nat
  b : Nat
  z : Nat
deriving Repr, Inhabited, DecidableEq

def Request.job (r : Request) : Job := ⟨langs[r.a]!,localTables[r.loc]!,langs[r.b]!,
  decide (r.loc=4),r.z⟩

def interval (a b : Int) := (List.range (b+1-a).toNat).map (fun (i : Nat) => a+(i : Int))

/-- Generate all affordable splits again in Lean. Include the empty slice
one below the claimed floor. At the seam old and new are both 25. -/
def extension (old new : Nat) : List Request := do
  let s ← List.range 12
  let some (lb,_) := bucket old s | []
  let drop ← [0,1]
  let kept := 1-drop
  let t := phase (s+kept)
  let some (floor,_) := bucket new t | [⟨1,4,1,0⟩] -- impossible disjointness test
  let z ← interval (floor-1) 4
  let v ← interval lb (z+norm (s+kept)-norm s)
  let a := slab old s v
  let b := slab new t z
  guard (a != 0 && b != 1)
  return ⟨a,(if old=0 then 0 else 2)+drop,b,(z+norm (s+kept)-norm s-v).toNat⟩

def maxBill (t : Nat) : Int :=
  if t=1 then 2 else 2*(t : Int)-4*((3*(t : Int)-16)/10+1)

/-- Increasing the suffix representative by ten shifts the raw price by
eight, exactly canceled by normalization. -/
theorem paired_phase (i j : Nat) :
    maxBill (i+phase j)-norm i-norm (phase j) = maxBill (i+j)-norm i-norm j := by
  by_cases small : j<2
  · simp [phase,small]
  let q := (j-2)/10
  have h : j=phase j+10*q := by dsimp [phase,q]; split_ifs; omega
  have pos : 2≤phase j := by simp [phase,small]
  conv_rhs => rw [h]
  rw [norm_shift]
  simp only [maxBill,if_neg (show i+phase j≠1 by omega),
    if_neg (show i+(phase j+10*q)≠1 by omega)]
  push_cast
  rw [show 3*((i:ℤ)+(phase j+10*q))-16=(3*(i+phase j)-16)+(3*q)*10 by ring,
    Int.add_mul_ediv_right _ _ (by decide)]
  ring

def intersections (n : Nat) : List Request := do
  let i ← List.range 3
  let j ← List.range (n+1)
  guard (0 < i+j)
  let u := phase i
  let v := phase j
  let some (lb,_) := bucket 2 u | [⟨1,4,1,0⟩]
  let some (rb,_) := bucket n v | [⟨1,4,1,0⟩]
  let cap := maxBill (i+j)-norm i-norm j
  let z ← interval lb (cap-rb)
  return ⟨slab 2 u z,4,slab n v (cap-z),0⟩

def unique (rs : List Request) := rs.eraseDups
def seam := unique (extension 25 25)
def requests := unique ((List.range 25).flatMap (fun n => extension n (n+1)) ++
  seam ++ (List.range 22).flatMap (fun i => intersections (4+i)))

def replay (rs : List Request) := rs.all (fun r => r.job.check)

theorem replay_sound {rs : List Request} (ok : replay rs) {r : Request} (h : r ∈ rs)
    {u v} (tr : Trace r.job.localRel 0 r.job.budget u v)
    (src : r.job.src.ends (r.job.src.read 1 u)) :
    (r.job.dst.ends (r.job.dst.read 1 v) != r.job.compl) = true :=
  check_sound _ (List.all_eq_true.mp ok _ h) tr src

end GridGraphs.Slit.Replay
