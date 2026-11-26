import GridGraphs.NoPitch.SparseDual
import GridGraphs.Results.ExactSquareFormula

namespace GridGraphs.NoPitch.Dual

private abbrev Parser := StateT Nat Option

private def uint (b : ByteArray) : Nat → Parser Nat
  | 0 => failure
  | gas+1 => do
    let i ← get
    if h : i<b.size then
      let x := b[i].toNat
      guard (48≤x && x<112)
      set (i+1)
      if x<80 then return x-48 else return x-80+32*(←uint b gas)
    else failure

private def signed (b : ByteArray) : Parser Int := do
  let v ← uint b 20
  return if v%2=0 then (v/2:Nat) else -((v/2:Nat):Int)-1

private def parse (b : ByteArray) : Parser Chart := do
  let u := uint b 20
  let s := signed b
  let scale ← u; let nr ← u; let nc ← u
  let mut rows := #[]
  for _ in [:nr] do
    rows := rows.push ⟨←u,←u,←s,⟨←s,←s,←s⟩⟩
  let mut cols := #[]
  for _ in [:nc] do
    let key ← u; let units ← u
    let fix ← u; guard (fix≤1)
    let obj ← s; let count ← u
    let mut pos := 0; let mut terms := []
    for _ in [:count] do
      pos := pos+(←u)
      guard (pos<nr)
      terms := (pos,←s)::terms
    cols := cols.push ⟨key,units,decide (fix=1),obj,terms⟩
  let off ← get
  guard (off+1=b.size && b[off]?.map UInt8.toNat == some 10)
  return ⟨scale,rows,cols⟩

def decode (s : String) := ((parse s.toUTF8).run' 0).getD default

def chart58 := decode (include_str "Data/chart58.v32")
def chart61 := decode (include_str "Data/chart61.v32")
def chart19 := decode (include_str "Data/chart19.v32")
def chart22 := decode (include_str "Data/chart22.v32")
def chart25 := decode (include_str "Data/chart25.v32")
def chart52 := decode (include_str "Data/chart52.v32")

def tailCheck (D : Chart) (k₀ : Int) :=
  let p := rhsSum D
  let s := 2*(D.scale:Int)
  0<D.scale && D.rows.all signOK && repair D == 0 &&
    64*p.a == s*(192*k₀^2+336*k₀-79) &&
    64*p.b == s*(768*k₀+672) && 64*p.c == s*768

def finiteCheck (D : Chart) (n : Nat) :=
  0<D.scale && D.rows.all signOK &&
    (rhsSum D).a+2*(n:Int)^2*repair D < 2*(D.scale:Int)*(GridGraphs.squareScore n+1:Nat)

/-- Evaluation of the dual is a polynomial identity in the width step,
not interpolation of a fractional optimum. Feasibility is intentionally
relative to the explicit polynomial right sides in the decoded chart. -/
theorem tail_bound (D : Chart) (k₀ : Int) (ok : tailCheck D k₀) {t : Nat} {cap M : Int}
    {x} (feas : Feasible D x 8 t cap) (obj : score D x=8*M) :
    64*M ≤ 192*(k₀+2*t)^2 +336*(k₀+2*t)-79 := by
  simp only [tailCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨pos,sign⟩,zero⟩,c₀⟩,c₁⟩,c₂⟩ := ok
  have h := replay_bound D feas sign
  rw [obj,zero,mul_zero,add_zero] at h
  have eq : 64*(rhsSum D).atStep t = 2*(D.scale:Int)*
      (192*(k₀+2*t)^2+336*(k₀+2*t)-79) := by
    unfold Poly.atStep
    linear_combination c₀ + (t:ℤ)*c₁ + (t:ℤ)^2*c₂
  apply (le_of_mul_le_mul_left (a:=(2*(D.scale:Int))) (by
    calc
      2*(D.scale:Int)*(64*M) ≤ 64*(rhsSum D).atStep t := by linarith only [h]
      _ = _ := eq) (by positivity))

theorem finite_bound (D : Chart) {n M : Nat} (ok : finiteCheck D n)
    {x} (feas : Feasible D x 8 0 (8*(n:Int)^2)) (obj : score D x=8*(M:Int)) :
    M ≤ GridGraphs.squareScore n := by
  simp only [finiteCheck,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨pos,sign⟩,cut⟩ := ok
  have h := replay_bound D feas sign
  rw [obj] at h
  simp [Poly.atStep] at h
  push_cast at cut
  by_contra! gt
  have worse : (GridGraphs.squareScore n:ℤ)+1 ≤ M := by omega
  have := mul_le_mul_of_nonneg_left worse (show 0≤2*(D.scale:Int) by positivity)
  linarith

end GridGraphs.NoPitch.Dual
