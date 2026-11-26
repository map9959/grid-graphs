import GridGraphs.Constructions.ResidueTwo.LowerDualReplay

/-! Random access to the physical rail marks. Coordinates are zero-based.
This implements the four zipper variants in `RESIDUE_TWO_CLASSIFICATION.md`
without storing a board or a table of parents. -/
namespace GridGraphs.ResidueTwoLower

def leftRail (l j : Nat) : Bool := j ≤ l && j%3 == 0
def rightRail (l j : Nat) : Bool := l ≤ j && j%3 == l%3
def regular (l j : Nat) := leftRail l j || rightRail (l+4) j

def band (l phase j : Nat) (whole right : Bool) :=
  let a := regular l j
  if phase == 2 then a || j == l+2
  else if whole && phase ≥ 5 then
    (a && j != (if right then l+4 else l)) ||
      j == (if phase == 5 then l+2 else if right then l+5 else l-1)
  else a

def cap (l row j : Nat) : Bool :=
  match row with
  | 3 => false
  | 4 => true
  | _ => leftRail (l-6) j || rightRail (l+4) j ||
    (if row == 0 then j == l+2 else if row == 1 then l-4 ≤ j && j < l else j == l+1)

def railLayout (n f extra i j : Nat) : Bool := Id.run do
  if i == 0 then return j < n-3 || j == n-1
  if i == 1 then return j == n-1
  if i == 2 then return j%3 == 2 || j == n-1
  if i < 3+f then
    let l := 3*(i-3)
    let r := n-1-l
    return leftRail l j || rightRail r j || (j%3 == 2 && l+5 ≤ j && j < r-4)
  let start := 3+f+extra
  if i < start then return regular (3*f) j
  let len := n-5-start
  if i ≥ n-5 then return cap (3*f-3*(len/7)) (i-(n-5)) j
  let b := (i-start)/7
  return band (3*f-3*b) ((i-start)%7) j (7*(b+1) ≤ len) false

/-- The repair shifts one mark in each affected row except the last one,
where it inserts a mark without removing the wedge mark. -/
def wireEdit (m i j : Nat) (old : Bool) : Bool := Id.run do
  if i == 0 && j == 1 then return false
  if i == 1 && j == 0 then return true
  if 2 ≤ i && 3*(i-2) ≤ m && j == 3*(i-2) then return true
  if 2 ≤ i && 3*(i-2) < m && j == 3*(i-2)+2 then return false
  return old

def zipper (n i j : Nat) : Bool :=
  let even := n%6 == 2
  let f := (n-2)/6
  let phase := n%42
  let wire := phase == 5 || phase == 11 || phase == 29
  let extra := if phase == 38 || phase == 29 then 1 else if phase == 5 then 2 else 0
  let m := if even then 3*f else if phase == 29 then 12+6*((n-71)/42)
    else if phase == 11 then 9+6*((n-53)/42) else 9+6*((n-47)/42)
  let old := railLayout n f extra i j
  if even || wire then wireEdit m i j old else old

def altFront (n a j : Nat) : Bool :=
  let l := 3*a
  j == 0 || (j < l && j%3 == 0) ||
    (l+2 ≤ j && j < n-5-l && j%3 == 2) || rightRail (n-1-l) j

def altCap (n l i j : Nat) : Bool :=
  match i with
  | 0 => leftRail l j || j == l+2 || j == n-1
  | 1 => leftRail l j || (l+5 ≤ j && j < n-2) || j == n-1
  | 2 => leftRail l j || j == l+3 || j == n-1
  | 3 => j == 0
  | _ => j != 1

def alternating (n i j : Nat) : Bool := Id.run do
  let f := (n-2)/6
  if i == 0 then return j ≥ 3 || j == 0
  if i == 1 then return j == 0
  if i < f+2 then return altFront n (i-2) j
  let b := (min i (n-5)-(f+2))/7
  let l := 3*(f-1)+3*(b%2)
  if i < n-5 then return band l ((i-(f+2))%7) j (7*(b+1) ≤ n-7-f) (b%2 == 0)
  return altCap n l (i-(n-5)) j

/-- The non-periodic small witnesses, then the 42-side construction schedule. -/
def marks (n : Nat) : Mask :=
  let small : Array Nat := match n with
    | 26 => #[67108861,1,33854025,49320521,33722953,38310473,38310473,38441545,
      38310473,38310473,38310473,38310473,38310473,38408777,38294089,38343241,
      38343241,38359625,38343241,38343241,38289993,37898313,34752777,43141409,33554433,41943037]
    | 29 => #[402653177,268435457,268435461,402653169,268435457,268435469,402653153,
      268435457,268436637,402649089,268436449,268584973,402128897,268566513,287571973,
      335544321,285212665,301989889,301989889,318767101,301989889,268435457,301989885,
      335544321,268435457,335544317,268435457,268435456,402653183]
    | 32 => #[3221225471,2147483648,2224179492,2761050401,2224179465,2425505865,
      2450670153,2453803593,2454229577,2454229577,2454360649,2454229577,2454229577,
      2453836361,2454753865,2453967433,2453967433,2455016009,2453967433,2453967433,
      2454753865,2453836361,2454229577,2454229577,2454360649,2454229577,2454229577,
      2449642057,2465239625,2449773129,2147483649,3221225469]
    | _ => #[]
  if !small.isEmpty then fun i j => small[i]!.testBit j
  else if n%42 == 14 then alternating n else zipper n

end GridGraphs.ResidueTwoLower
