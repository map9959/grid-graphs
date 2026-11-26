import GridGraphs.ResidueTwoUpper.OneGap.FanSlab

/-! A folded rectangular strip. Horizontal passes are anchored at real
ends, with separately audited closure on the three-column insertions. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSweep
open FanSlab

structure Box where
  rows : Nat  -- maximal origin index, inclusive
  cols : Nat
  loops : List Nat

def cell (G : Grid) (r c : Nat) := (G[r]!)[c]!
def build (B : Box) (f : Nat → Nat → Masks) : Grid :=
  Array.ofFn fun i : Fin (B.rows+1) => Array.ofFn fun j : Fin (B.cols+1) => f i j

def pred (B : Box) (rev : Bool) (c : Nat) : List Nat :=
  if rev then (if c=0 then [] else [c-1])++(if B.loops.contains c then [c+2] else [])
  else [c+1]++(if 2≤c && B.loops.contains (c-2) then [c-2] else [])
def dest (B : Box) (rev : Bool) (i : Nat) := if rev then B.cols-i else i
def dir (rev : Bool) := if rev then 2 else 0
private def supports (d : Nat) (m : Nat) (xs : Masks) := xs.any fun t => ov d m == ov ((d+2)%4) t
private def push (rev : Bool) (xs ys : Masks) := ys.filter fun m => supports ((dir rev+2)%4) m xs
private def vertical (B : Box) (G : Grid) := build B fun r c => (cell G r c).filter fun m =>
  (r==0 || supports 3 m (cell G (r-1) c)) && (r==B.rows || supports 1 m (cell G (r+1) c))
private def scan (B : Box) (rev : Bool) (row : Row) : Row := Id.run do
  let mut acc := Array.replicate (B.cols+1) ([] : Masks)
  for i in [:B.cols+1] do
    let c := dest B rev i
    let mut found := if i==0 then row[c]! else push rev acc[dest B rev (i-1)]! row[c]!
    if (if rev then 2≤c && B.loops.contains (c-2) else B.loops.contains c) then
      let a := row[dest B rev (i+1)]!; let b := row[dest B rev (i+2)]!
      for _ in [:64] do
        let more := (push rev (push rev (push rev found a) b) row[c]!).filter (!found.contains ·)
        if more.isEmpty then break
        found := more++found
    acc := acc.set! c found
  return acc
private def passes (B : Box) (rev : Bool) (old new : Row) := (List.range (B.cols+1)).all fun c =>
  (c != dest B rev 0 || old[c]!.all new[c]!.contains) &&
  (pred B rev c).all fun k => B.cols<k || (push rev new[c]! old[k]!).all new[k]!.contains

def check (B : Box) (endTest : Grid → Bool) : Nat → Grid → Bool
  | 0,G => endTest G
  | k+1,G =>
    let a := vertical B G; let b := a.map (scan B false); let out := b.map (scan B true)
    (List.range (B.rows+1)).all (fun r => (passes B false (a[r]!) (b[r]!)) && (passes B true (b[r]!) (out[r]!))) &&
      check B endTest k out
structure Path (B : Box) where
  last : Nat
  col : Nat → Nat
  M : Nat → Nat → Nat
  start : col 0=0
  stop : col last=B.cols
  bound : ∀ j≤last, col j≤B.cols
  next : ∀ j<last, col (j+1)∈pred B false (col j) ∧ col j∈pred B true (col (j+1))
  across : ∀ r≤B.rows, ∀ j<last, ov 0 (M r j)=ov 2 (M r (j+1))
  down : ∀ r<B.rows, ∀ j≤last, ov 1 (M r j)=ov 3 (M (r+1) j)
def Kept {B : Box} (T : Path B) (G : Grid) := ∀ r≤B.rows, ∀ j≤T.last, T.M r j∈cell G r (T.col j)
private theorem vert_sound {B : Box} {T : Path B} {G : Grid} (h : Kept T G) : Kept T (vertical B G) := by
  intro r hr j hj; have hc := T.bound _ hj
  simp [vertical,cell,build,show r<B.rows+1 by omega,show T.col j<B.cols+1 by omega]
  refine ⟨h r hr j hj,?_,?_⟩
  · cases r with
    | zero => exact .inl rfl
    | succ r => exact .inr (List.any_eq_true.mpr ⟨_,h r (by omega) j hj,beq_iff_eq.mpr (T.down r (by omega) j hj).symm⟩)
  · by_cases e : r=B.rows
    · exact .inl e
    · exact .inr (List.any_eq_true.mpr ⟨_,h (r+1) (by omega) j hj,beq_iff_eq.mpr (T.down r (by omega) j hj)⟩)
private theorem scan_sound {B : Box} {T : Path B} {G H : Grid} (rev : Bool) (old : Kept T G)
    (aud : ∀ r≤B.rows, passes B rev (G[r]!) (H[r]!)) : Kept T H := by
  intro r hr j hj
  let K (p : Nat) := T.M r p∈cell H r (T.col p)
  have ck (p : Nat) (hp : p≤T.last) := List.all_eq_true.mp (aud r hr) (T.col p) (List.mem_range.mpr (by have := T.bound p hp; omega))
  have begin' (p) (hp : p≤T.last) (base : T.col p=dest B rev 0) : K p := by
    have z := (Bool.and_eq_true_iff.mp (ck p hp)).1
    simp only [base,bne_self_eq_false,Bool.false_or] at z
    have w := old r hr p hp
    unfold K cell; rw [base]; unfold cell at w; rw [base] at w
    exact List.contains_iff_mem.mp (List.all_eq_true.mp z _ w)
  have extend (a b : Nat) (ha : a≤T.last) (hb : b≤T.last) (e : T.col b∈pred B rev (T.col a))
      (bits : ov ((dir rev+2)%4) (T.M r b)=ov (dir rev) (T.M r a)) (ka : K a) : K b := by
    have z := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (ck a ha)).2 _ e
    simp only [show ¬B.cols<T.col b by have := T.bound b hb; omega,decide_false,Bool.false_or] at z
    exact List.contains_iff_mem.mp (List.all_eq_true.mp z _ (List.mem_filter.mpr ⟨old r hr b hb,
      List.any_eq_true.mpr ⟨_,ka,by cases rev <;> exact beq_iff_eq.mpr bits⟩⟩))
  change K j
  cases rev with
  | false => induction j with
    | zero => exact begin' 0 (by omega) T.start
    | succ j ih => exact extend j (j+1) (by omega) hj (T.next j (by omega)).1 (T.across r hr j (by omega)).symm (ih (by omega))
  | true =>
    have rev (k : Nat) (hk : k≤T.last) : K (T.last-k) := by
      induction k with
      | zero => exact begin' _ le_rfl T.stop
      | succ k ih =>
        let b := T.last-(k+1); have eq : b+1=T.last-k := by dsimp [b]; omega
        exact extend (b+1) b (by dsimp [b]; omega) (by omega) (T.next b (by dsimp [b]; omega)).2
          (T.across r hr b (by dsimp [b]; omega)) (eq ▸ ih (by omega))
    simpa only [show T.last-(T.last-j)=j by omega] using rev (T.last-j) (by omega)

theorem sound {B : Box} (T : Path B) (endTest : Grid → Bool) (k : Nat) (G : Grid) (h : Kept T G) (pass : check B endTest k G) :
    ∃ H, endTest H ∧ Kept T H := by
  induction k generalizing G with
  | zero => exact ⟨G,pass,h⟩
  | succ k ih =>
    obtain ⟨audit,rest⟩ := Bool.and_eq_true_iff.mp pass
    have row (r : Nat) (hr : r≤B.rows) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp audit r (List.mem_range.mpr (by omega)))
    exact ih _ (scan_sound true (scan_sound false (vert_sound h) (fun r hr => (row r hr).1)) (fun r hr => (row r hr).2)) rest
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSweep
