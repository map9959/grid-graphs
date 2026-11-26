import GridGraphs.ResidueTwoUpper.OneGap.FanSlabData

/-! The 15-row shrinking-fan step. A folded horizontal row is a path,
not a cycle: retain only values reachable from each real end. The result
of each acceleration is audited by a local inductive invariant. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
open ResidueZero Stencil L7

def fan (y x : Nat) :=
  let a := 16+3*y
  let c := 19-6*y
  if x<a then 448 else if x<a+3 then [384,264,24][x-a]!
  else if x<a+3+c then 56 else if x<a+6+c then [24,12,6][x-(a+3+c)]! else 7

def transpose (m : Nat) := ((List.range 9).map fun k => lane m (3*(k%3)+k/3) <<< k).sum
def planted (r c m : Nat) := (List.range 9).all fun k =>
  let a := r+k/3; let b := c+k%3
  a>=6 || lane m k == lane (fan (a/3) (b/3)) (3*(b%3)+a%3)
abbrev Masks := List Nat
abbrev Row := Array Masks
abbrev Grid := Array Row
private def rc (c : Nat → Masks) : Row := Array.ofFn fun i : Fin 169 => c i
private def grid (r : Nat → Row) : Grid := Array.ofFn fun i : Fin 13 => r i
def get (D : Grid) (r c : Nat) := (D[r]!)[c]!
def base := grid fun r => rc fun c => (List.range 512).filter fun m => allowed r c m && planted r c m

-- Aligned positions of the three independently repeatable whole tiles.
def starts := [24,81,144]
def follows (c b : Nat) := b==c+1 || (starts.contains b && c==b+2)
def ov (d m : Nat) := match d with
  | 0 => m &&& 438 | 1 => m &&& 504 | 2 => (m &&& 219) <<< 1 | _ => (m &&& 63) <<< 3
private def supported (d : Nat) (m : Nat) (xs : Masks) := xs.any fun t => ov d m == ov ((d+2)%4) t
private def vert (D : Grid) := grid fun r => rc fun c => (get D r c).filter fun m =>
  (r==0 || supported 3 m (get D (r-1) c)) && (r==12 || supported 1 m (get D (r+1) c))
private def index (rev : Bool) (i : Nat) := if rev then 168-i else i
private def dir (rev : Bool) := if rev then 2 else 0
private def push (rev : Bool) (from' to' : Masks) := to'.filter fun m => supported ((dir rev+2)%4) m from'
private def run (rev : Bool) (row : Row) : Row := Id.run do
  let mut acc : Row := Array.replicate 169 []
  for i in [:169] do
    let c := index rev i
    let mut entry := if i==0 then row[c]! else push rev acc[index rev (i-1)]! row[c]!
    if starts.contains (if rev then c-2 else c) && (!rev || 2≤c) then
      let a := row[index rev (i+1)]!; let b := row[index rev (i+2)]!
      for _ in [:64] do
        let more := (push rev (push rev (push rev entry a) b) row[c]!).filter (!entry.contains ·)
        if more.isEmpty then break
        entry := more++entry
    acc := acc.set! c entry
  return acc
private def audit (rev : Bool) (old new : Row) := (List.range 169).all fun c =>
  let dest := index rev c
  let dests := ([dest+1] ++ (if starts.contains (dest-2) && dest≥2 then [dest-2] else []))
  let preds := ([dest-1] ++ (if starts.contains dest then [dest+2] else []))
  ((c != 0) || old[dest]!.all new[dest]!.contains) &&
    (if rev then preds.filter (fun k => follows k dest) else dests).all (fun k =>
      k>=169 || (push rev new[dest]! old[k]!).all new[k]!.contains)
private def hor (rev : Bool) (D : Grid) : Grid := D.map (run rev)
private def round (D : Grid) := hor true (hor false (vert D))
private def passes : Nat → Grid | 0 => base | n+1 => round (passes n)
private def good (D : Grid) :=
  let a := vert D; let b := hor false a; let lastGrid := hor true b
  (List.range 13).all fun r => (audit false (a[r]!) (b[r]!)) && (audit true (b[r]!) (lastGrid[r]!))
private def validate : Nat → Grid → Bool
  | 0,D => (List.range 57).all fun i => (get D 6 (3*i)).all fun m => m==transpose (fan 2 i)
  | t+1,D => good D && validate t (round D)
private theorem checked : validate 12 base := by native_decide

/-- Matched real rows in the folded chart. Only comparisons with physical
neighbors are assumed. Repetitions on different rows have the same width. -/
structure Trace where
  last : Nat
  column : Nat → Nat
  M : Nat → Nat → Nat
  lo : column 0=0
  hi : column last=168
  bound : ∀ j≤last, column j<169
  progress : ∀ j<last, follows (column j) (column (j+1))
  init : ∀ r<13, ∀ j≤last, M r j∈get base r (column j)
  down : ∀ r<12, ∀ j≤last, ov 1 (M r j)=ov 3 (M (r+1) j)
  right : ∀ r<13, ∀ j<last, ov 0 (M r j)=ov 2 (M r (j+1))

theorem base_mem {r c m : Nat} (hr : r<13) (hc : c<169) (hm : m<512)
    (a : allowed r c m) (p : planted r c m) : m∈get base r c := by
  simp [get,base,grid,rc,hr,hc,hm,a,p]

private def kept (T : Trace) (D : Grid) := ∀ r<13, ∀ j≤T.last, T.M r j∈get D r (T.column j)
private theorem vertical {T : Trace} {D : Grid} (keep : kept T D) : kept T (vert D) := by
  intro r hr j hj
  have hc := T.bound j hj
  simp [vert,get,grid,rc,hr,hc]
  refine ⟨keep _ hr _ hj,?_,?_⟩
  · cases r with
    | zero => exact Or.inl rfl
    | succ r => exact Or.inr (List.any_eq_true.mpr ⟨_,keep r (by omega) j hj,beq_iff_eq.mpr (T.down r (by omega) j hj).symm⟩)
  · by_cases e : r=12
    · exact Or.inl e
    · exact Or.inr (List.any_eq_true.mpr ⟨_,keep (r+1) (by omega) j hj,beq_iff_eq.mpr (T.down r (by omega) j hj)⟩)
private theorem horiz {T : Trace} {D : Grid} (s : Bool) (keep : kept T D)
    (checks : ∀ r<13, audit s D[r]! ((hor s D)[r]!)) : kept T (hor s D) := by
  intro r hr j hj
  let old := D[r]!; let new := (hor s D)[r]!
  let K (j : Nat) := T.M r j∈ new[T.column j]!
  have audit' := List.all_eq_true.mp (checks r hr)
  have begin' {j : Nat} (le : j≤T.last) (first : T.column j=index s 0) : K j := by
    have h := (Bool.and_eq_true_iff.mp (audit' 0 (by decide))).1
    have pass : old[index s 0]!.all new[index s 0]!.contains := by simpa using h
    unfold K; rw [first]; exact List.contains_iff_mem.mp (List.all_eq_true.mp pass _ (first ▸ keep r hr j le))
  have trans {a b : Nat} (lim : b≤T.last) (ca : T.column a<169)
      (e : if s then follows (T.column b) (T.column a) else follows (T.column a) (T.column b))
      (bits : ov ((dir s+2)%4) (T.M r b)=ov (dir s) (T.M r a)) (ha : K a) : K b := by
    let x := T.column a; let y := T.column b
    have lim' := T.bound b lim
    have inv : index s (index s x)=x := by cases s <;> simp [index,x] <;> omega
    have ok := (Bool.and_eq_true_iff.mp (audit' (index s x) (List.mem_range.mpr (by cases s <;> simp [index,x] <;> omega)))).2
    simp only [inv] at ok
    have following : y∈(if s then (([x-1]++(if starts.contains x then [x+2] else [])).filter fun k => follows k x)
      else [x+1]++(if starts.contains (x-2) && x≥2 then [x-2] else [])) := by
      cases s <;> dsimp [follows] at e ⊢ <;> simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at e
      · rcases e with h|⟨h1,h2⟩
        · simp [x,y,h]
        · simp only [x,y,h2,Nat.add_sub_cancel,h1,decide_true,Bool.true_and,if_true,List.mem_append,List.mem_singleton]; simp_all
      · apply List.mem_filter.mpr; refine ⟨?_,?_⟩
        · rcases e with h|⟨h1,h2⟩
          · simp [x,y,h]
          · simp [x,y,h2,List.contains_iff_mem.mp h1]
        · simpa [x,y,Bool.or_eq_true,Bool.and_eq_true] using e
    have p := List.all_eq_true.mp ok y following
    have p' : (push s new[x]! old[y]!).all new[y]!.contains := by simpa [y,show ¬169≤T.column b by omega] using p
    exact List.contains_iff_mem.mp (List.all_eq_true.mp p' _ (List.mem_filter.mpr ⟨keep r hr b lim,
      List.any_eq_true.mpr ⟨_,ha,by cases s <;> exact beq_iff_eq.mpr bits⟩⟩))
  change K j
  cases s with
  | false =>
    induction j with
    | zero => exact begin' (by omega) T.lo
    | succ j ih => exact trans hj (T.bound _ (by omega)) (T.progress j (by omega)) (T.right r hr j (by omega)).symm (ih (by omega))
  | true =>
    have rev (k : Nat) (le : k≤T.last) : K (T.last-k) := by
      induction k with
      | zero => exact begin' le_rfl T.hi
      | succ k ih =>
        let b := T.last-(k+1)
        have eq : b+1=T.last-k := by dsimp [b]; omega
        apply trans (a:=b+1) (by omega) (T.bound _ (by dsimp [b]; omega))
        · exact T.progress b (by dsimp [b]; omega)
        · exact T.right r hr b (by dsimp [b]; omega)
        · rw [eq]; exact ih (by omega)
    simpa only [show T.last-(T.last-j)=j by omega] using rev (T.last-j) (by omega)

theorem third_row (T : Trace) (i j : Nat) (hi : i<57) (hj : j≤T.last) (folded : T.column j=3*i) :
    T.M 6 j=transpose (fan 2 i) := by
  have go (n : Nat) (D : Grid) (cert : validate n D) (k : kept T D) : T.M 6 j=transpose (fan 2 i) := by
    induction n generalizing D with
    | zero => exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp cert i (List.mem_range.mpr hi)) _ (folded ▸ k 6 (by decide) j hj))
    | succ n ih =>
      obtain ⟨ok,rest⟩ := Bool.and_eq_true_iff.mp cert
      have rows (r : Nat) (hr : r∈List.range 13) := List.all_eq_true.mp ok r hr
      exact ih _ rest (horiz true (horiz false (vertical k) (fun r hr => (Bool.and_eq_true_iff.mp (rows r (List.mem_range.mpr hr))).1))
        (fun r hr => (Bool.and_eq_true_iff.mp (rows r (List.mem_range.mpr hr))).2))
  exact go 12 base checked T.init
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
