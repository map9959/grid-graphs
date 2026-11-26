import GridGraphs.ResidueTwoUpper.Opposite0101.Frame

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero

private def decodeRows (s : String) := ((s.trimAscii.toString.splitOn "\n").map
  (fun l => ((l.splitOn " ").filterMap String.toNat?).toArray)).toArray
def stencils := decodeRows (include_str "stencils.txt")
def suffixes := decodeRows (include_str "suffixes.txt")
def sTab (v : Bool) (j r : Nat) := (stencils[35*v.toNat+j]?.getD #[])[r]?.getD 0
def pTab (v : Bool) (j r : Nat) := (stencils[35*v.toNat+j]?.getD #[])[6+r]?.getD 0
def states (v : Bool) (j : Nat) := (suffixes[29*v.toNat+(j-5)]?).getD #[]
def entry (a b : Nat) := 128*a+b

/-- Repeated central columns only. Every successor pair uses either
an ordinary base transition or the central 17-to-15 seam. -/
def idx (u j : Nat) :=
  if j<15 then j else if j<15+42*u then 15+(j-15)%3 else j-42*u

theorem idx_pair {u j : Nat} (hj : j<35+42*u) :
    idx u j < 35 ∧ (idx u (j+1)=idx u j+1 ∨ idx u j=17 ∧ idx u (j+1)=15) := by
  unfold idx; split_ifs <;> omega

def colOK (v : Bool) (j a : Nat) : Bool := (List.range 7).all fun r =>
  match armBit v 35 r j with
  | none => true | some b => a.testBit r == b

def nbr (v : Bool) (r a b c : Nat) :=
  let east := bit c r; let west := bit a r
  let down := bit b (r+1); let up := if r=0 then 0 else bit b (r-1)
  if v then down+2*east+4*up+8*west else east+2*down+4*west+8*up

def pmask (v : Bool) (r a b c : Nat) :=
  ((List.range 9).map fun q =>
    let k := if v then q/3 else q%3
    let d := if v then q%3 else q/3
    bit (if k=0 then a else if k=1 then b else c) (r+d) <<< q).sum

def localOK (v : Bool) (j a b c : Nat) : Bool :=
  ((List.range 6).all fun r => (sTab v j r).testBit (bit b r + 2*nbr v r a b c)) &&
  (j==0 || j==34 || (List.range 5).all fun r => (pTab v (j-1) r).testBit (pmask v r a b c))

def initCheck (v : Bool) := (List.range 128).all fun a =>
  !colOK v 33 a || (List.range 128).all fun b => !colOK v 34 b ||
    !localOK v 34 a b 0 || (states v 33).contains (entry a b)

def stepCheck (v : Bool) (i j : Nat) :=
  (states v j).all fun p =>
    (List.range 128).all fun a =>
      !colOK v i a || !localOK v j a (p/128) (p%128) ||
        (states v i).contains (entry a (p/128))

def stepsCheck (v : Bool) := (List.range 28).all (fun k => stepCheck v (5+k) (6+k)) &&
  stepCheck v 17 15

theorem base_checked : ∀ v : Bool, initCheck v=true ∧ stepsCheck v=true := by native_decide

/-- Model of the restriction of a physical mask to one of the strips.
The predecessor and successor outside the board are padded with zeros. -/
structure StripOK (v : Bool) (u : Nat) (s : Nat → Nat) : Prop where
  small : ∀ j, s j<128
  column : ∀ j, j<35+42*u → colOK v (idx u j) (s j)=true
  step : ∀ j, j<35+42*u → localOK v (idx u j) (if j=0 then 0 else s (j-1))
    (s j) (if j+1=35+42*u then 0 else s (j+1))=true

theorem suffix_mem {v u s} (h : StripOK v u s) (i : Nat) (lo : 5 ≤ i) (hi : i≤33+42*u) :
    (states v (idx u i)).contains (entry (s i) (s (i+1)))=true := by
  have go (d i : Nat) (endEq : i+d=33+42*u) (lo : 5 ≤ i) :
      (states v (idx u i)).contains (entry (s i) (s (i+1)))=true := by
    induction d generalizing i with
    | zero =>
      have eq : idx u i=33 := by unfold idx; split_ifs <;> omega
      have eq' : idx u (i+1)=34 := by unfold idx; split_ifs <;> omega
      have x := (base_checked v).1
      simp only [initCheck,List.all_eq_true,List.mem_range] at x
      have a := h.column i (by omega); have b := h.column (i+1) (by omega)
      have l := h.step (i+1) (by omega)
      simp only [eq,eq'] at a b l ⊢
      simp [show i+1+1=35+42*u by omega] at l
      have X := x (s i) (h.small _)
      simp only [a,Bool.not_true,Bool.false_or,List.all_eq_true,List.mem_range] at X
      simpa [b,l] using X (s (i+1)) (h.small _)
    | succ d ih =>
      let j := i+1
      have next := ih j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have lim : 5 ≤ idx u i ∧ idx u i≤32 := by unfold idx; split_ifs <;> omega
      have stepOK : stepCheck v (idx u i) (idx u j)=true := by
        obtain ⟨_,p|⟨p,q⟩⟩ := idx_pair (u:=u) (j:=i) (by omega)
        · have C := (base_checked v).2; simp only [stepsCheck,Bool.and_eq_true] at C
          have all := C.1
          have e := List.all_eq_true.mp all (idx u i-5) (List.mem_range.mpr (by omega))
          simpa only [j,p,show 5+(idx u i-5)=idx u i by omega,
            show 6+(idx u i-5)=idx u i+1 by omega] using e
        · rw [p,show idx u j=15 from q]
          have C := (base_checked v).2; simp only [stepsCheck,Bool.and_eq_true] at C; exact C.2
      have x := Array.all_eq_true_iff_forall_mem.mp stepOK
      have f := x _ (by simpa using next)
      simp only [List.all_eq_true,List.mem_range] at f
      have a := h.column i (by omega)
      have l := h.step j (by dsimp [j]; omega)
      have no : j+1≠35+42*u := by dsimp [j]; omega
      simp only [if_neg no,if_neg (by dsimp [j]; omega : ¬j=0),show j-1=i by simp [j]] at l
      have div : entry (s j) (s (j+1))/128=s j := by unfold entry; have := h.small (j+1); omega
      have rem : entry (s j) (s (j+1))%128=s (j+1) := by unfold entry; have := h.small (j+1); omega
      simpa [div,rem,a,l,j] using f (s i) (h.small _)
  exact go (33+42*u-i) i (by omega) lo

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
