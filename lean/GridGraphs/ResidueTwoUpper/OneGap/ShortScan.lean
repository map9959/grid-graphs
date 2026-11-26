import GridGraphs.ResidueTwoUpper.OneGap.FanBootScore

/-! Short-fan scans retain both the 3×3 mark mask and the owner of a
forced edge. An overlap of two masks alone does not see a collision of
two parent arrows. Direction numbers are E,S,W,N, with 4 for a sink. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero Stencil L7 FanSlab

abbrev Label := Nat × Nat
abbrev Board := Array (Array (List Label))
def row (A : Board) (r : Nat) := A[r]?.getD #[]
def atRC (A : Board) (r c : Nat) := (row A r)[c]?.getD []
def build (s : Nat) (f : Nat → Nat → List Label) : Board :=
  Array.ofFn fun i : Fin s => Array.ofFn fun j : Fin s => f i j
theorem at_build {s r c} (hr : r<s) (hc : c<s) (f) : atRC (build s f) r c=f r c := by
  simp [atRC,row,build,hr,hc]

def contact (m d : Nat) := bit m 4 + bit m ([5,7,3,1][d]!) > 0
instance (m d : Nat) : Decidable (contact m d) := by unfold contact; infer_instance
def port (send : Bool) (d : Nat) (z : Label) :=
  2*ov d z.1 + (xor (send && decide (contact z.1 d)) (z.2==d)).toNat
def retain (send recv : Nat) (xs ys : List Label) :=
  let K := (xs.map (port true send)).toArray
  ys.filter fun y => K.contains (port false recv y)
theorem retain_mem {a b : Label} {xs ys : List Label} {d e : Nat}
    (ha : a∈xs) (hb : b∈ys) (portEq : port true d a=port false e b) :
    b∈retain d e xs ys := by
  exact List.mem_filter.mpr ⟨hb,by simpa only [List.contains_toArray,List.contains_iff_mem] using
    (List.mem_map.mpr ⟨a,ha,portEq⟩ : port false e b∈xs.map (port true d))⟩

def Kept (s : Nat) (M : Nat → Nat → Label) (A : Board) :=
  ∀ r<s, ∀ c<s, M r c ∈ atRC A r c
def Agree (s : Nat) (M : Nat → Nat → Label) := ∀ r<s, ∀ c<s,
  (c+1<s → port true 0 (M r c)=port false 2 (M r (c+1)) ∧
    port true 2 (M r (c+1))=port false 0 (M r c)) ∧
  (r+1<s → port true 1 (M r c)=port false 3 (M (r+1) c) ∧
    port true 3 (M (r+1) c)=port false 1 (M r c))

/-- A Gauss–Seidel pass: each replacement reads the already filtered
domain behind it, so information can travel a full row in one pass. -/
def lineStep (s : Nat) (vert rev : Bool) (A : Board) (r c : Nat) : Board :=
  let x := if rev then s-1-r else r
  let y := if rev then s-1-c else c
  let t := if vert then r else c
  if t=0 then A else
    let i := if vert then (if rev then x+1 else x-1) else x
    let j := if vert then y else (if rev then y+1 else y-1)
    let d := vert.toNat+2*rev.toNat
    let v := retain d ((d+2)%4) (atRC A i j) (atRC A x y)
    A.setIfInBounds x ((row A x).setIfInBounds y v)

private theorem setKept {s M A} (h : Kept s M A) {r c} {L : List Label} (z : M r c∈L) :
    Kept s M (A.setIfInBounds r ((row A r).setIfInBounds c L)) := by
  intro i hi j hj
  by_cases e : r=i
  · subst i
    by_cases H : r<A.size
    · change M r j ∈ (((A.setIfInBounds r ((row A r).setIfInBounds c L))[r]?.getD #[])[j]?.getD [])
      rw [Array.getElem?_setIfInBounds_self_of_lt H]; dsimp only [Option.getD_some]
      by_cases E : c=j
      · subst j
        by_cases J : c<(row A r).size
        · rwa [Array.getElem?_setIfInBounds_self_of_lt J]
        · rw [Array.setIfInBounds,dif_neg J]; exact h r hi c hj
      · rw [Array.getElem?_setIfInBounds_ne E]; exact h r hi j hj
    · simpa only [Array.setIfInBounds,dif_neg H] using h r hi j hj
  · simpa only [atRC,row,Array.getElem?_setIfInBounds_ne e] using h i hi j hj

theorem step_kept {s M A} (ok : Kept s M A) (e : Agree s M) (v b : Bool) (r c : Nat)
    (hr : r<s) (hc : c<s) : Kept s M (lineStep s v b A r c) := by
  cases v <;> cases b <;> simp only [lineStep,Bool.false_eq_true,if_false,if_true,Bool.toNat_false,Bool.toNat_true]
  all_goals split <;> first | exact ok | apply setKept ok
  all_goals apply retain_mem (ok _ (by omega) _ (by omega)) (ok _ (by omega) _ (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 1≤c)] using ((e r hr (c-1) (by omega)).1 (by omega)).1
  · exact ((e _ (by omega) _ (by omega)).1 (by omega)).2
  · simpa only [Nat.sub_add_cancel (by omega : 1≤r)] using ((e (r-1) (by omega) c hc).2 (by omega)).1
  · exact ((e _ (by omega) _ (by omega)).2 (by omega)).2

def pass (s : Nat) (v b : Bool) (A : Board) :=
  (List.finRange s).foldl (fun G (r : Fin s) => (List.finRange s).foldl
    (fun H (c : Fin s) => lineStep s v b H r c) G) A
def round (s : Nat) (A : Board) :=
  pass s true true (pass s false true (pass s true false (pass s false false A)))
def prune (s : Nat) : Nat → Board → Board
  | 0,A => A
  | t+1,A => prune s t (round s A)

theorem prune_kept {s M A} (h : Kept s M A) (e : Agree s M) (t : Nat) : Kept s M (prune s t A) := by
  have one (G v b) (k : Kept s M G) : Kept s M (pass s v b G) := by
    unfold pass
    apply List.foldlRecOn (motive:=Kept s M) _ _ k
    intro G h r _
    apply List.foldlRecOn (motive:=Kept s M) _ _ h
    intro H z c _; exact step_kept z e v b _ _ r.isLt c.isLt
  induction t generalizing A with
  | zero => exact h
  | succ t ih => exact ih (one _ _ _ (one _ _ _ (one _ _ _ (one _ _ _ h))))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
