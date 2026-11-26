import GridGraphs.ResidueZero.NineCycles
import GridGraphs.Results.ExactSquareFormula
import Std.Tactic.BVDecide.LRAT.Parser
import Std.Tactic.BVDecide.LRAT.Checker

/-! The side-nine upper, adapting the finite rectangle LRAT proof at side eight.
At nine, additional simple grid cycles are necessary; `geometry` verifies
that every added cut is the perimeter of a genuine simple grid cycle. -/
namespace GridGraphs.ResidueZero.Nine
open Std.Sat SimpleGraph

abbrev Site := GridVertex 9 9
def pos (p : Nat) : Site := (⟨p / 9 % 9, by omega⟩, ⟨p % 9, by omega⟩)
def gap (p q : Nat) := 81 + min p q * 81 + max p q
def cnt (i j : Nat) := 6642 + i * 36 + j
abbrev lits := CNF.Clause Nat
def counterRows : List lits := do
  let i ← List.range 81
  let j ← List.range 35
  [[(cnt (i+1) (j+1),false),(cnt i (j+1),true),(i,true)],
   [(cnt (i+1) (j+1),false),(cnt i j,true)]]

def edges : List (Nat × Nat) := do
  let p ← List.range 81
  let q ← [p+1,p+9]
  guard (q < 81 && !(q == p+1 && p%9 == 8))
  return (p,q)

def edgeRows : List lits := edges.flatMap fun (p,q) =>
  [[(gap p q,false),(p,false)],[(gap p q,false),(q,false)]]

def rectanglesOnly : List (List Nat) := do
  let a ← List.range 9
  let b ← List.range 9
  let u ← List.range 9
  let v ← List.range 9
  guard (a < u && b < v)
  return ((List.range (v-b)).map (fun d => 9*a+b+d)) ++
    ((List.range (u-a)).map (fun d => 9*(a+d)+v)) ++
    ((List.range (v-b)).map (fun d => 9*u+(v-d))) ++
    ((List.range (u-a)).map (fun d => 9*(u-d)+b))

def rectangles := rectanglesOnly ++ extraCycles

def boundary (r : List Nat) := r.zip (r.rotateLeft 1)
def rectRow (r : List Nat) : lits := (boundary r).map fun (p,q) => (gap p q,true)
def rows := counterRows ++ ((List.range 35).map fun j => [(cnt 0 (j+1),false)]) ++
  [[(cnt 81 35,true)]] ++ edgeRows ++ rectangles.map rectRow
def cnf : CNF Nat := ⟨rows.toArray⟩

private theorem unsat : cnf.Unsat := by
  let proof := (Std.Tactic.BVDecide.LRAT.parseLRATProof
    (include_str "nine.lrat").toUTF8).toOption.getD #[]
  apply Std.Tactic.BVDecide.LRAT.check_sound proof
  native_decide

def prefixCount (F : Finset Site) (i : Nat) :=
  ((List.range i).filter fun p => decide (pos p ∈ F)).length
def assignment (F : Finset Site) (v : Nat) : Bool :=
  if v < 81 then decide (pos v ∈ F)
  else if v < 6642 then
    decide (pos ((v-81)/81) ∉ F ∧ pos ((v-81)%81) ∉ F)
  else decide ((v-6642)%36 ≤ prefixCount F ((v-6642)/36))

private theorem mark_eval (F : Finset Site) {p : Nat} (hp : p<81) :
    assignment F p = decide (pos p ∈ F) := by simp [assignment,hp]

private theorem gap_eval (F : Finset Site) {p q : Nat} (hp : p<81) (hq : q<81) :
    assignment F (gap p q) = decide (pos p ∉ F ∧ pos q ∉ F) := by
  unfold assignment gap
  rcases le_total p q with le | le
  · simp [min_eq_left le,max_eq_right le,show ¬81+p*81+q<81 by omega,
      show 81+p*81+q<6642 by omega, show (81+p*81+q-81)/81=p by omega,
      show (81+p*81+q-81)%81=q by omega]
  · simp [min_eq_right le,max_eq_left le,show ¬81+q*81+p<81 by omega,
      show 81+q*81+p<6642 by omega,show (81+q*81+p-81)/81=q by omega,
      show (81+q*81+p-81)%81=p by omega,Bool.and_comm]

private theorem cnt_eval (F : Finset Site) (i j : Nat) (hj : j<36) :
    assignment F (cnt i j) = decide (j ≤ prefixCount F i) := by
  simp [assignment,cnt,show ¬6642+i*36+j<81 by omega, show ¬6642+i*36+j<6642 by omega,
    show (6642+i*36+j-6642)%36=j by omega,show (6642+i*36+j-6642)/36=i by omega]

private theorem count_step (F : Finset Site) (i : Nat) :
    prefixCount F (i+1) = prefixCount F i + (if pos i ∈ F then 1 else 0) := by
  by_cases h : pos i ∈ F <;> simp [prefixCount,List.range_succ,h]

private theorem count_full (F : Finset Site) : prefixCount F 81 = F.card := by
  have all : ((List.range 81).map pos).toFinset = Finset.univ := by decide
  have nodup : ((List.range 81).map pos).Nodup := by decide
  have eq : (((List.range 81).map pos).filter fun p => decide (p ∈ F)).toFinset = F := by
    ext v
    have mem := Finset.ext_iff.mp all v
    simp_all
  conv_rhs => rw [←eq, List.toFinset_card_of_nodup (nodup.filter _)]
  simp [prefixCount,List.filter_map,Function.comp_def]

/-- Finite geometry audit. Each perimeter embeds a simple cycle, and
every neighboring pair of cycle indices occurs as a counted gap. -/
private theorem geometry : ∀ r ∈ rectangles,
    2 < r.length ∧ (∀ e ∈ boundary r, e.1 < 81 ∧ e.2 < 81) ∧
    Function.Injective (fun i : Fin r.length => pos r[i]) ∧
    ∀ i j : Fin r.length, (cycleGraph r.length).Adj i j →
      (gridGraph 9 9).Adj (pos r[i]) (pos r[j]) ∧
      ((r[i],r[j]) ∈ boundary r ∨ (r[j],r[i]) ∈ boundary r) := by
  unfold Function.Injective
  native_decide

private theorem rect_eval (F : Finset Site)
    (h : (forcedEdgeGraph (gridGraph 9 9) (↑F : Set _)).IsAcyclic)
    {r} (hr : r ∈ rectangles) : (rectRow r).eval (assignment F) := by
  obtain ⟨len,bounds,inj,adj⟩ := geometry r hr
  by_contra bad
  have forced {p q} (e : (p,q) ∈ boundary r) : pos p ∈ F ∨ pos q ∈ F := by
    obtain ⟨hp,hq⟩ := bounds _ e
    by_contra! missed
    apply bad
    apply List.any_eq_true.mpr
    refine ⟨(gap p q,true),List.mem_map.mpr ⟨(p,q),e,rfl⟩,?_⟩
    simp [gap_eval F hp hq,missed]
  let G := forcedEdgeGraph (gridGraph 9 9) (↑F : Set _)
  have contains : cycleGraph r.length ⊑ G := by
    refine ⟨⟨⟨fun i => pos r[i],?_⟩,inj⟩⟩
    intro i j hij
    obtain ⟨grid,edge⟩ := adj i j hij
    exact ⟨grid,edge.elim forced (fun rev => (forced rev).symm)⟩
  obtain ⟨_,p,cyc,_⟩ := (cycleGraph_isContained_iff len).mp contains
  exact h p cyc

private theorem edge_bounds : ∀ e ∈ edges, e.1 < 81 ∧ e.2 < 81 := by native_decide

set_option maxHeartbeats 900000 in
theorem card_le (F : Finset Site)
    (h : (forcedEdgeGraph (gridGraph 9 9) (↑F : Set _)).IsAcyclic) : F.card ≤ 34 := by
  by_contra! many
  have full : 35 ≤ prefixCount F 81 := by rw [count_full]; omega
  have yes : cnf.eval (assignment F) := by
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro c hc
    change c ∈ rows.toArray at hc
    simp only [List.mem_toArray,rows,List.mem_append,List.mem_map,List.mem_singleton] at hc
    rcases hc with (((hc | ⟨j,hj,rfl⟩) | rfl) | hc) | ⟨r,hr,rfl⟩
    · simp only [counterRows,List.bind_eq_flatMap,List.mem_flatMap,List.mem_range,
        List.mem_cons,List.not_mem_nil,or_false] at hc
      obtain ⟨i,hi,j,hj,(rfl|rfl)⟩ := hc <;>
        simp [CNF.Clause.eval,cnt_eval F _ _ (by omega : j+1<36),cnt_eval F _ _ (by omega : j<36),
          mark_eval F hi,count_step] <;> split_ifs <;> grind
    · have hj' : j+1<36 := by have := List.mem_range.mp hj; omega
      simp [CNF.Clause.eval,cnt_eval F _ _ hj',prefixCount]
    · simp [CNF.Clause.eval,cnt_eval F 81 35 (by decide),full]
    · obtain ⟨⟨p,q⟩,he,inside⟩ := List.mem_flatMap.mp hc
      obtain ⟨hp,hq⟩ := edge_bounds _ he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl|rfl <;> by_cases a : pos p ∈ F <;> by_cases b : pos q ∈ F <;>
        simp [CNF.Clause.eval,gap_eval F hp hq,mark_eval F hp,mark_eval F hq,a,b]
    · exact rect_eval F h hr
  rw [unsat (assignment F)] at yes
  contradiction

theorem maximum_le : maxPreserved 9 9 ≤ 34 := by
  obtain ⟨F,hF,score⟩ := (squareMaskScore_iff_le (n := 9) (by decide)).mpr
    (le_refl (maxPreserved 9 9))
  rw [←score]
  exact card_le F (mem_acyclicForcedSets.mp hF)

theorem maximum_eq : maxPreserved 9 9 = squareScore 9 :=
  Nat.le_antisymm maximum_le (squareScore_lower_three_mul 3 (by decide))

end GridGraphs.ResidueZero.Nine
