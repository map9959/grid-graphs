import GridGraphs.Results.ExactSquareFormula
import Std.Tactic.BVDecide.LRAT.Parser
import Std.Tactic.BVDecide.LRAT.Checker

/-! Every rectangular perimeter in an acyclic forced graph contains an
edge with two unmarked ends. At side eight these inequalities already
exclude score 28. The checked LRAT proof uses only these inequalities
and a sequential counter for the 64 mark bits. -/
namespace GridGraphs.ResidueTwoUpper.Eight
open Std.Sat SimpleGraph

abbrev Site := GridVertex 8 8
def pos (p : Nat) : Site := (⟨p / 8 % 8, by omega⟩, ⟨p % 8, by omega⟩)
def gap (p q : Nat) := 64 + min p q * 64 + max p q
def cnt (i j : Nat) := 4160 + i * 29 + j
abbrev lits := CNF.Clause Nat
def counterRows : List lits := do
  let i ← List.range 64
  let j ← List.range 28
  [[(cnt (i+1) (j+1),false),(cnt i (j+1),true),(i,true)],
   [(cnt (i+1) (j+1),false),(cnt i j,true)]]

def edges : List (Nat × Nat) := do
  let p ← List.range 64
  let q ← [p+1,p+8]
  guard (q < 64 && !(q == p+1 && p%8 == 7))
  return (p,q)

def edgeRows : List lits := edges.flatMap fun (p,q) =>
  [[(gap p q,false),(p,false)],[(gap p q,false),(q,false)]]

def rectangles : List (List Nat) := do
  let a ← List.range 8
  let b ← List.range 8
  let u ← List.range 8
  let v ← List.range 8
  guard (a < u && b < v)
  return ((List.range (v-b)).map (fun d => 8*a+b+d)) ++
    ((List.range (u-a)).map (fun d => 8*(a+d)+v)) ++
    ((List.range (v-b)).map (fun d => 8*u+(v-d))) ++
    ((List.range (u-a)).map (fun d => 8*(u-d)+b))

def boundary (r : List Nat) := r.zip (r.rotateLeft 1)
def rectRow (r : List Nat) : lits := (boundary r).map fun (p,q) => (gap p q,true)
def rows := counterRows ++ ((List.range 28).map fun j => [(cnt 0 (j+1),false)]) ++
  [[(cnt 64 28,true)]] ++ edgeRows ++ rectangles.map rectRow
def cnf : CNF Nat := ⟨rows.toArray⟩

private theorem unsat : cnf.Unsat := by
  let proof := (Std.Tactic.BVDecide.LRAT.parseLRATProof
    (include_str "Data/eight.lrat").toUTF8).toOption.getD #[]
  apply Std.Tactic.BVDecide.LRAT.check_sound proof
  native_decide

def prefixCount (F : Finset Site) (i : Nat) :=
  ((List.range i).filter fun p => decide (pos p ∈ F)).length
def assignment (F : Finset Site) (v : Nat) : Bool :=
  if v < 64 then decide (pos v ∈ F)
  else if v < 4160 then
    decide (pos ((v-64)/64) ∉ F ∧ pos ((v-64)%64) ∉ F)
  else decide ((v-4160)%29 ≤ prefixCount F ((v-4160)/29))

private theorem mark_eval (F : Finset Site) {p : Nat} (hp : p<64) :
    assignment F p = decide (pos p ∈ F) := by simp [assignment,hp]

private theorem gap_eval (F : Finset Site) {p q : Nat} (hp : p<64) (hq : q<64) :
    assignment F (gap p q) = decide (pos p ∉ F ∧ pos q ∉ F) := by
  unfold assignment gap
  rcases le_total p q with le | le
  · simp [min_eq_left le,max_eq_right le,show ¬64+p*64+q<64 by omega,
      show 64+p*64+q<4160 by omega, show (64+p*64+q-64)/64=p by omega,
      show (64+p*64+q-64)%64=q by omega]
  · simp [min_eq_right le,max_eq_left le,show ¬64+q*64+p<64 by omega,
      show 64+q*64+p<4160 by omega,show (64+q*64+p-64)/64=q by omega,
      show (64+q*64+p-64)%64=p by omega,Bool.and_comm]

private theorem cnt_eval (F : Finset Site) (i j : Nat) (hj : j<29) :
    assignment F (cnt i j) = decide (j ≤ prefixCount F i) := by
  simp [assignment,cnt,show ¬4160+i*29+j<64 by omega, show ¬4160+i*29+j<4160 by omega,
    show (4160+i*29+j-4160)%29=j by omega,show (4160+i*29+j-4160)/29=i by omega]

private theorem count_step (F : Finset Site) (i : Nat) :
    prefixCount F (i+1) = prefixCount F i + (if pos i ∈ F then 1 else 0) := by
  by_cases h : pos i ∈ F <;> simp [prefixCount,List.range_succ,h]

private theorem count_full (F : Finset Site) : prefixCount F 64 = F.card := by
  have all : ((List.range 64).map pos).toFinset = Finset.univ := by decide
  have nodup : ((List.range 64).map pos).Nodup := by decide
  have eq : (((List.range 64).map pos).filter fun p => decide (p ∈ F)).toFinset = F := by
    ext v
    have mem := Finset.ext_iff.mp all v
    simp_all
  conv_rhs => rw [←eq, List.toFinset_card_of_nodup (nodup.filter _)]
  simp [prefixCount,List.filter_map,Function.comp_def]

/-- Finite geometry audit. Each perimeter embeds a simple cycle, and
every neighboring pair of cycle indices occurs as a counted gap. -/
private theorem geometry : ∀ r ∈ rectangles,
    2 < r.length ∧ (∀ e ∈ boundary r, e.1 < 64 ∧ e.2 < 64) ∧
    Function.Injective (fun i : Fin r.length => pos r[i]) ∧
    ∀ i j : Fin r.length, (cycleGraph r.length).Adj i j →
      (gridGraph 8 8).Adj (pos r[i]) (pos r[j]) ∧
      ((r[i],r[j]) ∈ boundary r ∨ (r[j],r[i]) ∈ boundary r) := by
  unfold Function.Injective
  native_decide

private theorem rect_eval (F : Finset Site)
    (h : (forcedEdgeGraph (gridGraph 8 8) (↑F : Set _)).IsAcyclic)
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
  let G := forcedEdgeGraph (gridGraph 8 8) (↑F : Set _)
  have contains : cycleGraph r.length ⊑ G := by
    refine ⟨⟨⟨fun i => pos r[i],?_⟩,inj⟩⟩
    intro i j hij
    obtain ⟨grid,edge⟩ := adj i j hij
    exact ⟨grid,edge.elim forced (fun rev => (forced rev).symm)⟩
  obtain ⟨_,p,cyc,_⟩ := (cycleGraph_isContained_iff len).mp contains
  exact h p cyc

private theorem edge_bounds : ∀ e ∈ edges, e.1 < 64 ∧ e.2 < 64 := by decide

set_option maxHeartbeats 900000 in
theorem card_le (F : Finset Site)
    (h : (forcedEdgeGraph (gridGraph 8 8) (↑F : Set _)).IsAcyclic) : F.card ≤ 27 := by
  by_contra! many
  have full : 28 ≤ prefixCount F 64 := by rw [count_full]; omega
  have yes : cnf.eval (assignment F) := by
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro c hc
    change c ∈ rows.toArray at hc
    simp only [List.mem_toArray,rows,List.mem_append,List.mem_map,List.mem_singleton] at hc
    rcases hc with (((hc | ⟨j,hj,rfl⟩) | rfl) | hc) | ⟨r,hr,rfl⟩
    · simp only [counterRows,List.bind_eq_flatMap,List.mem_flatMap,List.mem_range,
        List.mem_cons,List.not_mem_nil,or_false] at hc
      obtain ⟨i,hi,j,hj,(rfl|rfl)⟩ := hc <;>
        simp [CNF.Clause.eval,cnt_eval F _ _ (by omega : j+1<29),cnt_eval F _ _ (by omega : j<29),
          mark_eval F hi,count_step] <;> split_ifs <;> grind
    · have hj' : j+1<29 := by have := List.mem_range.mp hj; omega
      simp [CNF.Clause.eval,cnt_eval F _ _ hj',prefixCount]
    · simp [CNF.Clause.eval,cnt_eval F 64 28 (by decide),full]
    · obtain ⟨⟨p,q⟩,he,inside⟩ := List.mem_flatMap.mp hc
      obtain ⟨hp,hq⟩ := edge_bounds _ he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl|rfl <;> by_cases a : pos p ∈ F <;> by_cases b : pos q ∈ F <;>
        simp [CNF.Clause.eval,gap_eval F hp hq,mark_eval F hp,mark_eval F hq,a,b]
    · exact rect_eval F h hr
  rw [unsat (assignment F)] at yes
  contradiction

theorem maximum_le : maxPreserved 8 8 ≤ 27 := by
  obtain ⟨F,hF,score⟩ := (squareMaskScore_iff_le (n := 8) (by decide)).mpr
    (le_refl (maxPreserved 8 8))
  rw [←score]
  exact card_le F (mem_acyclicForcedSets.mp hF)

theorem maximum_eq : maxPreserved 8 8 = 27 :=
  Nat.le_antisymm maximum_le twentySeven_le_maxPreserved_eight_eight

end GridGraphs.ResidueTwoUpper.Eight
