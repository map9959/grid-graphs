import GridGraphs.Constructions.ConstructionCertificate

/-!
# The finite diagonal construction for twenty rows

The U-U dual connectivity of the canonical row-mask witness is certified by
explicit parent-direction, rank, and crossed-primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 24000000
set_option maxRecDepth 100000

private def table (xs : List Nat) (c fallback : Nat) : Nat :=
  xs[c]?.getD fallback

/-- The canonical mask in row `r`. -/
def finiteU20Mask : Nat → Nat
  | 0 => 2 | 1 => 1048574 | 2 => 898782 | 3 => 505558
  | 4 => 456438 | 5 => 450230 | 6 => 449462 | 7 => 449462
  | 8 => 449270 | 9 => 449494 | 10 => 449398 | 11 => 449398
  | 12 => 449366 | 13 => 449398 | 14 => 449502 | 15 => 449242
  | 16 => 449502 | 17 => 449398 | 18 => 524286 | 19 => 262146
  | _ => 0

private def finiteU20Selected (v : GridVertex 20 20) : Bool :=
  let c := v.2.val
  match v.1.val with
  | 0 => c == 1
  | 1 => 1 ≤ c
  | 2 => (1 ≤ c && c ≤ 4) || (6 ≤ c && c ≤ 7) ||
      (9 ≤ c && c ≤ 10) || (12 ≤ c && c ≤ 13) || (15 ≤ c && c ≤ 16) || 18 ≤ c
  | 3 => (1 ≤ c && c ≤ 2) || c == 4 || (6 ≤ c && c ≤ 7) ||
      (9 ≤ c && c ≤ 10) || (12 ≤ c && c ≤ 13) || (15 ≤ c && c ≤ 18)
  | 4 => (1 ≤ c && c ≤ 2) || (4 ≤ c && c ≤ 7) ||
      (9 ≤ c && c ≤ 10) || (12 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 5 => (1 ≤ c && c ≤ 2) || (4 ≤ c && c ≤ 5) || c == 7 ||
      (9 ≤ c && c ≤ 12) || (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 6 | 7 => (1 ≤ c && c ≤ 2) || (4 ≤ c && c ≤ 5) ||
      (7 ≤ c && c ≤ 9) || (11 ≤ c && c ≤ 12) ||
      (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 8 => (1 ≤ c && c ≤ 2) || (4 ≤ c && c ≤ 7) || c == 9 ||
      (11 ≤ c && c ≤ 12) || (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 9 => (1 ≤ c && c ≤ 2) || c == 4 || (6 ≤ c && c ≤ 9) ||
      (11 ≤ c && c ≤ 12) || (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 10 | 11 | 13 | 17 => (1 ≤ c && c ≤ 2) || (4 ≤ c && c ≤ 6) ||
      (8 ≤ c && c ≤ 9) || (11 ≤ c && c ≤ 12) ||
      (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 12 => (1 ≤ c && c ≤ 2) || c == 4 || c == 6 ||
      (8 ≤ c && c ≤ 9) || (11 ≤ c && c ≤ 12) ||
      (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 14 | 16 => (1 ≤ c && c ≤ 4) || (6 ≤ c && c ≤ 9) ||
      (11 ≤ c && c ≤ 12) || (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 15 => c == 1 || (3 ≤ c && c ≤ 4) || (6 ≤ c && c ≤ 7) || c == 9 ||
      (11 ≤ c && c ≤ 12) || (14 ≤ c && c ≤ 15) || (17 ≤ c && c ≤ 18)
  | 18 => 1 ≤ c && c ≤ 18
  | 19 => c == 1 || c == 18
  | _ => false

/-- The selected vertices with the twenty specified row masks. -/
def finiteU20 : Finset (GridVertex 20 20) :=
  Finset.univ.filter fun v => finiteU20Selected v = true

/-- Parent directions: up, down, left, right, and outside are `0,1,2,3,4`. -/
def finiteU20ParentDirection (r c : Nat) : Nat :=
  match r with
  | 0 => table [3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] c 4
  | 1 => table [3,1,2,2,2,3,1,2,3,1,2,3,1,2,3,1,2,3,4] c 4
  | 2 => table [3,1,2,0,2,3,1,2,3,1,2,3,1,2,3,3,1,3,0] c 4
  | 3 => table [3,1,2,3,1,1,2,2,3,1,2,3,3,1,3,0,3,0,2] c 4
  | 4 => table [3,1,2,3,1,2,0,2,3,3,1,3,0,3,0,2,3,0,2] c 4
  | 5 => table [3,1,2,3,1,2,3,1,3,0,3,0,2,3,0,2,3,0,2] c 4
  | 6 => table [3,1,2,3,1,2,3,3,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 7 => table [3,1,2,3,3,1,3,0,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 8 => table [3,1,2,3,0,3,0,2,1,2,3,0,2,3,0,2,3,0,2] c 4
  | 9 => table [3,1,2,3,1,3,0,0,2,2,3,0,2,3,0,2,3,0,2] c 4
  | 10 => table [3,1,2,3,3,0,2,3,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 11 => table [3,1,2,3,0,0,2,3,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 12 => table [3,1,2,3,1,1,2,3,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 13 => table [3,3,1,1,2,3,1,3,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 14 => table [3,0,3,1,2,3,3,0,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 15 => table [3,1,3,1,2,3,0,2,1,2,3,0,2,3,0,2,3,0,2] c 4
  | 16 => table [3,3,0,3,1,3,0,0,2,2,3,0,2,3,0,2,3,0,2] c 4
  | 17 => table [3,0,2,3,3,0,2,3,0,2,3,0,2,3,0,2,3,0,2] c 4
  | 18 => table [3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2] c 4
  | _ => 4

/-- The explicit parent of every dual face. -/
def finiteU20Parent : GridFace 20 20 → GridFace 20 20
  | .out => .out
  | .cell r c =>
      match finiteU20ParentDirection r.val c.val with
      | 0 => if h : 0 < r.val then .cell ⟨r.val - 1, by omega⟩ c else .out
      | 1 => if h : r.val + 1 < 19 then .cell ⟨r.val + 1, h⟩ c else .out
      | 2 => if h : 0 < c.val then .cell r ⟨c.val - 1, by omega⟩ else .out
      | 3 => if h : c.val + 1 < 19 then .cell r ⟨c.val + 1, h⟩ else .out
      | _ => .out

/-- Explicit distances from the outside face in the parent tree. -/
def finiteU20Rank : GridFace 20 20 → Nat
  | .out => 0
  | .cell r c =>
      match r.val with
      | 0 => table [62,61,62,63,64,39,38,39,24,23,24,17,16,17,10,9,10,3,2] c.val 0
      | 1 => table [61,60,61,62,63,38,37,38,23,22,23,16,15,16,9,8,9,2,1] c.val 0
      | 2 => table [60,59,60,63,64,37,36,37,22,21,22,15,14,15,8,7,6,3,2] c.val 0
      | 3 => table [59,58,59,34,33,34,35,36,21,20,21,14,13,12,9,8,5,4,5] c.val 0
      | 4 => table [58,57,58,33,32,33,36,37,20,19,18,15,14,11,10,11,6,5,6] c.val 0
      | 5 => table [57,56,57,32,31,32,25,24,21,20,17,16,17,12,11,12,7,6,7] c.val 0
      | 6 => table [56,55,56,31,30,31,24,23,22,23,18,17,18,13,12,13,8,7,8] c.val 0
      | 7 => table [55,54,55,30,29,28,25,24,23,24,19,18,19,14,13,14,9,8,9] c.val 0
      | 8 => table [54,53,54,31,30,27,26,27,30,31,20,19,20,15,14,15,10,9,10] c.val 0
      | 9 => table [53,52,53,32,31,28,27,28,29,30,21,20,21,16,15,16,11,10,11] c.val 0
      | 10 => table [52,51,52,31,30,29,30,31,30,31,22,21,22,17,16,17,12,11,12] c.val 0
      | 11 => table [51,50,51,32,31,30,31,32,31,32,23,22,23,18,17,18,13,12,13] c.val 0
      | 12 => table [50,49,50,49,48,39,40,33,32,33,24,23,24,19,18,19,14,13,14] c.val 0
      | 13 => table [49,48,47,46,47,38,37,34,33,34,25,24,25,20,19,20,15,14,15] c.val 0
      | 14 => table [50,49,46,45,46,37,36,35,34,35,26,25,26,21,20,21,16,15,16] c.val 0
      | 15 => table [49,48,45,44,45,38,37,38,41,42,27,26,27,22,21,22,17,16,17] c.val 0
      | 16 => table [48,47,46,43,42,39,38,39,40,41,28,27,28,23,22,23,18,17,18] c.val 0
      | 17 => table [49,48,49,42,41,40,41,42,41,42,29,28,29,24,23,24,19,18,19] c.val 0
      | 18 => table [50,49,50,43,42,41,42,43,42,43,30,29,30,25,24,25,20,19,20] c.val 0
      | _ => 0

/-- Codes for the explicit crossed edges. Horizontal `(r,c)` is `19*r+c`;
vertical `(r,c)` is `380+20*r+c`. -/
private def finiteU20ParentEdgeCode (r c : Nat) : Nat :=
  match r with
  | 0 => table [381,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37] c 0
  | 1 => table [401,39,402,403,404,406,44,407,409,47,410,412,50,413,415,53,416,418,419] c 0
  | 2 => table [421,58,422,41,424,426,63,427,429,66,430,432,69,433,435,436,73,438,56] c 0
  | 3 => table [441,77,442,444,80,81,446,447,449,85,450,452,453,89,455,72,457,74,458] c 0
  | 4 => table [461,96,462,464,99,465,82,467,469,470,105,472,88,474,90,475,477,93,478] c 0
  | 5 => table [481,115,482,484,118,485,487,121,489,104,491,106,492,494,109,495,497,112,498] c 0
  | 6 => table [501,134,502,504,137,505,507,508,122,509,511,125,512,514,128,515,517,131,518] c 0
  | 7 => table [521,153,522,524,525,157,527,140,141,529,531,144,532,534,147,535,537,150,538] c 0
  | 8 => table [541,172,542,544,156,546,158,547,179,549,551,163,552,554,166,555,557,169,558] c 0
  | 9 => table [561,191,562,564,194,566,177,178,568,569,571,182,572,574,185,575,577,188,578] c 0
  | 10 => table [581,210,582,584,585,195,586,588,198,589,591,201,592,594,204,595,597,207,598] c 0
  | 11 => table [601,229,602,604,213,214,606,608,217,609,611,220,612,614,223,615,617,226,618] c 0
  | 12 => table [621,248,622,624,251,252,626,628,236,629,631,239,632,634,242,635,637,245,638] c 0
  | 13 => table [641,642,268,269,644,646,272,648,255,649,651,258,652,654,261,655,657,264,658] c 0
  | 14 => table [661,267,663,288,664,666,667,273,274,669,671,277,672,674,280,675,677,283,678] c 0
  | 15 => table [681,305,683,307,684,686,291,687,312,689,691,296,692,694,299,695,697,302,698] c 0
  | 16 => table [701,702,306,704,327,706,310,311,708,709,711,315,712,714,318,715,717,321,718] c 0
  | 17 => table [721,324,722,724,725,328,726,728,331,729,731,334,732,734,337,735,737,340,738] c 0
  | 18 => table [741,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,758] c 0
  | _ => 0

private inductive FiniteU20PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 20 20)
  | vertical (edge : VerticalGridEdge 20 20)

private def FiniteU20PrimalEdge.primalEndpoints :
    FiniteU20PrimalEdge → GridVertex 20 20 × GridVertex 20 20
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU20PrimalEdge.dualEndpoints :
    FiniteU20PrimalEdge → GridFace 20 20 × GridFace 20 20
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU20ParentEdge : GridFace 20 20 → FiniteU20PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      let code := finiteU20ParentEdgeCode r.val c.val
      if code < 380 then
        .horizontal ⟨⟨(code / 19) % 20, Nat.mod_lt _ (by norm_num)⟩,
          ⟨code % 19, Nat.mod_lt _ (by norm_num)⟩⟩
      else
        let code := code - 380
        .vertical ⟨⟨(code / 20) % 19, Nat.mod_lt _ (by norm_num)⟩,
          ⟨code % 20, Nat.mod_lt _ (by norm_num)⟩⟩

private theorem finiteU20PrimalEdge_adj (e : FiniteU20PrimalEdge)
    (x y : GridFace 20 20) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU20)
    (h₂ : e.primalEndpoints.2 ∈ finiteU20)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU20).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU20_parent_ne (f : GridFace 20 20) (hf : f ≠ .out) :
    f ≠ finiteU20Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

private theorem finiteU20_parent_edge_data (f : GridFace 20 20) (hf : f ≠ .out) :
    let e := finiteU20ParentEdge f
    e.primalEndpoints.1 ∈ finiteU20 ∧
      e.primalEndpoints.2 ∈ finiteU20 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU20Parent f) := by
  simp only [finiteU20, Finset.mem_filter, Finset.mem_univ, true_and, HasDualEndpoints]
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

/-- The explicit ranked parent certificate on all three hundred sixty-two faces. -/
def finiteU20RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU20) where
  root := .out
  parent := finiteU20Parent
  rank := finiteU20Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU20_parent_edge_data f hf
    exact finiteU20PrimalEdge_adj (finiteU20ParentEdge f) f (finiteU20Parent f)
      (finiteU20_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;> decide

theorem finiteU20_compl_card :
    ((Finset.univ : Finset (GridVertex 20 20)) \ finiteU20).card = 150 := by
  have hU : finiteU20.card = 250 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 400 - 250 = 150
  norm_num

/-- One hundred fifty vertices can be preserved in the twenty-by-twenty grid. -/
theorem oneHundredFifty_le_maxPreserved_twenty_twenty :
    150 ≤ maxPreserved 20 20 := by
  rw [← finiteU20_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU20 finiteU20RankedDualCertificate

end GridGraphs
