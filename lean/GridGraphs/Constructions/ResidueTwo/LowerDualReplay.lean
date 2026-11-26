import GridGraphs.Results.ExactSquareFormula
import GridGraphs.Constructions.ConstructionCertificate

/-! A compact physical check for the residue-two lower constructions. A dual
distance array is untrusted: each bounded face must exhibit a strictly
descending dual edge across two unmarked primal sites. -/
namespace GridGraphs.ResidueTwoLower

abbrev Mask := Nat → Nat → Bool

private def holes (n : Nat) (m : Mask) : Finset (GridVertex n n) :=
  Finset.univ.filter fun v => m v.1 v.2 = false

private def index {n} : GridFace n n → Nat
  | .out => (n-1)^2
  | .cell r c => r.val*(n-1)+c.val

private def arc {n} (m : Mask) (d : Array Nat) (x : GridFace n n)
    (p : GridVertex n n × GridVertex n n) (f : GridFace n n × GridFace n n) : Bool :=
  !m p.1.1 p.1.2 && !m p.2.1 p.2.2 &&
    ((x == f.1 && decide (d[index f.2]! < d[index x]!)) ||
     (x == f.2 && decide (d[index f.1]! < d[index x]!)))

private theorem arc_sound {n} {m : Mask} {d} {x : GridFace n n} {p f}
    (h : arc m d x p f = true) :
    p.1 ∈ holes n m ∧ p.2 ∈ holes n m ∧
      ∃ y, HasDualEndpoints f x y ∧ d[index y]! < d[index x]! := by
  simp [arc, Bool.and_eq_true, Bool.or_eq_true] at h
  refine ⟨by simpa [holes] using h.1.1, by simpa [holes] using h.1.2, ?_⟩
  rcases h.2 with ⟨h,g⟩ | ⟨h,g⟩
  · exact ⟨_, Or.inl ⟨h,rfl⟩,g⟩
  · exact ⟨_, Or.inr ⟨h,rfl⟩,g⟩

private def hArc {n} (m : Mask) (d : Array Nat) (x : GridFace n n)
    (e : HorizontalGridEdge n n) :=
  arc m d x (horizontalPrimalEndpoints e) (horizontalDualEndpoints e)

private def vArc {n} (m : Mask) (d : Array Nat) (x : GridFace n n)
    (e : VerticalGridEdge n n) :=
  arc m d x (verticalPrimalEndpoints e) (verticalDualEndpoints e)

private def checkCell (n : Nat) (m : Mask) (d : Array Nat) (r c : Fin (n-1)) :=
  let x := GridFace.cell r c
  hArc m d x ⟨⟨r.val,by omega⟩,c⟩ || hArc m d x ⟨⟨r.val+1,by omega⟩,c⟩ ||
  vArc m d x ⟨r,⟨c.val,by omega⟩⟩ || vArc m d x ⟨r,⟨c.val+1,by omega⟩⟩

private theorem checkCell_sound {n m d r c} (h : checkCell n m d r c = true) :
    ∃ y, (uuDualGraph (holes n m)).Adj (.cell r c) y ∧
      d[index y]! < d[index (.cell r c : GridFace n n)]! := by
  let x := GridFace.cell r c
  have hor (e : HorizontalGridEdge n n) (he : hArc m d x e = true) :
      ∃ y, (uuDualGraph (holes n m)).Adj x y ∧ d[index y]! < d[index x]! := by
    obtain ⟨a,b,y,hf,lt⟩ := arc_sound he
    exact Exists.intro y (And.intro (show (uuDualGraph (holes n m)).Adj x y from
      ⟨fun eq => (Nat.ne_of_lt lt) (congrArg (fun z => d[index z]!) eq.symm),
        Or.inl ⟨e,a,b,hf⟩⟩) lt)
  have ver (e : VerticalGridEdge n n) (he : vArc m d x e = true) :
      ∃ y, (uuDualGraph (holes n m)).Adj x y ∧ d[index y]! < d[index x]! := by
    obtain ⟨a,b,y,hf,lt⟩ := arc_sound he
    exact Exists.intro y (And.intro (show (uuDualGraph (holes n m)).Adj x y from
      ⟨fun eq => (Nat.ne_of_lt lt) (congrArg (fun z => d[index z]!) eq.symm),
        Or.inr ⟨e,a,b,hf⟩⟩) lt)
  simp only [checkCell,Bool.or_eq_true] at h
  rcases h with ((h|h)|h)|h
  · exact hor _ h
  · exact hor _ h
  · exact ver _ h
  · exact ver _ h

/-- Construct candidate dual distances by breadth-first search. All arrays
are linear in board area; no rank or parent tables need to be stored. -/
def distances (n : Nat) (m : Mask) : Array Nat := Id.run do
  let w := n-1
  let out := w*w
  let mut adj : Array (List Nat) := Array.replicate (out+1) []
  for i in [:n] do
    for j in [:w] do
      if !m i j && !m i (j+1) then
        let a := if i == 0 then out else (i-1)*w+j
        let b := if i == w then out else i*w+j
        adj := adj.modify a (b :: ·)
        adj := adj.modify b (a :: ·)
      if !m j i && !m (j+1) i then
        let a := if i == 0 then out else j*w+i-1
        let b := if i == w then out else j*w+i
        adj := adj.modify a (b :: ·)
        adj := adj.modify b (a :: ·)
  let inf := out+1
  let mut d := (Array.replicate inf inf).set! out 0
  let mut q := #[out]
  for k in [:inf] do
    if k ≥ q.size then break
    let a := q[k]!
    for b in adj[a]! do
      if d[b]! == inf then
        d := d.set! b (d[a]!+1)
        q := q.push b
  return d

/-- Exact marked cardinality and a locally certified descent for every face. -/
def replay (n s : Nat) (m : Mask) : Bool :=
  let d := distances n m
  decide ((Finset.univ.filter (fun v : GridVertex n n => m v.1 v.2)).card = s) &&
    decide (∀ r c, checkCell n m d r c = true)

theorem replay_sound {n s m} (hn : 0 < n) (h : replay n s m = true) :
    s ≤ maxPreserved n n := by
  classical
  simp only [replay, Bool.and_eq_true, decide_eq_true_eq] at h
  let d := distances n m
  let G := uuDualGraph (holes n m)
  have reach : ∀ x : GridFace n n, G.Reachable x .out := by
    intro x
    induction x using (measure (fun x : GridFace n n => d[index x]!)).wf.induction with
    | h x ih =>
      cases x with
      | out => exact .refl _
      | cell r c =>
        obtain ⟨y,e,lt⟩ := checkCell_sound (h.2 r c)
        exact e.reachable.trans (ih y lt)
  let : Nonempty (GridFace n n) := ⟨.out⟩
  have conn : G.Connected := ⟨fun a b => (reach a).trans (reach b).symm⟩
  have e : Finset.univ \ holes n m =
      Finset.univ.filter (fun v : GridVertex n n => m v.1 v.2) := by
    ext v
    simp [holes]
  simpa only [e,h.1] using compl_card_le_maxPreserved_of_uuDual_connected hn hn _ conn

end GridGraphs.ResidueTwoLower
