import GridGraphs.Constructions.ResidueTwo.LowerZipperRoutes

/-! A finite dual obstruction has a directed primal boundary. Following
that boundary never reverses. A potential which decreases on turns and
does not increase on straight edges therefore rules out the obstruction. -/
namespace GridGraphs.ResidueTwoLower.Turn

inductive Dir | east | south | west | north deriving DecidableEq, Repr
abbrev Pt := ℤ × ℤ

def advance (v : Pt) : Dir → Pt
  | .east => (v.1,v.2+1)
  | .south => (v.1+1,v.2)
  | .west => (v.1,v.2-1)
  | .north => (v.1-1,v.2)

def turnR : Dir → Dir
  | .east => .south | .south => .west | .west => .north | .north => .east
def turnL : Dir → Dir
  | .east => .north | .north => .west | .west => .south | .south => .east

/-- Faces use the coordinates of their upper-left corner, even outside
the frame (where they all denote the one unbounded face). -/
def face (n : Nat) (i j : ℤ) : GridFace n n :=
  if h : 0 ≤ i ∧ i<(n:ℤ)-1 ∧ 0 ≤ j ∧ j<(n:ℤ)-1 then
    .cell ⟨i.toNat,by omega⟩ ⟨j.toNat,by omega⟩
  else .out

def leftCell (v : Pt) : Dir → Pt
  | .east => (v.1-1,v.2)
  | .south => v
  | .west => (v.1,v.2-1)
  | .north => (v.1-1,v.2-1)
def rightCell (v : Pt) : Dir → Pt
  | .east => v
  | .south => (v.1,v.2-1)
  | .west => (v.1-1,v.2-1)
  | .north => (v.1-1,v.2)

def onBoard (n : Nat) (v : Pt) : Prop :=
  0≤v.1 ∧ v.1<n ∧ 0≤v.2 ∧ v.2<n

def forced (n : Nat) (m : Mask) (v : Pt) (d : Dir) : Prop :=
  let w := advance v d
  onBoard n v ∧ onBoard n w ∧ (m v.1.toNat v.2.toNat || m w.1.toNat w.2.toNat)

private theorem hfaces {n : Nat} {i j : ℤ} (hi : 0 ≤ i ∧ i<n) (hj : 0 ≤ j ∧ j<(n:ℤ)-1) :
    let e : HorizontalGridEdge n n := ⟨⟨i.toNat,by omega⟩,⟨j.toNat,by omega⟩⟩
    horizontalDualEndpoints e = (face n (i-1) j,face n i j) := by
  simp only [horizontalDualEndpoints,face]
  congr 1 <;> split_ifs <;> first | rfl | congr 2 <;> omega

private theorem vfaces {n : Nat} {i j : ℤ} (hi : 0 ≤ i ∧ i<(n:ℤ)-1) (hj : 0 ≤ j ∧ j<n) :
    let e : VerticalGridEdge n n := ⟨⟨i.toNat,by omega⟩,⟨j.toNat,by omega⟩⟩
    verticalDualEndpoints e = (face n i (j-1),face n i j) := by
  simp only [verticalDualEndpoints,face]
  congr 1 <;> split_ifs <;> first | rfl | congr 2 <;> omega

private def dark (n : Nat) (m : Mask) (v : Pt) :=
  ¬(holeDual n m).Reachable (face n v.1 v.2) .out

private theorem dark_bounds {n m i j} (h : dark n m (i,j)) :
    0 ≤ i ∧ i<(n:ℤ)-1 ∧ 0 ≤ j ∧ j<(n:ℤ)-1 := by
  by_contra neg
  exact h (by simp [face,neg])

private theorem hforced {n m i j} (h : ¬(dark n m (i-1,j) ↔ dark n m (i,j))) :
    forced n m (i,j) .east := by
  have b : dark n m (i-1,j) ∨ dark n m (i,j) := by tauto
  have a : (0 ≤ i ∧ i<n) ∧ (0 ≤ j ∧ j<(n:ℤ)-1) := by
    rcases b with b|b <;> obtain ⟨_,_,_,_⟩ := dark_bounds b <;> omega
  refine ⟨by simp [onBoard]; omega,by simp [onBoard,advance]; omega,?_⟩
  simp only [advance,Bool.or_eq_true]
  by_contra! neg
  obtain ⟨x,y⟩ := neg
  let e : HorizontalGridEdge n n := ⟨⟨i.toNat,by omega⟩,⟨j.toNat,by omega⟩⟩
  have ne : face n (i-1) j ≠ face n i j := by
    intro eq; apply h; unfold dark; simp [eq]
  have adj : (holeDual n m).Adj (face n (i-1) j) (face n i j) := by
    refine ⟨ne,Or.inl ⟨e,?_,?_,Or.inl ?_⟩⟩
    · simpa [e,horizontalPrimalEndpoints] using x
    · simpa [e,horizontalPrimalEndpoints,show (j+1).toNat=j.toNat+1 by omega] using y
    · rw [show horizontalDualEndpoints e=_ from hfaces a.1 a.2]; exact ⟨rfl,rfl⟩
  exact h ⟨fun u p => u (adj.reachable.trans p),fun u p => u (adj.symm.reachable.trans p)⟩

private theorem vforced {n m i j} (h : ¬(dark n m (i,j-1) ↔ dark n m (i,j))) :
    forced n m (i,j) .south := by
  have b : dark n m (i,j-1) ∨ dark n m (i,j) := by tauto
  have a : (0 ≤ i ∧ i<(n:ℤ)-1) ∧ (0 ≤ j ∧ j<n) := by
    rcases b with b|b <;> obtain ⟨_,_,_,_⟩ := dark_bounds b <;> omega
  refine ⟨by simp [onBoard]; omega,by simp [onBoard,advance]; omega,?_⟩
  simp only [advance,Bool.or_eq_true]
  by_contra! neg
  obtain ⟨x,y⟩ := neg
  let e : VerticalGridEdge n n := ⟨⟨i.toNat,by omega⟩,⟨j.toNat,by omega⟩⟩
  have ne : face n i (j-1) ≠ face n i j := by
    intro eq; apply h; unfold dark; simp [eq]
  have adj : (holeDual n m).Adj (face n i (j-1)) (face n i j) := by
    refine ⟨ne,Or.inr ⟨e,?_,?_,Or.inl ?_⟩⟩
    · simpa [e,verticalPrimalEndpoints] using x
    · simpa [e,verticalPrimalEndpoints,show (i+1).toNat=i.toNat+1 by omega] using y
    · rw [show verticalDualEndpoints e=_ from vfaces a.1 a.2]; exact ⟨rfl,rfl⟩
  exact h ⟨fun u p => u (adj.reachable.trans p),fun u p => u (adj.symm.reachable.trans p)⟩

private def rim (n : Nat) (m : Mask) (v : Pt) (d : Dir) :=
  dark n m (rightCell v d) ∧ ¬dark n m (leftCell v d)

private theorem rim_forced {n m v d} (h : rim n m v d) : forced n m v d := by
  rcases v with ⟨i,j⟩
  cases d
  · exact hforced (fun eq => h.2 (eq.mpr h.1))
  · exact vforced (fun eq => h.2 (eq.mp h.1))
  · have f := hforced (i := i) (j := j-1) (fun eq => h.2 (eq.mp h.1))
    simpa [forced,advance,Bool.or_comm,and_left_comm,and_comm,and_assoc] using f
  · have f := vforced (i := i-1) (j := j) (fun eq => h.2 (eq.mpr h.1))
    simpa [forced,advance,Bool.or_comm,and_left_comm,and_comm,and_assoc] using f

private theorem next_rim {n m v d} (h : rim n m v d) :
    rim n m (advance v d) d ∨ rim n m (advance v d) (turnL d) ∨
    rim n m (advance v d) (turnR d) := by
  cases d <;> simp [rim,advance,rightCell,leftCell,turnL,turnR] at * <;> tauto

private def leftToGo (n : Nat) (v : Pt) : Dir → Nat
  | .east => ((n:ℤ)-v.2).toNat
  | .south => ((n:ℤ)-v.1).toNat
  | .west => v.2.toNat
  | .north => v.1.toNat

private theorem straight_lt {n m v d} (h : forced n m v d) :
    leftToGo n (advance v d) d < leftToGo n v d := by
  cases d <;> simp [forced,advance,onBoard,leftToGo] at * <;> omega

/-- A rank on *directed forced edges*. Turns strictly decrease it;
remaining straight steps always decrease the distance to the grid boundary. -/
theorem routes_of_turn_rank {n : Nat} (m : Mask) (rank : Pt → Dir → Nat)
    (straight : ∀ v d, forced n m v d → forced n m (advance v d) d →
      rank (advance v d) d ≤ rank v d)
    (bend : ∀ v d e, e=turnL d ∨ e=turnR d → forced n m v d → forced n m (advance v d) e →
      rank (advance v d) e < rank v d) (r c : Fin (n-1)) :
    (holeDual n m).Reachable (.cell r c) .out := by
  have no (s : Pt × Dir) : ¬rim n m s.1 s.2 := by
    induction s using (measure (fun s : Pt × Dir => rank s.1 s.2*(n+1)+leftToGo n s.1 s.2)).wf.induction with
    | h s ih =>
      rcases s with ⟨v,d⟩
      intro h
      have f := rim_forced h
      have kill (e : Dir) (he : rim n m (advance v d) e)
          (p : rank (advance v d) e < rank v d) : False := by
        have fe := rim_forced he
        have bd : leftToGo n (advance v d) e ≤ n := by
          cases e <;> simp [forced,onBoard,leftToGo] at fe ⊢ <;> omega
        have g := Nat.mul_le_mul_right (n+1) (Nat.succ_le_of_lt p)
        rw [Nat.succ_mul] at g
        apply ih (advance v d,e) _ he
        change rank (advance v d) e*(n+1)+leftToGo n (advance v d) e <
          rank v d*(n+1)+leftToGo n v d
        omega
      rcases next_rim h with hx|hx|hx
      · have p := Nat.mul_le_mul_right (n+1) (straight v d f (rim_forced hx))
        have q := straight_lt f
        dsimp only at q
        apply ih (advance v d,d) _ hx
        change rank (advance v d) d*(n+1)+leftToGo n (advance v d) d <
          rank v d*(n+1)+leftToGo n v d
        omega
      · exact kill _ hx (bend _ _ _ (.inl rfl) f (rim_forced hx))
      · exact kill _ hx (bend _ _ _ (.inr rfl) f (rim_forced hx))
  by_contra fail
  have none (i : Nat) : ¬ dark n m ((i:ℤ),(c.val:ℤ)) := by
    induction i with
    | zero =>
      intro h; apply no ((0,(c.val:ℤ)),.east)
      exact ⟨h,fun b => by have z := (dark_bounds b).1; norm_num at z⟩
    | succ i ih =>
      intro h; apply no ((((i+1:Nat):ℤ),(c.val:ℤ)),.east)
      refine ⟨h,?_⟩
      simpa [leftCell] using ih
  apply none r.val
  unfold dark
  simpa [face,show (r.val:ℤ)<(n:ℤ)-1 by omega,show (c.val:ℤ)<(n:ℤ)-1 by omega] using fail

end GridGraphs.ResidueTwoLower.Turn
