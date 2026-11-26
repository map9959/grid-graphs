import GridGraphs.Geometry.PhysicalNoPitchLine

/-! Incidences before quotienting by square symmetries. A face carries the
component relation of the *global* skeleton, not one independently chosen
corner partition per face. -/
namespace GridGraphs.NoPitch
open PitchCut Finset
variable {k : Nat} (F : Finset (Site k))

abbrev FacePos (k : Nat) := Fin k × Fin k
abbrev EdgeWord := Fin 4 → Bool
abbrev Mask := Fin 4 → EdgeWord

def coord (i : Fin k) (a : Fin 4) : Fin (N k) :=
  ⟨3*i.val+a.val,by have := i.isLt; have := a.isLt; unfold N; omega⟩

def faceMask (p : FacePos k) : Mask :=
  fun a b => decide ((coord p.1 a,coord p.2 b) ∈ F)

def skeleton := F.filter (fun x => x.1.val%3=0 ∨ x.2.val%3=0)

abbrev Corner := Fin 2 × Fin 2
def cornerOffset (b : Fin 2) : Fin 4 := ⟨3*b.val,by have := b.isLt; omega⟩
def corner (p : FacePos k) (c : Corner) : Site k :=
  (coord p.1 (cornerOffset c.1),coord p.2 (cornerOffset c.2))

noncomputable def joined (x y : Site k) : Bool := by
  classical
  exact decide ((forcedEdgeGraph (gridGraph (N k) (N k)) (↑(skeleton F) : Set _)).Reachable x y)

abbrev PartitionBits := Corner → Corner → Bool
noncomputable def faceAtom (p : FacePos k) : Mask × PartitionBits :=
  (faceMask F p,fun c d => joined F (corner p c) (corner p d))

/-- Four consecutive site bits as read by two successive line letters. -/
def lineEdge (v : Fin (N k)) (j : Fin k) : EdgeWord :=
  let a := letter F v j
  let b := letter F v (j.val+1)
  ![a.z,a.r,b.l,b.z]

theorem edge_agrees (p : FacePos k) (a : Fin 4) :
    faceMask F p a=lineEdge F (coord p.1 a) p.2 := by
  ext b
  have off (b : Fin 4) : 3*p.2.val+b.val<N k := (coord p.2 b).isLt
  have z : 3*(p.2.val+1)=3*p.2.val+3 := by omega
  fin_cases b <;> simp [faceMask,lineEdge,letter,coord,bit,z,
    show 3*p.2.val<N k from off 0,show 3*p.2.val+1<N k from off 1,
    show 3*p.2.val+2<N k from off 2,show 3*p.2.val+3<N k from off 3] <;> rfl

/-- Histogram over physical occurrences (as opposed to canonical column ids). -/
def hist {I A : Type*} [Fintype I] [DecidableEq A] (f : I → A) (a : A) : Nat :=
  ∑ i, if f i=a then 1 else 0

theorem marginal {I A B : Type*} [Fintype I] [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : I → A) (view : A → B) (b : B) :
    (∑ a, if view a=b then hist f a else 0)=hist (view ∘ f) b := by
  classical
  unfold hist
  simp_rw [Finset.ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  simpa [Function.comp_def] using (show
    (∑ a : A, if view a=b then (if f i=a then 1 else 0) else 0)=
      (if view (f i)=b then 1 else 0 : Nat) from by
    rw [sum_eq_single (f i)] <;> simp_all [eq_comm])

/-- Every pooled face/line overlap row, with arbitrary position labels.
Choose `a=0` or `3` to read either boundary of every coarse face. -/
theorem face_line_marginal {L : Type*} [Fintype L] [DecidableEq L]
    (label : FacePos k → L) (a : Fin 4) (target : L × EdgeWord) :
    (∑ atom : L × (Mask × PartitionBits),
      if (atom.1,atom.2.1 a)=target then
        hist (fun p => (label p,faceAtom F p)) atom else 0) =
      hist (fun p : FacePos k => (label p,lineEdge F (coord p.1 a) p.2)) target := by
  classical
  rw [marginal (fun p => (label p,faceAtom F p)) (fun atom => (atom.1,atom.2.1 a))]
  congr 1
  funext p
  exact congrArg (label p,·) (edge_agrees F p a)

private theorem across {i j : Fin k} (next : i.val+1=j.val) :
    coord i 3=coord j 0 := by
  apply Fin.ext; change 3*i.val+3=3*j.val+0; omega

/-- A cut records whether the endpoints lie in different skeleton trees.
Both occurrences along an internal edge use the very same connectivity. -/
noncomputable def faceBoundary (p : FacePos k) (side : Fin 2) : EdgeWord × Bool :=
  ((faceAtom F p).1 (cornerOffset side), !((faceAtom F p).2 (side,0) (side,1)))

theorem shared_boundary {i j : Fin k} (next : i.val+1=j.val) (x : Fin k) :
    faceBoundary F (i,x) 1=faceBoundary F (j,x) 0 := by
  have eq := across next
  have e : coord i (cornerOffset 1)=coord j (cornerOffset 0) := eq
  simp only [faceBoundary,faceAtom,corner,e,edge_agrees]

/-- State after exactly `t` letters of the physical line. -/
def prefixState (v : Fin (N k)) : Nat → State
  | 0 => start (!containsActive (word F v))
  | t+1 => advance (prefixState v t) (letter F v t)

def lineStep (v : Fin (N k)) (j : Fin k) : State × State :=
  (prefixState F v (j.val+1),prefixState F v (j.val+2))

def stepView (s : State × State) : EdgeWord :=
  let a := s.1.prev.getD default
  let b := s.2.prev.getD default
  ![a.z,a.r,b.l,b.z]

theorem step_view (v : Fin (N k)) (j : Fin k) :
    stepView (lineStep F v j)=lineEdge F v j := rfl

/-- The free chart's two face-to-transition constraints (top and
bottom) as equalities of pooled physical occurrence counts. -/
theorem pooled_overlap {L : Type*} [Fintype L] [DecidableEq L]
    (label : FacePos k → L) (a : Fin 4) (target : L × EdgeWord) :
    (∑ atom : L × (Mask × PartitionBits), if (atom.1,atom.2.1 a)=target then
      hist (fun p => (label p,faceAtom F p)) atom else 0) =
    ∑ step : L × (State × State), if (step.1,stepView step.2)=target then
      hist (fun p : FacePos k => (label p,lineStep F (coord p.1 a) p.2)) step else 0 := by
  rw [face_line_marginal,marginal (fun p : FacePos k => (label p,lineStep F (coord p.1 a) p.2))
    (fun step => (step.1,stepView step.2))]
  rfl

end GridGraphs.NoPitch
