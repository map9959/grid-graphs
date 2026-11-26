import GridGraphs.NoPitch.StarCoverage
import GridGraphs.NoPitch.PhysicalWiring

namespace GridGraphs.NoPitch.FaceRows
open GridGraphs.NoPitch.Dual Keys PitchCut Wired Finset

/-- Original chart row numbers for patch/face marginals at side 19.
The dual keeps only the rows with nonzero multipliers. -/
def selected (D : Chart) (i : Nat) :=
  if h : i<D.rows.size then 4711≤D.rows[i].source && D.rows[i].source≤5172 else false
abbrev Terms := List (Nat × Int)
def terms (D : Chart) (c : Col) : Terms :=
  (c.terms.filter fun t => selected D t.1).map (fun t => (t.1,t.2*c.units))

theorem terms_coeff (D : Chart) (i : Nat) (sel : selected D i) (c : Col) :
    coeff i (terms D c)=coeff i c.terms*c.units := by
  unfold terms
  induction c.terms with
  | nil => simp [coeff]
  | cons t ts ih =>
    rcases t with ⟨j,v⟩
    by_cases e : j=i
    · subst j; simp [coeff,sel,add_mul] at ih ⊢; omega
    · cases h : selected D j <;> simp [coeff,h,e] at ih ⊢ <;> exact ih

def signatures (D : Chart) := D.cols.map (terms D)
def contribution (D : Chart) (m : Index) (ss : Array Terms) (key : Nat) : Terms :=
  match locate D m key with
  | none => []
  | some j => ss[j.val]?.getD []

theorem scatter_lhs {I : Type*} [Fintype I] (D : Chart) (i : Fin D.rows.size)
    (sel : selected D i) (keys : I → Nat) :
    lhs D (scatter D (index D) keys) i =
      ∑ x, coeff i (contribution D (index D) (signatures D) (keys x)) := by
  unfold lhs scatter; simp_rw [mul_sum]; rw [sum_comm]
  apply sum_congr rfl; intro x _
  cases h : locate D (index D) (keys x) with
  | none => simp [contribution,h,coeff]
  | some j =>
    rw [sum_eq_single j]
    · simpa [contribution,h,signatures,j.isLt] using (terms_coeff D i sel D.cols[j]).symm
    · intro b _ ne; simp [Ne.symm ne]
    · simp

def childAx (i : Fin 6) (d : Fin 2) : Fin (N 6-2) := ⟨3*i.val+d.val,by
  have := i.isLt; have := d.isLt; unfold N; omega⟩
def child (p : FacePos 6) (d : Corner) : PatchPos 6 := (childAx p.1 d.1,childAx p.2 d.2)
def slice (m : Mask) (d : Corner) : Nine := fun q =>
  m (Fin.ofNat 4 (d.1.val+q.1.val)) (Fin.ofNat 4 (d.2.val+q.2.val))

theorem slice_eq (F : Finset (Site 6)) (p : FacePos 6) (d : Corner) :
    slice (faceMask F p) d=patchMask F (child p d) := by
  funext q
  have axis_eq (i : Fin 6) (a : Fin 2) (b : Fin 3) :
      coord i (Fin.ofNat 4 (a.val+b.val))=Fin.ofNat (N 6) ((childAx i a).val+b.val) := by
    apply Fin.ext; have := i.isLt; have := a.isLt; have := b.isLt
    simp only [coord,N,Fin.val_ofNat,childAx]; omega
  simp only [slice,faceMask,axis_eq,child,patchMask]
  rfl

def children (w : Nat → Terms) (p : FacePos 6) (m : Mask) :=
  corners.flatMap fun d => w (patchCode (child p d) (slice m d))
def balanced (ts : Terms) := ts.all (fun t => coeff t.1 ts==0)
theorem zero_of_balanced (ts : Terms) (h : balanced ts) (i : Nat) : coeff i ts=0 := by
  by_cases m : ∃ t∈ts, t.1=i
  · obtain ⟨t,mem,rfl⟩ := m
    exact beq_iff_eq.mp (List.all_eq_true.mp h _ mem)
  · unfold coeff
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨t,mem,rfl⟩ := List.mem_map.mp hz
    simp [show t.1≠i from fun eq => m ⟨_,mem,eq⟩]

def missing (p : PatchPos 6) := p.1.val%3==2 || p.2.val%3==2
def otherOK (D : Chart) := D.cols.all fun c =>
  c.key%8==2 || c.key%8==4 || (terms D c).isEmpty
def rowOK (D : Chart) := D.rows.all fun r =>
  !(4711≤r.source && r.source≤5172) || (r.sense==0 && r.rhs==⟨0,0,0⟩)
def unusedOK (D : Chart) :=
  let w := contribution D (index D) (signatures D)
  decide (∀ p : PatchPos 6, missing p → ∀ a : Nine, w (patchCode p a)=[])

/-- Check sparse vectors for *all* selected rows at once, one face and
its four child patches at a time. Cache the children across partitions. -/
def tileOK (D : Chart) :=
  let w := contribution D (index D) (signatures D)
  decide (∀ i : Fin 65536, let m := maskOf i
    fresh initial (rawEdges m) →
    let kids := Vector.ofFn (n:=36) fun j =>
      children w (Fin.ofNat 6 (j.val/6),Fin.ofNat 6 j.val) m
    ∀ z∈catalog m, let vs := faceViews m (partOf z)
      ∀ p : FacePos 6, balanced (w (keyAt p vs) ++ kids[(6*p.1.val+p.2.val)%36]))

end GridGraphs.NoPitch.FaceRows
