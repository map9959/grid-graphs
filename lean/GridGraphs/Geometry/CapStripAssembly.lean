import GridGraphs.Geometry.CapRowBill
import GridGraphs.Geometry.PitchMarkedCut

namespace GridGraphs.CapSite
open GridGraphs.Slit GridGraphs.Slit.Replay GridGraphs.Slit.Data GridGraphs.PitchCut

/-- One physical horizontal edge at a slit: its two incident marks and
whether it sends to the right. An absent edge never sets the direction bit. -/
structure Face where
  l : Bool
  r : Bool
  east : Bool

def Face.dir (f : Face) := (f.l || f.r) && f.east
def Face.code (f : Face) := one f.l+2*one f.r+4*one f.dir
def Face.flip (f : Face) : Face := ⟨f.r,f.l,!f.east⟩

/-- All strips in a row use the same `face` function. Downward directions
refer to the bond entering this row from above. -/
structure Band where
  face : Nat → Face
  center : Nat → Bool
  innerEast : Nat → Bool × Bool
  downs : Nat → Nat

def sample (b : Band) (t : Nat) : Row :=
  let a := b.face t
  let c := b.face (t+1)
  ⟨one a.l+2*one a.r+4*one (b.center t)+8*one c.l+16*one c.r,
   b.downs t,one a.dir+2*one (b.innerEast t).1+4*one (b.innerEast t).2+8*one c.dir⟩

private theorem letters (b : Band) (t : Nat) :
    letter (sample b t) 0=(b.face t).code ∧ letter (sample b t) 3=(b.face (t+1)).code := by
  generalize ha : b.face t=a
  generalize hc : b.face (t+1)=c
  simp only [sample,ha,hc,letter,Face.code,bit]
  rcases a with ⟨x,y,d⟩; rcases c with ⟨u,v,e⟩
  generalize b.center t=m
  generalize b.innerEast t=p
  rcases p with ⟨p,q⟩
  -- Direction bits at the internal bonds do not affect the two tapes.
  simp only [Face.dir]
  cases x <;> cases y <;> cases d <;> cases u <;> cases v <;> cases e <;>
    cases m <;> cases p <;> cases q <;> decide

def stripRows (bs : List Band) (t : Nat) := bs.map (sample · t)
def tape (bs : List Band) (t : Nat) := bs.map (fun b => (b.face t).code)
def kind (t d : Nat) := (if t=0 then 0 else 2)+d

/-- One side read from its guard to the meeting slit. Its only
combinatorial hypotheses are vertex laws, not automaton runs. -/
structure Half (n : Nat) where
  bands : List Band
  drops : Nat → Nat
  bounded : ∀ t<n, drops t ≤ 1
  guard : ∀ b∈bands, (b.face 0).code=0
  physical : ∀ t<n, PhysicalStrip (kind t (drops t)) initial (stripRows bands t)

def kept (H : Half n) := ∑ t ∈ Finset.range n, (1-H.drops t)
def paid (H : Half n) := ∑ t ∈ Finset.range n, stripCost initial (stripRows H.bands t)
def geometric (H : Half n) := ∑ t ∈ Finset.range n, stripGeom initial (stripRows H.bands t)
def rootCount (H : Half n) := ∑ t ∈ Finset.range n, stripSinks initial (stripRows H.bands t)

theorem half_prefix (ok : tablesOK) (H : Half n) :
    Prefix n (kept H) (paid H) (tape H.bands n) := by
  suffices ∀ m≤n, Prefix m (∑ t ∈ Finset.range m, (1-H.drops t))
      (∑ t ∈ Finset.range m, stripCost initial (stripRows H.bands t)) (tape H.bands m)
    from this _ le_rfl
  intro m; induction m with
  | zero =>
    intro _; simp only [Finset.range_zero,Finset.sum_empty]
    apply Prefix.guard
    intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact H.guard _ hb
  | succ m ih =>
    intro le
    have lt : m<n := by omega
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    apply Prefix.extend _ (H.bounded _ lt) (ih (by omega))
    have tr := (physical_strip_trace ok (show kind m (H.drops m)<4 by
      have := H.bounded _ lt; unfold kind; split_ifs <;> omega) (H.physical _ lt)).1
    simpa only [stripRows,trans,kind,tape,List.map_map,Function.comp_def,(letters _ _).1,(letters _ _).2]
      using tr

theorem half_paid (H : Half n) : (paid H : Int) = geometric H-2*n+2*rootCount H := by
  unfold paid geometric rootCount
  push_cast
  calc
    _ = ∑ t ∈ Finset.range n, (stripGeom initial (stripRows H.bands t)-2+
        2*(stripSinks initial (stripRows H.bands t) : Int)) := by
        apply Finset.sum_congr rfl; intro t ht
        have := strip_conservation (H.physical t (Finset.mem_range.mp ht))
        have : phi initial=2 := by decide
        omega
    _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,mul_comm]

private theorem face_arc (f : Face) : ∃ e ∈ reflect.arcs 0,
    left e=f.code ∧ right e=f.flip.code ∧ target e=0 ∧ bill e=0 := by
  rcases f with ⟨a,b,d⟩
  cases a <;> cases b <;> cases d <;>
    first | exact ⟨0,by decide +kernel⟩ | exact ⟨49,by decide +kernel⟩ |
      exact ⟨42,by decide +kernel⟩ | exact ⟨59,by decide +kernel⟩ |
      exact ⟨21,by decide +kernel⟩ | exact ⟨14,by decide +kernel⟩ | exact ⟨31,by decide +kernel⟩

theorem face_word (fs : List Face) :
    Trace reflect 0 0 (fs.map Face.code) (fs.map (fun f => f.flip.code)) := by
  induction fs with
  | nil => exact .stop (by decide +kernel) (by decide +kernel)
  | cons f fs ih =>
    obtain ⟨e,mem,x,y,d,c⟩ := face_arc f
    simp only [List.map_cons,←x,←y]
    exact .step mem (by omega) (by simpa [d,c] using ih)

/-- Assemble on a single physical seam in its original vertical order.
The site budgets telescope; only total geometry and the number of actual
nonterminal sinks are required, rather than per-strip bill equalities. -/
def assemble (ok : tablesOK) {k rank : Nat} {bonus : Int} (L : Half 2) (R : Half (k-1))
    (keeps : kept L+kept R+rank=k+1) (pos : 0 < kept L+kept R)
    (hk : 1≤k)
    (billEq : 4*bonus=2*((k:ℤ)+1)+2*rank-
      (geometric L+geometric R-2*(k+1)+2*(rootCount L+rootCount R : Nat)))
    (matchFaces : R.bands.map (fun b => b.face (k-1)) =
      (L.bands.map (fun b => b.face 2)).map Face.flip) : CapTrace k rank bonus where
  leftKept := kept L
  rightKept := kept R
  leftBill := paid L
  rightBill := paid R
  leftWord := tape L.bands 2
  rightWord := tape R.bands (k-1)
  kept := keeps
  pos := pos
  bill := by
    have := half_paid L; have := half_paid R
    push_cast at billEq; omega
  leftTrace := half_prefix ok L
  rightTrace := half_prefix ok R
  seam := by
    have h := face_word (L.bands.map (fun b => b.face 2))
    have eq := congrArg (List.map Face.code) matchFaces
    simp only [List.map_map,Function.comp_def] at eq h
    unfold tape; rwa [eq]

end GridGraphs.CapSite
