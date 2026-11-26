import GridGraphs.ResidueTwoUpper.OneGap.FanPortQuad

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port

abbrev Board := Array (Array (List Quad))
def row (G : Board) (r : Nat) := G[r]?.getD #[]
def atRC (G : Board) (r c : Nat) := (row G r)[c]?.getD []
def stamp (x y : Nat) := x + (y <<< 22)
def seam (q : Quad) : Nat → Nat
  | 0 => stamp q.c q.d
  | 1 => stamp q.b q.d
  | 2 => stamp q.a q.b
  | _ => stamp q.a q.c

def Kept (W H : Nat) (X : Nat → Nat → Quad) (G : Board) := ∀ r<H, ∀ c<W, X r c∈atRC G r c
def retain (s t : Nat) (A B : List Quad) := let keys := Std.HashSet.ofList (A.map (seam · s)); B.filter fun q => keys.contains (seam q t)
private theorem retain_mem {s t : Nat} {a b : Quad} {A B : List Quad} (ha : a∈A) (hb : b∈B) (e : seam a s=seam b t) : b∈retain s t A B := by
  apply List.mem_filter.mpr; refine ⟨hb,?_⟩; rw [Std.HashSet.contains_ofList,List.contains_iff_mem]; exact List.mem_map.mpr ⟨a,ha,e⟩
private theorem setKept {W H X G} (ok : Kept W H X G) {r c L} (hit : X r c∈L) : Kept W H X (G.setIfInBounds r ((row G r).setIfInBounds c L)) := by
  intro i hi j hj
  by_cases er : r=i
  swap
  · simpa only [atRC,row,Array.getElem?_setIfInBounds_ne er] using ok i hi j hj
  subst i; by_cases hr : r<G.size
  swap
  · simpa only [Array.setIfInBounds,dif_neg hr] using ok r hi j hj
  unfold atRC row; rw [Array.getElem?_setIfInBounds_self_of_lt hr]; dsimp only [Option.getD_some]
  by_cases ec : c=j
  swap
  · rw [Array.getElem?_setIfInBounds_ne ec]; exact ok r hi j hj
  subst j; by_cases hc : c<(row G r).size
  · change _∈(((row G r).setIfInBounds c L)[c]?.getD []); rwa [Array.getElem?_setIfInBounds_self_of_lt hc]
  · change _∈(((row G r).setIfInBounds c L)[c]?.getD []); rw [Array.setIfInBounds,dif_neg hc]; exact ok r hi c hj

structure Bond where
  r : Nat
  c : Nat
  y : Nat
  x : Nat
  s : Nat
  t : Nat
def bonds (W H : Nat) := let pts := (List.range H).flatMap fun r => (List.range W).map fun c => (r,c)
  let hor : List Bond := pts.filterMap fun (r,c) => if c+1<W then some ⟨r,c,r,c+1,0,2⟩ else none
  let ver : List Bond := pts.filterMap fun (r,c) => if r+1<H then some ⟨r,c,r+1,c,1,3⟩ else none
  let rev (e : Bond) : Bond := ⟨e.y,e.x,e.r,e.c,e.t,e.s⟩
  hor++ver++hor.reverse.map rev++ver.reverse.map rev

def topOK (dang : Bool) (q : Quad) := [q.a,q.c].all fun l => mask l==73 && out l 3==(if dang then 0 else 1)
def startWith (all : List Quad) (W H : Nat) (dang : Bool) := let first := all.filter (topOK dang)
  Array.ofFn fun i : Fin H => Array.replicate W (if i.val=0 then first else all)
abbrev startGrid := startWith master
def move (G : Board) (e : Bond) := G.setIfInBounds e.y ((row G e.y).setIfInBounds e.x (retain e.s e.t (atRC G e.r e.c) (atRC G e.y e.x)))
def scrub (W H : Nat) (es : List Bond) (G : Board) : Nat → Board
  | 0 => G
  | n+1 => es.foldl move (scrub W H es G n)
def testWith (all : List Quad) (W H d s rounds : Nat) (dang : Bool) :=
  let G := scrub W H (bonds W H) (startWith all W H dang) rounds
  (List.range (s+1)).all fun r => (atRC G r d).all fun q => mask q.a==73

abbrev test := testWith master

theorem window_with {all : List Quad} {W H d s rounds : Nat} {dang : Bool} (X : Nat → Nat → Quad)
    (init : ∀ r<H, ∀ c<W, X r c∈all ∧ (r=0 → topOK dang (X r c)))
    (agree : ∀ e∈bonds W H, e.r<H ∧ e.c<W ∧ e.y<H ∧ e.x<W ∧ seam (X e.r e.c) e.s=seam (X e.y e.x) e.t)
    (pass : testWith all W H d s rounds dang) (fit : s<H ∧ d<W) : ∀ r≤ s, mask (X r d).a=73 := by
  have K : Kept W H X (startWith all W H dang) := by
    intro r hr c hc; obtain ⟨hin,top⟩ := init r hr c hc; by_cases e : r=0
    · simpa [atRC,row,startWith,hr,hc,e,show 0<H by omega] using And.intro hin (top e)
    · simpa [atRC,row,startWith,hr,hc,e] using hin
  have sweep (G : Board) (h : Kept W H X G) (es : List Bond) (sub : ∀ e∈es,e∈bonds W H) : Kept W H X (es.foldl move G) := by
    induction es generalizing G with
    | nil => exact h
    | cons a es ih =>
      obtain ⟨a1,a2,a3,a4,ax⟩ := agree a (sub _ (.head _)); apply ih _ (setKept h (retain_mem (h _ a1 _ a2) (h _ a3 _ a4) ax)) (fun e he => sub _ (.tail _ he))
  have sound (n) : Kept W H X (scrub W H (bonds W H) (startWith all W H dang) n) := by induction n with
    | zero => exact K
    | succ n ih => exact sweep _ ih _ (fun _ he => he)
  intro r hr; exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp pass r (List.mem_range.mpr (by omega))) _ (sound rounds r (by omega) d fit.2))
theorem window {W H d s rounds : Nat} {dang : Bool} (X : Nat → Nat → Quad)
    (init : ∀ r<H, ∀ c<W, X r c∈master ∧ (r=0 → topOK dang (X r c)))
    (agree : ∀ e∈bonds W H, e.r<H ∧ e.c<W ∧ e.y<H ∧ e.x<W ∧ seam (X e.r e.c) e.s=seam (X e.y e.x) e.t)
    (pass : test W H d s rounds dang) (fit : s<H ∧ d<W) : ∀ r≤ s, mask (X r d).a=73 := window_with X init agree pass fit
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
