import GridGraphs.ResidueTwoUpper.Orientation
import GridGraphs.ResidueTwoUpper.PatchColumns
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry

namespace GridGraphs.ResidueTwoUpper.Star
open NoPitch.Dual NoPitch.Keys Location

abbrev Site (s : Nat) := GridVertex s s
abbrev Dir := Fin 4
def dr : Dir → Nat := ![1,2,1,0]
def dc : Dir → Nat := ![2,1,0,1]
def fits (s i o : Nat) := 1 ≤ i+o ∧ i+o<s+1
instance (s i o) : Decidable (fits s i o) := inferInstanceAs (Decidable (_ ∧ _))
def inside (s i j : Nat) (d : Dir) := fits s i (dr d) ∧ fits s j (dc d)
instance (s i j d) : Decidable (inside s i j d) := inferInstanceAs (Decidable (_ ∧ _))
def step {s} (x : Site s) (d : Dir) (h : inside s x.1 x.2 d) : Site s :=
  (⟨x.1.val+dr d-1,by have := h.1.2; omega⟩,⟨x.2.val+dc d-1,by have := h.2.2; omega⟩)

def sample {s} (F : Finset (Site s)) (x : Site s) (d : Dir) :=
  if h : inside s x.1 x.2 d then decide (step x d h ∈ F) else false
def letter (s i j : Nat) (b : Dir → Bool) (d : Dir) :=
  if inside s i j d then (b d).toNat else 9

def encoding (s i j : Nat) (f : Bool) (b : Dir → Nat) (o : Option Dir) (g : Fin 8) :=
  let p := transform g s i j
  let loc := Location.axis s 6 p.1*16+Location.axis s 6 p.2
  let word := (List.finRange 4).foldl (fun z d => 10*z+b (Fin.ofNat 4 (direction (invers g) d))) (2*loc+f.toNat)
  5*word+(o.map (fun d => direction g d+1)).getD 0
def key (s i j : Nat) (f : Bool) (b : Dir → Nat) (o : Option Dir) :=
  2*minimum (encoding s i j f b o)

def compatible (s i j : Nat) (f : Bool) (b : Dir → Bool) (o : Option Dir) :=
  (∀ d : Dir, b d → inside s i j d ∧ !b (d+1)) ∧
    ∀ d ∈ o, inside s i j d ∧ (f || b d)=true
instance (s i j f b o) : Decidable (compatible s i j f b o) := by unfold compatible; infer_instance

def baseCheck (D : Chart) :=
  let ix := index D
  decide (∀ (i j : Fin 20) f b o, compatible 20 i j f b o →
    (locate D ix (key 20 i j f (letter 20 i j b) o)).any (fun col =>
      D.cols[col].objective*(D.cols[col].units:Int) == if f then 8 else 0))
theorem base_checked : baseCheck periodThree := by native_decide

theorem dir_of_adj {s} {x y : Site s} (adj : (gridGraph s s).Adj x y) :
    ∃ (d : Dir) (h : inside s x.1 x.2 d), step x d h=y := by
  rcases x with ⟨⟨i,hi⟩,⟨j,hj⟩⟩; rcases y with ⟨⟨u,hu⟩,⟨v,hv⟩⟩
  change adjacent s s _ _ at adj
  simp only [adjacent,Fin.ext_iff] at adj
  rcases adj with ⟨a,b|b⟩|⟨a,b|b⟩
  all_goals first
    | exact ⟨0,by change (1 ≤ i+1 ∧ i+1<s+1) ∧ (1 ≤ j+2 ∧ j+2<s+1); omega,
        Prod.ext (Fin.ext (by change i+1-1=u; omega)) (Fin.ext (by change j+2-1=v; omega))⟩
    | exact ⟨1,by change (1 ≤ i+2 ∧ i+2<s+1) ∧ (1 ≤ j+1 ∧ j+1<s+1); omega,
        Prod.ext (Fin.ext (by change i+2-1=u; omega)) (Fin.ext (by change j+1-1=v; omega))⟩
    | exact ⟨2,by change (1 ≤ i+1 ∧ i+1<s+1) ∧ (1 ≤ j+0 ∧ j+0<s+1); omega,
        Prod.ext (Fin.ext (by change i+1-1=u; omega)) (Fin.ext (by change j+0-1=v; omega))⟩
    | exact ⟨3,by change (1 ≤ i+0 ∧ i+0<s+1) ∧ (1 ≤ j+1 ∧ j+1<s+1); omega,
        Prod.ext (Fin.ext (by change i+0-1=u; omega)) (Fin.ext (by change j+1-1=v; omega))⟩

noncomputable def out {s} {F : Finset (Site s)} {root : Site s}
    (A : RootArrows (forcedEdgeGraph (gridGraph s s) (↑F : Set _)) root) (x : Site s) :=
  if h : ∃ d : Dir, ∃ ok : inside s x.1 x.2 d, A.parent x=some (step x d ok)
    then some h.choose else none

theorem out_spec {s} {F : Finset (Site s)} {root : Site s}
    (A : RootArrows (forcedEdgeGraph (gridGraph s s) (↑F : Set _)) root) (x : Site s) :
    ∀ d ∈ out A x, ∃ ok : inside s x.1 x.2 d, A.parent x=some (step x d ok) := by
  intro d; unfold out; split
  next h => intro e; cases e; exact h.choose_spec
  next => simp

theorem out_none {s} {F : Finset (Site s)} {root : Site s}
    (A : RootArrows (forcedEdgeGraph (gridGraph s s) (↑F : Set _)) root) (x : Site s) :
    out A x=none ↔ A.parent x=none := by
  unfold out
  split
  next h => obtain ⟨d,ok,e⟩ := h; simp [e]
  next h =>
    simp only [true_iff]
    cases e : A.parent x with
    | none => rfl
    | some y =>
      obtain ⟨d,ok,rfl⟩ := dir_of_adj (A.legal e).1
      exact False.elim (h ⟨d,ok,e⟩)

theorem physical_compatible {s} (F : Finset (Site s))
    (ac : (forcedEdgeGraph (gridGraph s s) (↑F : Set _)).IsAcyclic) {root : Site s}
    (A : RootArrows (forcedEdgeGraph (gridGraph s s) (↑F : Set _)) root) (x : Site s) :
    compatible s x.1 x.2 (decide (x∈F)) (sample F x) (out A x) := by
  constructor
  · intro d hd
    obtain ⟨ok,mem⟩ : ∃ h : inside s x.1 x.2 d, step x d h∈F := by
      simpa [sample] using hd
    refine ⟨ok,?_⟩
    by_contra! yes
    obtain ⟨ok',mem'⟩ : ∃ h : inside s x.1 x.2 (d+1), step x (d+1) h∈F := by
      simpa [sample] using yes
    apply CarrierLayers.ThreeCarrier.diagonal_preserved_false _ ac _ _ mem mem'
    all_goals
      have a := ok.1.1; have b := ok.2.1
      have c := ok'.1.1; have e := ok'.2.1
      dsimp only [step]
      have rr : dr d+1=dr (d+1) ∨ dr (d+1)+1=dr d := by fin_cases d <;> decide
      have cc : dc d+1=dc (d+1) ∨ dc (d+1)+1=dc d := by fin_cases d <;> decide
      omega
  · intro d hd
    obtain ⟨ok,e⟩ := out_spec A x d hd
    exact ⟨ok,by simpa [sample,ok] using (A.legal e).2⟩

end GridGraphs.ResidueTwoUpper.Star
