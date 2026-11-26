import GridGraphs.Geometry.NoPitchLine
import GridGraphs.Geometry.PitchMarkedCut

namespace GridGraphs.NoPitch
open PitchCut Finset
variable {k : Nat} (F : Finset (Site k)) (v : Fin (N k))

/-- Reading outside the square gives the blank guard, never an extra mark. -/
def bit (c : Nat) : Bool := if h : c<N k then decide ((v,⟨c,h⟩)∈F) else false
def letter (i : Nat) : Letter :=
  ⟨decide (0 < i) && bit F v (3*i-1), bit F v (3*i), bit F v (3*i+1)⟩
def word := (List.range (k+1)).map (letter F v)

theorem nonpitch_word (np : ¬Pitch F v) :
    containsActive (word F v) ∨ containsVac (word F v) := by
  by_contra! bad
  have plain (i : Nat) (hi : i≤k) :
      (letter F v i).l=false ∧ (letter F v i).r=false ∧ (letter F v i).z=true := by
    have m : letter F v i ∈ word F v := List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩
    simp only [containsActive,containsVac] at bad
    cases l : (letter F v i).l <;> cases r : (letter F v i).r <;>
      cases z : (letter F v i).z <;> simp_all [active]
  apply np
  ext ⟨u,c⟩
  simp only [mem_filter,rowTeeth,mem_image,mem_univ,true_and,Prod.mk.injEq]
  constructor
  · rintro ⟨mc,rfl⟩
    have hc := c.isLt
    unfold N at hc
    let i := (c.val+1)/3
    have hi : i≤k := by dsimp [i]; omega
    obtain ⟨l,r,_⟩ := plain i hi
    have hit : bit F u c.val=true := by simp [bit,mc,c.isLt]
    have eq : 3*i=c.val := by
      by_contra ne
      rcases (show (0 < i ∧ 3*i-1=c.val) ∨ 3*i+1=c.val by dsimp [i] at *; omega) with ⟨p,e⟩|e
      · simp [letter,p,e,hit] at l
      · simp [letter,e,hit] at r
    exact ⟨⟨i,by omega⟩,rfl,Fin.ext eq⟩
  · rintro ⟨i,rfl,rfl⟩
    have h := (plain i.val (by omega)).2.2
    have bound : 3*i.val<N k := (teeth k i).isLt
    refine ⟨?_,rfl⟩
    change (v,⟨3*i.val,bound⟩) ∈ F
    simpa [letter,bit,bound] using h

private theorem end_range (s : State) (j n : Nat) (len : j+n=k+1)
    (init : s.prev.isNone → j=0) :
    endsOK s ((List.range' j n).map (letter F v)) := by
  induction n generalizing s j with
  | zero => trivial
  | succ n ih =>
    rw [List.range'_succ]; simp only [List.map_cons]
    refine ⟨fun h => by simp [letter,init h],?_,ih _ _ (by omega) (by simp [advance])⟩
    intro h
    have zero : n=0 := by simpa using congrArg List.length h
    have bound : ¬3*j+1<N k := by unfold N; omega
    simp [letter,bit,bound]

/-- Every actual non-pitch row supplies an accepting weighted run, with
exact debit, without assuming any run or chart variables as input. -/
theorem physical_line (np : ¬Pitch F v) :
    let w := word F v
    ∃ n, run (start (!containsActive w)) w=some n ∧
      (n:Int)=(w.map localCredit).sum+pathsFrom none w-1 := by
  obtain ⟨n,hn⟩ := noPitch_accepts _ (nonpitch_word F v np)
  refine ⟨n,hn,?_⟩
  have ends := end_range F v (start (!containsActive (word F v))) 0 (k+1) (by omega) (by simp)
  rw [←List.range_eq_range'] at ends
  have eq := run_price (w:=word F v) (by simp [word]) ends hn
  simpa [total_eq,start] using eq

end GridGraphs.NoPitch
