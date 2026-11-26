import GridGraphs.Tests.SouthCapAllPrices
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapBank

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open Std.Sat ResidueZero

abbrev Offset := Nat × Nat
def sites : List Offset := (List.range 18).flatMap fun r => (List.range 18).map (r,·)
def num (p : Offset) (t : Nat) := 6*(18*p.1+p.2)+t
def markVar (p : Offset) := num p 0
def arcVar (p : Offset) (d : Nat) := num p (d+1)
def sheetVar (p : Offset) := num p 5
def baseAt (t : Nat) := 1+3*repTile t-6
def absAt (r c : Nat) (p : Offset) : Pos := (baseAt r+p.1,baseAt c+p.2)
def move (p : Offset) (d : Nat) : Offset :=
  let q := shift (p.1,p.2) d
  (q.1.toNat,q.2.toNat)
def inHalo (p : Offset) (d : Nat) := inside 18 (shift (p.1,p.2) d)
def onBoard (r c : Nat) (p : Offset) := inside 119 (absAt r c p)
def starIx (x : Int) := if x<113 then ((x-6)%3).toNat else (x-110).toNat
def patchIx (x : Int) := if x<111 then ((x-6)%3).toNat else (x-108).toNat
private def pairs (xs : List Nat) :=
  xs.flatMap fun a => (xs.filter (a<·)).map (a,·)

private def cubeRows (vars : List Nat) (guard : CNF.Clause Nat) (cubes : List Nat) :
    List (CNF.Clause Nat) :=
  cubes.map fun z => guard ++
    (vars.zipIdx.filter fun (_,i) => (z%512).testBit i).map fun (x,i) => (x,!(z/512).testBit i)

/-- `a` is the mark at `(118,117)`; `(117,118)` has the opposite bit.
The near two sides of the atlas are outside every halo. -/
def seFrame (a : Bool) (p : Pos) : Option Bool :=
  if p=(118,117) then some a
  else if p=(117,118) then some !a
  else if p.1=118 ∨ p.2=118 then some true
  else if p.1=117 ∨ p.2=117 then some false
  else none

def patchVars (p : Offset) : List Nat :=
  (List.range 9).map fun i => markVar (p.1+i/3,p.2+i%3)
def fourVars : List Nat :=
  -- The saved ordinary bank is in producer order: NW, NE, SW, SE.
  [(6,6),(6,9),(9,6),(9,9)].flatMap patchVars
private def wordBits (m : Nat) : CNF.Clause Nat :=
  fourVars.zipIdx |>.map fun (x,i) => (x,!m.testBit i)

def clauseRows (r c : Nat) (a : Bool) : List (CNF.Clause Nat) := sites.flatMap fun p =>
  if !onBoard r c p then [] else
    let z := absAt r c p
    let rim := (seFrame a z).toList.map fun b => [(markVar p,b)]
    let patch := if p.1+2<18 && p.2+2<18 && inside 117 z then
      cubeRows (patchVars p) [] (patchCubes (patchIx z.1) (patchIx z.2)) else []
    let ds := (List.range 4).filter fun d => inside 119 (shift z d)
    if !ds.all (inHalo p) then rim ++ patch else
      let vars := markVar p :: ds.map (fun d => markVar (move p d))
      let arcs := ds.map (arcVar p)
      let unique := (pairs arcs).map fun (x,y) => [(x,false),(y,false)]
      let price := (ds++[4]).flatMap fun o =>
        let guard := if o=4 then arcs.map (·,true) else [(arcVar p o,false)]
        cubeRows vars guard (starCubes (starIx z.1) (starIx z.2) o)
      let edges := ds.flatMap fun d =>
        let p' := move p d
        let v := arcVar p d
        let w := arcVar p' ((d+2)%4)
        let x := markVar p
        let y := markVar p'
        let turns := (List.range 4).flatMap fun e =>
          if e=(d+2)%4 || !inHalo p' e || !onBoard r c (move p' e) then [] else
            let guard := [(v,false),(arcVar p' e,false)]
            let wrap := (d==0 && e==3) || (d==3 && e==0)
            [guard++[(sheetVar p,false),(sheetVar p',!wrap)],
             guard++[(sheetVar p,true),(sheetVar p',wrap)]]
        [[(x,false),(v,true),(w,true)],[(y,false),(v,true),(w,true)],
         [(v,false),(w,false)],[(v,false),(x,true),(y,true)],[(w,false),(x,true),(y,true)]] ++ turns
      rim ++ patch ++ unique ++ price ++ edges

def allowedWords (r c : Nat) : List Nat :=
  (packedBank[7*(r-6)+(c-6)]!).toList ++ (extra r c).map packWord

/-- The input to the refutation checker: the local clauses plus a
blocking clause for every word in the expanded catalogue. -/
def coverageProblem (r c : Nat) (a : Bool) : CNF Nat :=
  ⟨(clauseRows r c a ++ (allowedWords r c).map wordBits).toArray⟩

def projectedWord (assign : Nat → Bool) : Nat :=
  ((fourVars.zipIdx).map fun (x,i) => (assign x).toNat <<< i).sum

def packVars (a : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x::xs => (a x).toNat+2*packVars a xs

theorem packVars_bit (a : Nat → Bool) (xs : List Nat) (i : Nat) (hi : i<xs.length) :
    (packVars a xs).testBit i=a xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => cases h : a x <;> simp [packVars,Nat.testBit_zero,h]
    | succ i =>
      rw [Nat.testBit_succ]
      have div : packVars a (x::xs)/2=packVars a xs := by
        cases h : a x <;> simp [packVars,h]; omega
      rw [div]
      exact ih i (by simpa using hi)

private theorem cubeRows_hold (a : Nat → Bool) (vs : List Nat) (guard : CNF.Clause Nat)
    (row : List Nat) (ok : guard.eval a=true ∨ rejects row (packVars a vs)=false)
    {cl : CNF.Clause Nat} (mem : cl∈cubeRows vs guard row)
    (bits : ∀ z∈row, (z%512)<2^vs.length ∧ (z/512 &&& (z%512))=z/512) :
    cl.eval a=true := by
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp mem
  simp only [CNF.Clause.eval,List.any_append,Bool.or_eq_true]
  rcases ok with yes|no
  · exact Or.inl yes
  · right
    have ne : (packVars a vs &&& (z%512)) ≠ z/512 := by
      have misses := List.any_eq_false.mp no z hz
      simpa using misses
    have validValue := (bits z hz).2
    have someBit : ∃ i, (z%512).testBit i=true ∧
        (packVars a vs).testBit i≠(z/512).testBit i := by
      by_contra! all
      apply ne
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_and]
      cases h : (z%512).testBit i
      · have eq := congrArg (fun x : Nat => x.testBit i) validValue
        simpa [Nat.testBit_and,h] using eq
      · simpa [h] using all i h
    obtain ⟨i,yes,bad⟩ := someBit
    have hi : i<vs.length := by
      by_contra! le
      have lim := lt_of_lt_of_le (bits z hz).1 (Nat.pow_le_pow_right (by decide) le)
      exact Bool.noConfusion (yes.symm.trans (Nat.testBit_eq_false_of_lt lim))
    have hmem : (vs[i],i)∈vs.zipIdx := by
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
    rw [packVars_bit a vs i hi] at bad
    apply List.any_eq_true.mpr
    refine ⟨_,List.mem_map.mpr ⟨(vs[i],i),List.mem_filter.mpr ⟨hmem,yes⟩,rfl⟩,?_⟩
    dsimp
    cases x : a vs[i] <;> cases y : (z/512).testBit i <;> simp_all

/-- Exact interface between a halo assignment and the generated CNF.
`patch` and `star` refer to the audited compressed price rows;
`edge` and `turn` are in the producer's numeric wire order. -/
structure MarkPriceLaws (r c : Nat) (b : Bool) (a : Nat → Bool) : Prop where
  rim : ∀ p∈sites, onBoard r c p → ∀ m, seFrame b (absAt r c p)=some m → a (markVar p)=m
  patch : ∀ p∈sites, onBoard r c p →
    (p.1+2<18 && p.2+2<18 && inside 117 (absAt r c p)) →
    let row := patchCubes (patchIx (absAt r c p).1) (patchIx (absAt r c p).2)
    rejects row (packVars a (patchVars p))=false ∧
      (∀ z∈row, (z%512)<2^(patchVars p).length ∧ (z/512 &&& (z%512))=z/512)
  star : ∀ p∈sites, onBoard r c p →
    let ds := (List.range 4).filter fun d => inside 119 (shift (absAt r c p) d)
    ds.all (inHalo p) → ∀ o∈ds++[4],
    let vs := markVar p :: ds.map (fun d => markVar (move p d))
    let guard : CNF.Clause Nat := if o=4 then (ds.map (arcVar p)).map (·,true) else [(arcVar p o,false)]
    let row := starCubes (starIx (absAt r c p).1) (starIx (absAt r c p).2) o
    (guard.eval a=true ∨ rejects row (packVars a vs)=false) ∧
      (∀ z∈row, (z%512)<2^vs.length ∧ (z/512 &&& (z%512))=z/512)

structure ClauseLaws (r c : Nat) (b : Bool) (a : Nat → Bool) : Prop
    extends MarkPriceLaws r c b a where
  unique : ∀ p∈sites, ∀ d e, d<4 → e<4 → d≠e → (a (arcVar p d) && a (arcVar p e))=false
  edge : ∀ p∈sites, onBoard r c p → ∀ d<4, inside 119 (shift (absAt r c p) d) → inHalo p d →
    let q := move p d
    let x := a (arcVar p d)
    let y := a (arcVar q ((d+2)%4))
    (x || y)=(a (markVar p) || a (markVar q)) ∧ (x && y)=false
  turn : ∀ p∈sites, onBoard r c p → ∀ d<4, inside 119 (shift (absAt r c p) d) → inHalo p d →
    let q := move p d
    ∀ e<4, e≠(d+2)%4 → inHalo q e → onBoard r c (move q e) →
      a (arcVar p d)=true → a (arcVar q e)=true →
      a (sheetVar q)=xor (a (sheetVar p)) ((d==0 && e==3) || (d==3 && e==0))

set_option maxHeartbeats 1600000 in
theorem clauseRows_hold {r c b a} (laws : ClauseLaws r c b a) :
    ∀ cl∈clauseRows r c b, cl.eval a=true := by
  intro cl mem
  obtain ⟨p,hp,mem⟩ := List.mem_flatMap.mp mem
  by_cases board : onBoard r c p
  · simp only [board,Bool.not_true,Bool.false_eq_true,if_false] at mem
    let ds := (List.range 4).filter fun d => inside 119 (shift (absAt r c p) d)
    have rimSat {cl : CNF.Clause Nat} (h : cl∈(seFrame b (absAt r c p)).toList.map fun m => [(markVar p,m)]) :
        cl.eval a=true := by
      obtain ⟨m,hm,rfl⟩ := List.mem_map.mp h
      have eq := laws.rim p hp board m (Option.mem_toList.mp hm)
      simp [CNF.Clause.eval,eq]
    have patchSat {cl} (h : cl∈(if p.1+2<18 && p.2+2<18 && inside 117 (absAt r c p) then
        cubeRows (patchVars p) [] (patchCubes (patchIx (absAt r c p).1) (patchIx (absAt r c p).2)) else [])) :
        cl.eval a=true := by
      split at h
      · rename_i t
        have ok := laws.patch p hp board t
        exact cubeRows_hold _ _ _ _ (Or.inr ok.1) h ok.2
      · simp at h
    by_cases all : ds.all (inHalo p)
    · simp only [←show ds = (List.range 4).filter (fun d => inside 119 (shift (absAt r c p) d)) from rfl,
        all,Bool.not_true,Bool.false_eq_true,if_false,List.mem_append] at mem
      rcases mem with (((h|h)|h)|h)|h
      · exact rimSat h
      · exact patchSat h
      · obtain ⟨⟨x,y⟩,xy,rfl⟩ := List.mem_map.mp h
        obtain ⟨x',hx,yx⟩ := List.mem_flatMap.mp xy
        obtain ⟨y',hy,e⟩ := List.mem_map.mp yx
        obtain ⟨dx,mdx,dxEq⟩ := List.mem_map.mp hx
        obtain ⟨dy,mdy,dyEq⟩ := List.mem_map.mp (List.mem_filter.mp hy).1
        have lt := (List.mem_filter.mp hy).2
        cases e
        simp only [←dxEq,←dyEq] at lt ⊢
        have ne : dx≠dy := by intro z; subst dy; simp at lt
        have neq := laws.unique p hp dx dy
          (List.mem_range.mp (List.mem_filter.mp mdx).1)
          (List.mem_range.mp (List.mem_filter.mp mdy).1) ne
        cases hdx : a (arcVar p dx) <;> cases hdy : a (arcVar p dy) <;>
          simp_all [CNF.Clause.eval,List.any_cons,List.any_nil]
      · obtain ⟨o,ho,h⟩ := List.mem_flatMap.mp h
        have ok := laws.star p hp board all o ho
        exact cubeRows_hold _ _ _ _ ok.1 h ok.2
      · obtain ⟨d,md,h⟩ := List.mem_flatMap.mp h
        have hr := List.mem_filter.mp md
        have d4 := List.mem_range.mp hr.1
        have inH := List.all_eq_true.mp all d md
        rcases List.mem_append.mp h with h|h
        · have e := laws.edge p hp board d d4 hr.2 inH
          dsimp only at e
          simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl|rfl|rfl|rfl|rfl <;>
            simp only [CNF.Clause.eval,List.any_cons,List.any_nil] <;>
            revert e <;>
            generalize a (arcVar p d) = x, a (arcVar (move p d) ((d+2)%4)) = y,
              a (markVar p) = m, a (markVar (move p d)) = n <;>
            cases x <;> cases y <;> cases m <;> cases n <;> decide
        · obtain ⟨e,me,h⟩ := List.mem_flatMap.mp h
          split at h
          · simp at h
          · rename_i tri
            simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at tri
            have ne : e≠(d+2)%4 := fun eq => tri (Or.inl (Or.inl eq))
            have ih : inHalo (move p d) e=true := by
              by_contra! bad; exact tri (.inl (.inr (Bool.eq_false_iff.mpr bad)))
            have ob : onBoard r c (move (move p d) e)=true := by
              by_contra! bad; exact tri (.inr (Bool.eq_false_iff.mpr bad))
            have law := laws.turn p hp board d d4 hr.2 inH e (List.mem_range.mp me) ne ih ob
            simp only [List.mem_cons,List.not_mem_nil,or_false] at h
            rcases h with rfl|rfl <;>
              simp only [CNF.Clause.eval,List.cons_append,List.nil_append,List.any_cons,List.any_nil] <;>
              revert law <;>
              generalize a (arcVar p d) = x, a (arcVar (move p d) e) = y,
                a (sheetVar p) = sx, a (sheetVar (move p d)) = sy,
                ((d==0 && e==3) || (d==3 && e==0)) = warp <;>
              cases x <;> cases y <;> cases sx <;> cases sy <;> cases warp <;> decide
    · have aa : ds.all (inHalo p)=false := Bool.eq_false_iff.mpr all
      simp only [←show ds = (List.range 4).filter (fun d => inside 119 (shift (absAt r c p) d)) from rfl,
        aa,Bool.not_false,if_true,List.mem_append] at mem
      exact mem.elim rimSat patchSat
  · have no : onBoard r c p=false := Bool.eq_false_iff.mpr board
    simp [no] at mem

/-- Soundness of the catalogue refutation independently of how it was
generated. A satisfying physical assignment must agree bit-for-bit
with one saved word; the proof does not rely on an external model
enumeration or an assertion about solver completeness. -/
theorem admitted_bits {r c : Nat} {a : Bool}
    (unsat : (coverageProblem r c a).Unsat) (assign : Nat → Bool)
    (physical : ∀ cl∈clauseRows r c a, cl.eval assign=true) :
    ∃ m∈allowedWords r c, ∀ z∈fourVars.zipIdx, assign z.1=m.testBit z.2 := by
  classical
  by_contra! none
  have bad := unsat assign
  have sat : (coverageProblem r c a).eval assign=true := by
    simp only [coverageProblem,CNF.eval,Array.all_eq_true]
    intro i hi
    have mem := Array.getElem_mem (xs:=(clauseRows r c a ++ (allowedWords r c).map wordBits).toArray) hi
    rw [List.mem_toArray,List.mem_append] at mem
    rcases mem with h|h
    · exact physical _ h
    · obtain ⟨m,hm,e⟩ := List.mem_map.mp h
      rw [←e]
      obtain ⟨⟨x,b⟩,hx,ne⟩ := none m hm
      unfold wordBits CNF.Clause.eval
      apply List.any_eq_true.mpr
      refine ⟨(x,!m.testBit b),List.mem_map.mpr ⟨(x,b),hx,rfl⟩,?_⟩
      dsimp at ne ⊢
      cases a : assign x <;> cases t : m.testBit b <;> simp_all
  exact Bool.noConfusion (sat.symm.trans bad)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
