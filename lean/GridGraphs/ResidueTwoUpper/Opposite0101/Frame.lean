import GridGraphs.ResidueTwoUpper.TwoGapRotate

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero Stencil TwoGap.Words TwoGap.Box

def word (c : Corner) := if c.1=c.2 then 3 else 13

theorem words {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 1 0 1) (c : Corner) :
    physicalWord (by omega) F c=word c := by
  obtain ⟨P,_,_,_,_,_,good,_⟩ := Frame.frame_of_score u F acy score
  have ok := physicalWord_ok (by omega) F P good c
  have decode : ∀ s : Fin 4 → Fin 4, packed s=code4 0 1 0 1 →
      ∀ i, s i=(if i.val%2=0 then 0 else 1) := by native_decide
  have d := decode _ canon
  rcases c with ⟨a,b⟩
  cases a <;> cases b
  case' false.false => have h := d 0; change digit _ F (false,false)=0 at h
  case' false.true => have h := d 1; change digit _ F (false,true)=1 at h
  case' true.false => have h := d 3; change digit _ F (true,false)=1 at h
  case' true.true => have h := d 2; change digit _ F (true,true)=0 at h
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ok
  all_goals rcases ok with z|z|z|z <;> first | exact z | simp [digit,z] at h

/-- Bits on either arm of the NW L, in local `(depth,column)` coordinates.
At the far end the cap is NE on the north arm and SW on the west arm. -/
def armBit (v : Bool) (n r j : Nat) : Option Bool :=
  if j≥n then some false else
  if r=0 then some (if v then decide (j+2≠n) else decide (j≠1 ∧ j≠2))
  else if j=0 then some (if v then decide (r≠1 ∧ r≠2) else true)
  else if j+1=n then some (if v then true else decide (r≠1))
  else if r=1 ∨ j=1 ∨ j+2=n then some false else none

def xy {α : Type*} (v : Bool) (r j : α) : α × α := if v then (j,r) else (r,j)

def vertex {n : Nat} (v : Bool) (r j : Nat) (hr : r<n) (hj : j<n) : GridVertex n n :=
  xy v ⟨r,hr⟩ ⟨j,hj⟩

private theorem smallWords : ∀ (v far : Bool) (r k : Fin 5) (flag : Bool),
    armBit v 35 r (if far then 34-k.val else k.val)=some flag →
    let c := xy v false far
    let rc := xy v r k
    (rc.1.val≤1 ∨ rc.2.val≤1) ∧ cell c (word c) 0 rc.1 rc.2=flag.toNat := by native_decide

private theorem frameEnd {n r j} (hn : 35 ≤ n) (J : j<n) (near : j≤4 ∨ j+5 ≥ n) (v : Bool) :
    armBit v 35 r (if 4 < j then 34-(n-1-j) else j)=armBit v n r j := by
  let J' := if 4 < j then 34-(n-1-j) else j
  have near' : ∀ x : Nat, x≤2 → (J'=x ↔ j=x) ∧ (J'+x=35 ↔ j+x=n) := by
    intro x hx; dsimp [J']; split <;> omega
  change armBit v 35 r J'=_
  have bd : J'<35 := by dsimp [J']; split <;> omega
  simp only [armBit,if_neg (Nat.not_le.mpr bd),if_neg (Nat.not_le.mpr J),
    (near' 0 (by decide)).1,(near' 1 (by decide)).1,(near' 2 (by decide)).1,
    (near' 1 (by decide)).2,(near' 2 (by decide)).2,ne_eq]

private theorem arm_far {n j r : Nat} (v flag : Bool) (J : j<n)
    (distance : 5 ≤ r ∨ (5 ≤ j ∧ j+5 < n)) (known : armBit v n r j=some flag) :
    (flag=true ∧ (r=0 ∨ j=0 ∨ j+1=n)) ∨
    (flag=false ∧ r≠0 ∧ j≠0 ∧ j+1≠n ∧ (r=1 ∨ j=1 ∨ j+2=n)) := by
  cases v <;> cases flag <;> simp [armBit,show ¬j≥n by omega] at known <;>
    split_ifs at known <;> simp_all <;> omega

set_option maxHeartbeats 800000 in
theorem armBit_physical {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 1 0 1)
    (v : Bool) {r j : Nat} (hr : r<7) (hj : j<35+42*u) {flag : Bool}
    (known : armBit v (35+42*u) r j=some flag) :
    decide (vertex v r j (by omega) hj ∈ F)=flag := by
  let n := 35+42*u
  have hn : 35 ≤ n := by dsimp [n]; omega
  obtain ⟨P,_,step,_,_,_,good,_⟩ := Frame.frame_of_score u F acy score
  have geo x := Frame.star_geometry hn F P step x (good (.inl x))
  by_cases near : r≤4 ∧ (j≤4 ∨ j+5 ≥ n)
  · let far := decide (4 < j)
    let k : Fin 5 := ⟨loc n far j,by dsimp [loc,far]; split_ifs <;> simp_all <;> omega⟩
    let t : Fin 5 := ⟨r,by omega⟩
    let c := xy v false far
    let rc := xy v t k
    have known' : armBit v 35 t (if far then 34-k.val else k.val)=some flag := by
      have J : j<n := hj
      convert (frameEnd (r:=r) hn J near.2 v).trans known using 2
      dsimp [t,k,loc,far]; split_ifs <;> simp_all
    obtain ⟨small,val⟩ := smallWords v far t k flag known'
    have phy := cell_physical hn F c (corners_marked u F acy score) (fun x => (geo x).1)
      (fun x => (geo x).2.1) rc.1 rc.2
    rw [words F acy score canon] at phy
    have matchVal : cell c (word c) (maskAt F (origin (by omega) c 2 2)) rc.1 rc.2 =
        cell c (word c) 0 rc.1 rc.2 := by
      change rc.1.val≤1 ∨ rc.2.val≤1 at small
      unfold cell; split_ifs <;> omega
    have matchPt : site hn c rc.1 rc.2=vertex v r j (by omega) hj := by
      cases v <;> ext <;> dsimp [c,xy,rc,site,vertex,k,t,loc,far,n] <;> split_ifs <;> omega
    rw [matchVal,matchPt] at phy
    exact (by decide : Function.Injective Bool.toNat) (phy.symm.trans val)
  · have distance : 5 ≤ r ∨ (5 ≤ j ∧ j+5 < n) := by omega
    have markOr := arm_far v flag hj distance known
    have geom : Frame.depthAt n (coord (vertex v r j (by omega) hj))=1 ∧ flag=false ∨
        Frame.straight n (coord (vertex v r j (by omega) hj)) ∧ flag=true := by
      rcases markOr with ⟨rfl,bd⟩|⟨rfl,rest⟩
      · right; refine ⟨?_,rfl⟩
        cases v <;> dsimp [vertex,xy,Frame.straight,Frame.depthAt,Frame.depth,coord,n] at * <;> omega
      · left; refine ⟨?_,rfl⟩
        cases v <;> dsimp [vertex,xy,Frame.depthAt,Frame.depth,coord,n] at * <;> omega
    rcases geom with ⟨g,rfl⟩|⟨g,rfl⟩
    · simp [(geo _).2.1 g]
    · simp [(geo _).1 g]

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
