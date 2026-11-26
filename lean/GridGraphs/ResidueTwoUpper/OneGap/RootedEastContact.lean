import GridGraphs.ResidueTwoUpper.OneGap.RootCoverField

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSeed FanSlab Camera BoundarySix.Connected

private theorem acrossEdge {u r c F v} (ru : r<35+42*u) (cu : c+1<35+42*u)
    (m : onSite F v r c=true ∨ onSite F v r (c+1)=true) :
    (Bonds F).Adj (railPoint u v c r) (railPoint u v (c+1) r) := by
  have a := railPoint_coords (v:=v) (by omega : c<35+42*u) ru
  have b := railPoint_coords (v:=v) cu ru
  constructor
  · rw [Camera.adj_iff v,a,b]; simp
  · have mark {d : Nat} (h : coordinates v (railPoint u v d r)=((r:Int),(d:Int)))
        (m : onSite F v r d=true) : railPoint u v d r∈F := by
      have eq := coords_view v (railPoint u v d r)
      rw [h] at eq
      unfold onSite at m
      rw [eq,marked_at] at m
      exact of_decide_eq_true m
    exact m.imp (mark a) (mark b)

theorem no_east_middle {u F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1) {j : Nat}
    (lo : 1≤j) (hi : j<11+14*u) (root : RootLine F v (10+14*u) j)
    (mid : bit (tile F v j (10+14*u)) 1=1) : False := by
  let n := 35+42*u
  let c := 1+3*(10+14*u)
  let r := 1+3*j
  have wall : c+3+1=n := by dsimp [c,n]; omega
  have rl : 3≤r := by dsimp [r]; omega
  have rh : r+2<n := by dsimp [r,n]; omega
  have cl : 0<c := by dsimp [c]; omega
  have m : onSite F v r (c+1)=true := readBit 1 mid
  have prem : preset n false (!H.cornerBit) 0 r=some true := by
    simp [preset,show r≠1 by omega,show r≠2 by omega,show r+2≠n by omega]
  have markedEnd := H.east 0 r (by omega) (by decide) (by omega) true prem
  rw [south_coords,turned] at markedEnd
  have endM : onSite F v r (c+2+1)=true := by
    change marked F (L7.view v (n:Nat) r (c+2+1:Nat))=true
    change marked F (L7.view v (n:Nat) r ((n:Int)-1-(0:Nat)))=true at markedEnd
    convert markedEnd using 3; omega
  let a := north_attachment (v:=v) cl (by omega : c+1<35+42*u) (stop:=3*j)
    (by dsimp [r,n] at *; omega) (F:=F) (fun i hi => root i (by omega))
  let x (d : Nat) (dl : 0<d) (dh : d+1<n) := railInner u v d r dl dh (by omega) (by omega)
  have e₁ : (interiorGraph F).Adj (x c cl (by omega)) (x (c+1) (by omega) (by omega)) :=
    acrossEdge (by omega) (by omega) (.inr m)
  have e₂ : (interiorGraph F).Adj (x (c+1) (by omega) (by omega)) (x (c+2) (by omega) (by omega)) :=
    acrossEdge (by omega) (by omega) (.inl m)
  let b : PerimeterVertex n := ⟨railPoint u v (c+2+1) r,(boundary_in_view v _).mpr (by
    rw [railPoint_coords (by omega) (by omega)]; dsimp; omega)⟩
  have path := a.reached.symm.trans (by
    simpa only [show 3*j+1=r by dsimp [r]; omega] using e₁.reachable.trans e₂.reachable)
  have eq := (unique_attachment (by omega) F acy one a.inside (x (c+2) (by omega) (by omega))
    a.rim b path a.link (acrossEdge (by omega) (by omega) (.inr endM))).2
  have same := congrArg (fun p : PerimeterVertex n => (coordinates v p.val).1) eq
  change (coordinates v (railPoint u v c 0)).1=(coordinates v (railPoint u v (c+2+1) r)).1 at same
  rw [railPoint_coords (by omega) (by omega),railPoint_coords (by omega) (by omega)] at same
  dsimp at same; omega

def eastOK (x : Nat) := !(x%2==1 && bit (x/2) 1==1)
def rimBank (a b : Nat) (top south : Bool) :=
  (labelBank a b top south).filter fun v => b != 12 || (eastOK v.2.1 && eastOK v.2.2.2)

theorem physical_east_filter {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (y f : Nat) (yl : 4≤y) (fl : 4≤f) (fh : f<11+14*u)
    (seed : ∀ i, f ≤ i → i < 11+14*u → RootLine F v i y) :
    let k := 11+14*u
    let t := fun r c => tile F v (y+r) (f+c)
    ∀ r c : Nat, r+2 ≤ k-y → c+2 ≤ k-f →
      (endTag (k-f) c != 12 || (eastOK (field t r (c+1)) && eastOK (field t (r+1) (c+1))))=true := by
  intro k t r c hr hc
  by_cases far : endTag (k-f) c=12
  · have loc : f+(c+1)=10+14*u := by unfold endTag at far; dsimp [k] at *; split_ifs at far <;> omega
    have safe (j : Nat) (jh : j≤r+1) : eastOK (field t j (c+1))=true := by
      have line (z : Nat) (on : flags t z (c+1)=true) : RootLine F v (f+(c+1)) (y+z) := by
        induction z with
        | zero => exact seed _ (by omega) (by omega)
        | succ z ih =>
          obtain ⟨old,m⟩ := Bool.and_eq_true_iff.mp on
          simp only [descent,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at m
          exact extend_line (ih old) m.1 m.2
      cases on : flags t j (c+1) with
      | false => simp [eastOK,field,labelled,on,Nat.mul_comm 2]
      | true =>
        have path := line j on
        rw [loc] at path
        have no := no_east_middle H acy one (by omega : 1≤y+j) (by dsimp [k] at *; omega) path
        have div (n : Nat) : (n*2+1)/2=n := by omega
        simp [eastOK,field,labelled,on,t,loc,Nat.mul_comm 2,div]
        exact no
    simp [far,safe r (by omega),safe (r+1) le_rfl]
  · simp [far]

theorem physical_rim_bank {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (y f : Nat) (yl : 4≤y) (fl : 4≤f) (fh : f<11+14*u)
    (seed : ∀ i, f ≤ i → i < 11+14*u → tile F v y i=73 ∧ RootLine F v i y) :
    let k := 11+14*u
    let t := fun r c => tile F v (y+r) (f+c)
    ∀ r c : Nat, r+2 ≤ k-y → c+2 ≤ k-f →
      word (field t) r c ∈ rimBank (endTag (k-y) r) (endTag (k-f) c)
        (r==0) (r+2==k-y) := by
  intro k t r c hr hc
  exact List.mem_filter.mpr ⟨physical_label_bank H acy one score hk y f yl fl fh seed r c hr hc,
    physical_east_filter H acy one y f yl fl fh (fun i l h => (seed i l h).2) r c hr hc⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
