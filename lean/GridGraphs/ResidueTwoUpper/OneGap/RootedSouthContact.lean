import GridGraphs.ResidueTwoUpper.OneGap.RootedRailPhysicalStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSeed FanSlab BoundarySix.Connected

/-- Every plaquette from row and column four through the far fringes;
the 43-row restriction applies to the cap schedule, not its atlas. -/
theorem board_word {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) {y x : Nat} (yl : 4≤y) (xl : 4≤x)
    (yh : y+2≤11+14*u) (xh : x+2≤11+14*u) :
    word (tile F v) y x ∈ bankWords (endTag (11+14*u) y) (endTag (11+14*u) x) := by
  let k := 11+14*u
  let pl : Placement u k (k-y) (k-x) 0 0 :=
    ⟨rfl,hk,by dsimp [k]; omega,by dsimp [k]; omega,by dsimp [k]; omega,by dsimp [k]; omega⟩
  have adm := physical_rectangle_word pl H acy score
  have tag (a : Nat) (ha : a+2≤k) : endTag (k-a) 0=endTag k a := by
    unfold endTag; split_ifs <;> omega
  rw [tag y yh,tag x xh] at adm
  have equal : rectWord F v k (k-y) (k-x) 0 0=word (tile F v) y x := by
    simp only [rectWord,word,tile,firstRow,show k-(k-y)=y by omega,
      show k-(k-x)=x by omega,Nat.mul_zero,Nat.add_zero,Nat.mul_add,Nat.mul_one,Nat.add_assoc]
  rw [equal] at adm
  have small (r c : Nat) : tile F v r c<512 := (unpack _).1
  exact bankWords_cover ⟨small ..,small ..,small ..,small ..⟩ adm

theorem no_south_middle {u F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1) {i : Nat}
    (lo : 1 ≤ i) (hi : i < 11+14*u) (root : RootLine F v i (10+14*u))
    (mark : bit (tile F v (10+14*u) i) 3=1) : False := by
  let n := 35+42*u
  let c := 1+3*i
  have CL : 0<c := by dsimp [c]; omega
  have CU : c+2<n := by dsimp [c,n]; omega
  have markedMid : onSite F v (n-3) c=true := by
    have m : onSite F v (1+3*(10+14*u)+1) c=true := readBit 3 mark
    simpa only [show 1+3*(10+14*u)+1=n-3 by dsimp [n]; omega] using m
  have mEnd : onSite F v (n-1) c=true := by
    have prem : preset n false H.cornerBit 0 c=some true := by
      simp [preset,c,show i≠0 by omega,show 1+3*i≠2 by omega,
        show 1+3*i+2≠n by dsimp [n]; omega]
    have m := H.south 0 c (by dsimp [c]; omega) (by decide) (by omega) true prem
    rw [south_coords] at m
    change marked F (L7.view v (n:Nat) (n-1:Nat) c)=true
    rw [Nat.cast_sub (show 1≤n by dsimp [n]; omega)]
    simpa only [Nat.cast_one,Nat.cast_zero,sub_zero] using m
  let a := north_attachment (F:=F) (v:=v) CL (by omega : c+1<n) (stop:=n-3)
    (by dsimp [n]; omega : n-3+2<35+42*u) (by
      intro r bound
      by_cases before : r<1+3*(10+14*u)
      · exact root r before
      · apply Bool.or_eq_true_iff.mpr
        rcases (show r=n-3 ∨ r+1=n-3 by dsimp [n] at *; omega) with e|e
        · exact .inl (e ▸ markedMid)
        · exact .inr (e ▸ markedMid))
  let b : PerimeterVertex n := ⟨railPoint u v c (n-1),(boundary_in_view v _).mpr (by
    rw [railPoint_coords (by dsimp [n] at *; omega) (by dsimp [n]; omega)]
    right; left; dsimp [n]; omega)⟩
  have link := rail_edge (F:=F) (v:=v) (r:=n-3+1) (by omega : c<35+42*u)
    (by dsimp [n]; omega) (Bool.or_eq_true_iff.mpr (Or.inr
      (show onSite F v (n-3+1+1) c=true by rwa [show n-3+1+1=n-1 by dsimp [n]; omega])))
  rw [show n-3+1+1=n-1 by dsimp [n]; omega] at link
  have eq := (unique_attachment (by omega) F acy one a.inside _ a.rim b
    a.reached.symm a.link link).2
  have re := congrArg (fun t : PerimeterVertex n => (coordinates v t.val).1) eq
  change (coordinates v (railPoint u v c 0)).1=(coordinates v (railPoint u v c (n-1))).1 at re
  rw [railPoint_coords (by omega) (by omega),railPoint_coords (by omega) (by dsimp [n]; omega)] at re
  dsimp [n] at re; omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
