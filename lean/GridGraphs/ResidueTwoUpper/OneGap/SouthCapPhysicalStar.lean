import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarAdmissible

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil L7
open Std.Sat
set_option maxRecDepth 1024

private theorem spin_sink (g o : Nat) : spin g o=4 ↔ o=4 := by
  unfold spin turn
  split <;> simp_all
  omega

private theorem out_sink {n : Nat} (x y : GridVertex n n) : outDir x y=4 ↔ y=x := by
  unfold outDir
  split_ifs <;> simp_all [eq_comm]

private theorem isolated_star_clear {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset) (hp : fits p)
    (board : onBoard (endTag h r) (endTag w c) p)
    (halo : (starDirs (absAt (endTag h r) (endTag w c) p)).all (inHalo p))
    (iso : (Bonds F).IsIsolated (pl.point v (slot p hp board))) :
    let z := absAt (endTag h r) (endTag w c) p
    let a := numericField (windowField pl H)
    let m := packVars a (starMarkVars p (starDirs z))
    bit m 0=0 ∧ neighbourCode (starDirs z) m=0 := by
  let x : Slots h w r c := slot p hp board
  let z := absAt (endTag h r) (endTag w c) p
  let a := numericField (windowField pl H)
  have atNeighbour (d : Nat) (on : d∈starDirs z) :
      a (markVar p)=false ∧ a (markVar (move p d))=false := by
    have d4 := List.mem_range.mp (List.mem_filter.mp on).1
    have iH := List.all_eq_true.mp halo d on
    let y : Slots h w r c := slot (move p d) (move_geom hp d4 iH).1
      (move_board d4 iH (List.mem_filter.mp on).2)
    have adj := (pl.point_adj v x y).mpr (move_geom hp d4 iH).2.2.2
    have mx := numeric_mark (windowField pl H) x
    have my := numeric_mark (windowField pl H) y
    change a (markVar p)=decide (pl.point v x∈F) at mx
    change a (markVar (move p d))=decide (pl.point v y∈F) at my
    rw [mx,my]
    constructor <;> apply decide_eq_false <;> intro mem
    · exact iso _ ⟨adj,Or.inl mem⟩
    · exact iso _ ⟨adj,Or.inr mem⟩
  have north : 3∈starDirs z := by
    obtain ⟨a,b⟩ := (onBoard_iff p).mp board
    have lo : 88≤atlasSite h r p.1 := atlasSite_ge88 pl.row
    apply List.mem_filter.mpr
    refine ⟨by decide,?_⟩
    have atZ : z=((atlasSite h r p.1:Int),(atlasSite w c p.2:Int)) := by
      simp only [z,absAt,baseAt,atlasSite,Nat.cast_add]
    rw [atZ]
    simp only [shift,inside,Bool.and_eq_true,decide_eq_true_eq]
    omega
  have packed := packed_star_bits a p z
  dsimp only
  rw [packed.1,packed.2,(atNeighbour 3 north).1]
  refine ⟨rfl,?_⟩
  have blank : (fun d : Fin 4 => inside 119 (shift z d) && a (markVar (move p d))) =
      fun _ => false := by
    funext d
    by_cases on : inside 119 (shift z d)
    · have mem : d.val∈starDirs z := List.mem_filter.mpr ⟨List.mem_range.mpr d.isLt,on⟩
      simp [(atNeighbour d mem).2]
    · simp [Bool.eq_false_iff.mpr on]
  rw [blank]
  decide

set_option maxHeartbeats 1000000 in
/-- The generator's star tests (legal local configuration, sink guard,
and price zero) hold on the one physical parent orientation. -/
theorem physical_star_readout {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) :
    StarReadout (endTag h r) (endTag w c) (numericField (windowField pl H)) := by
  intro p hp board
  let z := absAt (endTag h r) (endTag w c) p
  let ds := starDirs z
  let a := numericField (windowField pl H)
  change ds.all (inHalo p) → ∀ o∈ds++[4],
    (starGuard p ds o).eval a≠true → starReject119 z ds o (packVars a (starMarkVars p ds))=false
  intro halo o mem guard
  let fit := siteFits hp
  let s : Slots h w r c := slot p fit board
  let x := pl.point v s
  let m := packVars a (starMarkVars p ds)
  let f := decide (x∈F)
  have mark := physical_star_mark_readout pl H p fit board halo
  change bit m 0=f.toNat ∧ rotBits (viewIndex v) (neighbourCode ds m)=neighbours F (coord x) at mark
  have out : outDir x (H.parent x)=spin (viewIndex v) o :=
    guarded_star_out pl H p fit board o halo mem guard
  have ol : o<5 := by
    rcases List.mem_append.mp mem with d|d
    · exact Nat.lt_trans (List.mem_range.mp (List.mem_filter.mp d).1) (by decide)
    · have eq : o=4 := by simpa using d
      omega
  have nl : neighbourCode ds m<16 := by
    have h := (packed_star_bits a p z).2
    change neighbourCode ds m=_ at h
    rw [h]
    exact code_lt _
  let no : Fin 5 := ⟨o,ol⟩
  let nb : Fin 16 := ⟨neighbourCode ds m,nl⟩
  have ok := starOK_physical F acy x (H.parent x) (fun ne => H.step x ne.symm)
  change starOK (35+42*u:Nat) (coord x) f.toNat (neighbours F (coord x)) (outDir x (H.parent x))=true at ok
  have legal := starOK_atlas_transport pl v p fit board f nb no
  change starOK (35+42*u:Nat) (coord x) f.toNat (rotBits (viewIndex v) (neighbourCode ds m))
    (spin (viewIndex v) o) = starOK 119 z f.toNat (neighbourCode ds m) o at legal
  rw [mark.2,←out,ok] at legal
  have zero := H.atlas_star pl.size pl.wide pl.height pl.width pl.row pl.col
    (d:=p.1) (e:=p.2) (by have := fit.1; omega) (by have := fit.2; omega)
    x (pl.point_coord v s)
  have zEq : z=((atlasSite h r p.1:Int),(atlasSite w c p.2:Int)) := by
    simp only [z,absAt,baseAt,atlasSite,Nat.cast_add]
  have orbit := star_view_price v 119 z f.toNat nb no
  change twoOrbitStar 119 z f.toNat (neighbourCode ds m) o =
    twoOrbitStar 119 (L7.view v 119 z.1 z.2) f.toNat
      (rotBits (viewIndex v) (neighbourCode ds m)) (spin (viewIndex v) o) at orbit
  rw [mark.2,←out] at orbit
  have zero' : twoOrbitStar 119 z f.toNat (neighbourCode ds m) o=0 := by
    rw [orbit,zEq]
    exact zero
  have filter :
      (if z.1==118 && z.2==118 then f.toNat==1 && o==4
       else o != 4 || (f.toNat==0 && neighbourCode ds m==0))=true := by
    by_cases root : z.1=118 ∧ z.2=118
    · have eq : x=seSite u v := by
        apply (pl.point_root v s).mpr
        rw [zEq] at root
        change atlasSite h r p.1=118 ∧ atlasSite w c p.2=118
        constructor <;> omega
      have sink : o=4 := (spin_sink _ _).mp (out.symm.trans ((out_sink _ _).mpr (eq ▸ H.root)))
      have yes : f=true := decide_eq_true (eq ▸ scored_se_marked acy score)
      simp [root.1,root.2,yes,sink]
    · have off : (z.1==118 && z.2==118)=false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        simp only [Bool.and_eq_true,beq_iff_eq] at yes
        exact root yes
      rw [off]
      by_cases sink : o=4
      · have fix : H.parent x=x := (out_sink _ _).mp (out.trans ((spin_sink _ _).mpr sink))
        have notRoot : x≠seSite u v := by
          intro eq
          apply root
          rw [zEq]
          have b := (pl.point_root v s).mp eq
          change atlasSite h r p.1=118 ∧ atlasSite w c p.2=118 at b
          constructor <;> omega
        have iso := physical_nonroot_sink_isolated H acy score x notRoot fix
        have clear := isolated_star_clear pl H p fit board halo iso
        change bit m 0=0 ∧ neighbourCode ds m=0 at clear
        simp [sink,←mark.1,clear.1,clear.2]
      · simp [sink]
  change starReject119 z ds o m=false
  simp only [starReject119,mark.1,legal.symm,filter,zero',Bool.true_and,Bool.not_true,Bool.false_or]
  decide

/-- All local clauses of the generated physical window, with no
remaining price, edge, or rim assumptions. -/
theorem scored_halo_clauses {u k h w r c F v q} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q (fanDirection u v)) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) :
    ∀ cl∈clauseRows (endTag h r) (endTag w c) H.cornerBit,
      cl.eval (numericField (windowField pl H))=true :=
  clauseRows_hold (physical_clause_laws pl H (physical_mark_price_laws pl H
    (physical_price_readout_of_stars pl H acy (physical_star_readout pl H acy score))))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
