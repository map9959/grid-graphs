import GridGraphs.ResidueTwoUpper.OneGap.SouthCapCoverageProblem
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapNumericField

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7
set_option maxRecDepth 1024

abbrev BoardOffset := Nat × Nat
def fits (p : BoardOffset) := p.1 < 18 ∧ p.2 < 18

theorem siteFits {p : BoardOffset} (h : p∈sites) : fits p := by
  obtain ⟨r,hr,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨c,hc,e⟩ := List.mem_map.mp hm
  rw [←e]
  exact ⟨List.mem_range.mp hr,List.mem_range.mp hc⟩

theorem move_geom {p : BoardOffset} (hp : fits p) {d : Nat} (hd : d<4)
    (inside : inHalo p d) :
    fits (move p d) ∧
    move (move p d) ((d+2)%4)=p ∧
    inHalo (move p d) ((d+2)%4)=true ∧
    adjacent 18 18 (⟨p.1,hp.1⟩,⟨p.2,hp.2⟩)
      (⟨(move p d).1,by
        unfold inHalo ResidueZero.inside at inside
        interval_cases d <;> simp [ResidueZero.shift,move] at * <;> omega⟩,
       ⟨(move p d).2,by
        unfold inHalo ResidueZero.inside at inside
        interval_cases d <;> simp [ResidueZero.shift,move] at * <;> omega⟩) := by
  unfold inHalo ResidueZero.inside at inside
  interval_cases d <;>
    simp only [fits,move,inHalo,ResidueZero.inside,ResidueZero.shift,adjacent,Fin.ext_iff,
      Prod.ext_iff, Bool.and_eq_true, decide_eq_true_eq] at * <;>
    norm_num [ResidueZero.shift] at * <;>
    have hx := hp.1 <;> have hy := hp.2 <;> omega

private theorem move_ne {p : BoardOffset} {d e : Nat} (hd : d<4) (he : e<4)
    (a : inHalo p d) (b : inHalo p e) (ne : d≠e) : move p d≠move p e := by
  unfold inHalo ResidueZero.inside at a b
  interval_cases d <;> interval_cases e <;>
    simp [move,ResidueZero.shift,Prod.ext_iff] at * <;> omega

theorem onBoard_iff {h w r c : Nat} (p : BoardOffset) :
    onBoard (endTag h r) (endTag w c) p ↔
      atlasSite h r p.1 < 119 ∧ atlasSite w c p.2 < 119 := by
  have castInside (x y : Nat) :
      ResidueZero.inside 119 (x,y) ↔ x<119 ∧ y<119 := by
    simp only [ResidueZero.inside, Bool.and_eq_true, decide_eq_true_eq]
    omega
  simp only [onBoard,absAt,atlasSite,baseAt,←Int.natCast_add]
  exact castInside _ _

def slot {h w r c : Nat} (p : BoardOffset) (hp : fits p)
    (hb : onBoard (endTag h r) (endTag w c) p) : Slots h w r c :=
  ⟨(⟨p.1,hp.1⟩,⟨p.2,hp.2⟩),(onBoard_iff p).mp hb⟩

theorem slot_board {h w r c : Nat} (x : Slots h w r c) :
    onBoard (endTag h r) (endTag w c) (x.1.1.val,x.1.2.val) := by
  exact (onBoard_iff _).mpr x.2

theorem move_board {h w r c : Nat} {p : BoardOffset} {d : Nat} (hd : d<4)
    (halo : inHalo p d) (board : ResidueZero.inside 119 (shift (absAt (endTag h r) (endTag w c) p) d)) :
    onBoard (endTag h r) (endTag w c) (move p d) := by
  unfold inHalo ResidueZero.inside at halo
  interval_cases d <;> simp [onBoard,absAt,move,ResidueZero.shift,ResidueZero.inside] at * <;> omega

theorem nextSlot_move {h w r c : Nat} {p : BoardOffset} (hp : fits p)
    (board : onBoard (endTag h r) (endTag w c) p) {d : Nat}
    (hd : d<4) (halo : inHalo p d)
    (endBoard : onBoard (endTag h r) (endTag w c) (move p d)) :
    nextSlot (slot p hp board) d=some (slot (move p d) (move_geom hp hd halo).1 endBoard :
      Slots h w r c) := by
  have bound := (move_geom hp hd halo).1
  have valid : atlasSite h r (move p d).1 < 119 ∧ atlasSite w c (move p d).2 < 119 := by
    exact (onBoard_iff _).mp endBoard
  have nonneg : 0≤(shift (p.1,p.2) d).1 ∧ 0≤(shift (p.1,p.2) d).2 := by
    have z := halo
    simp only [inHalo,ResidueZero.inside,Bool.and_eq_true,decide_eq_true_eq] at z
    exact ⟨z.1.1.1,z.1.2⟩
  unfold nextSlot
  change (if 0≤(shift (p.1,p.2) d).1 ∧ 0≤(shift (p.1,p.2) d).2 then
    optionalSlot (move p d).1 (move p d).2 else none)=_
  rw [if_pos nonneg]
  simp [optionalSlot,bound.1,bound.2,valid,slot]

/-- The numeric CNF's two opposed direction variables read the same
undirected edge of the physical halo. -/
theorem physical_edge_law {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : BoardOffset) (hp : p∈sites)
    (board : onBoard (endTag h r) (endTag w c) p) (d : Nat) (hd : d<4)
    (inside : ResidueZero.inside 119 (shift (absAt (endTag h r) (endTag w c) p) d))
    (halo : inHalo p d) :
    let a := numericField (windowField pl H)
    let q := move p d
    let x := a (arcVar p d)
    let y := a (arcVar q ((d+2)%4))
    (x || y)=(a (markVar p) || a (markVar q)) ∧ (x && y)=false := by
  let W := windowField pl H
  have geom := move_geom (siteFits hp) hd halo
  let x : Slots h w r c := slot p (siteFits hp) board
  let y : Slots h w r c := slot (move p d) geom.1 (move_board hd halo inside)
  have xy : nextSlot x d=some y := nextSlot_move _ _ hd halo _
  have yx : nextSlot y ((d+2)%4)=some x := by
    have dst : onBoard (endTag h r) (endTag w c) (move (move p d) ((d+2)%4)) := by
      rw [geom.2.1]
      exact board
    have e := nextSlot_move geom.1 (move_board hd halo inside) (d:=(d+2)%4) (by omega) geom.2.2.1 dst
    rw [show slot (move (move p d) ((d+2)%4)) _ dst=x from
      Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst geom.2.1)) (Fin.ext (congrArg Prod.snd geom.2.1)))] at e
    exact e
  have ax := numeric_arc W x ⟨d,hd⟩
  have ay := numeric_arc W y ⟨(d+2)%4,by omega⟩
  rw [xy] at ax
  rw [yx] at ay
  have adj : adjacent 18 18 x.1 y.1 := geom.2.2.2
  have edges := window_edges pl H x y
  change (numericField W (wireNumber p.1 p.2 (d+1)) ||
    numericField W (wireNumber (move p d).1 (move p d).2 (((d+2)%4)+1))) =
      (numericField W (wireNumber p.1 p.2 0) ||
        numericField W (wireNumber (move p d).1 (move p d).2 0)) ∧ _
  change numericField W (wireNumber p.1 p.2 (d+1))=W.arrow x y at ax
  change numericField W (wireNumber (move p d).1 (move p d).2 (((d+2)%4)+1))=W.arrow y x at ay
  have mx := numeric_mark W x
  have my := numeric_mark W y
  change numericField W (wireNumber p.1 p.2 0)=W.mark x at mx
  change numericField W (wireNumber (move p d).1 (move p d).2 0)=W.mark y at my
  constructor
  · simpa [ax,ay,mx,my,adj] using edges.1
  · change (numericField W (wireNumber p.1 p.2 (d+1)) &&
      numericField W (wireNumber (move p d).1 (move p d).2 (((d+2)%4)+1)))=false
    rw [ax,ay]
    exact edges.2

private theorem nextSlot_coords {h w r c : Nat} (x y : Slots h w r c) (d : Nat)
    (eq : nextSlot x d=some y) :
    let p := (x.1.1.val,x.1.2.val)
    inHalo p d = true ∧ (y.1.1.val,y.1.2.val)=move p d := by
  unfold nextSlot at eq
  dsimp only at eq ⊢
  split at eq
  · rename_i nonneg
    unfold optionalSlot at eq
    split at eq <;> try contradiction
    split at eq <;> try contradiction
    split at eq <;> try contradiction
    injection eq with e
    subst y
    rename_i hi hj _
    constructor
    · simp only [inHalo,ResidueZero.inside,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨⟨⟨nonneg.1,by omega⟩,nonneg.2⟩,by omega⟩
    · rfl
  · contradiction

/-- Only one of the compass wires can read the physical parent. -/
theorem physical_unique_law {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : BoardOffset) (hp : p∈sites)
    (d e : Nat) (hd : d<4) (he : e<4) (ne : d≠e) :
    let a := numericField (windowField pl H)
    (a (arcVar p d) && a (arcVar p e))=false := by
  let W := windowField pl H
  have fit := siteFits hp
  change (numericField W (wireNumber p.1 p.2 (d+1)) &&
    numericField W (wireNumber p.1 p.2 (e+1))) = false
  by_cases board : onBoard (endTag h r) (endTag w c) p
  · let x : Slots h w r c := slot p fit board
    have ad := numeric_arc W x ⟨d,hd⟩
    have ae := numeric_arc W x ⟨e,he⟩
    change numericField W (wireNumber p.1 p.2 (d+1)) = _ at ad
    change numericField W (wireNumber p.1 p.2 (e+1)) = _ at ae
    rw [ad,ae]
    apply Bool.eq_false_iff.mpr
    intro both
    simp only [Bool.and_eq_true] at both
    obtain ⟨ad,ae⟩ := both
    cases xd : nextSlot x d with
    | none => simp [xd] at ad
    | some y =>
      cases xe : nextSlot x e with
      | none => simp [xe] at ae
      | some z =>
        rw [xd] at ad
        rw [xe] at ae
        have ay : x≠y ∧ H.parent (pl.point v x)=pl.point v y := of_decide_eq_true ad
        have az : x≠z ∧ H.parent (pl.point v x)=pl.point v z := of_decide_eq_true ae
        have eq := pl.point_injective v (ay.2.symm.trans az.2)
        have yd := nextSlot_coords x y d xd
        have ze := nextSlot_coords x z e xe
        change inHalo p d=true ∧ _ at yd
        change inHalo p e=true ∧ _ at ze
        exact move_ne hd he yd.1 ze.1 ne
          (yd.2.symm.trans ((congrArg (fun s : Slots h w r c => (s.1.1.val,s.1.2.val)) eq).trans ze.2))
  · have no : optionalSlot (h:=h) (w:=w) (r:=r) (c:=c) p.1 p.2=none := by
      have notIn := fun inside => board ((onBoard_iff p).mpr inside)
      simp only [optionalSlot,dif_pos fit.1,dif_pos fit.2,dif_neg notIn]
    unfold numericField
    rw [read_wireNumber _ _ _ _ fit.2 (by omega),
      read_wireNumber _ _ _ _ fit.2 (by omega)]
    simp [slotValue,no]

/-- A single direction map must name the directed compass edges of
each window. This makes the already checked sheet equation usable
without any choices of arrows or sheets in the numeric assignment. -/
def NamesDirections {u k h w r c} (pl : Placement u k h w r c) (v : View)
    (dir : Site u → Site u → Nat) : Prop :=
  ∀ (x y : Slots h w r c) (d : Nat), d<4 → nextSlot x d=some y →
    dir (pl.point v x) (pl.point v y)=d

private def unview (v : View) (n : Int) (p : Pos) : Pos :=
  let a := reflect v.rowFar n p.1
  let b := reflect v.colFar n p.2
  if v.swap then (b,a) else (a,b)

private theorem unview_view (v : View) (n r c : Int) :
    unview v n (L7.view v n r c)=(r,c) := by
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [unview,L7.view,reflect]

/-- Compass numbering in the fan view, independent of the chosen window. -/
def fanDirection (u : Nat) (v : View) (x y : Site u) : Nat :=
  let a := unview v (35+42*(u:Int)) (coord x)
  let b := unview v (35+42*(u:Int)) (coord y)
  if b.2=a.2+1 then 0 else if b.1=a.1+1 then 1 else if b.2=a.2-1 then 2 else 3

theorem fanDirection_names {u k h w r c} (pl : Placement u k h w r c) (v : View) :
    NamesDirections pl v (fanDirection u v) := by
  intro x y d hd eq
  obtain ⟨inH,mv⟩ := nextSlot_coords x y d eq
  have row := congrArg Prod.fst mv
  have col := congrArg Prod.snd mv
  change y.1.1.val=(move (x.1.1.val,x.1.2.val) d).1 at row
  change y.1.2.val=(move (x.1.1.val,x.1.2.val) d).2 at col
  simp only [fanDirection,pl.point_coord, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    unview_view,haloSite]
  interval_cases d <;>
    simp only [move,ResidueZero.shift,Int.toNat_natCast,
      inHalo,ResidueZero.inside,Bool.and_eq_true,decide_eq_true_eq] at row col inH <;>
    norm_num at row col inH <;> split_ifs <;> omega

theorem physical_turn_law {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (names : NamesDirections pl v dir) (p : BoardOffset)
    (hp : p∈sites) (board : onBoard (endTag h r) (endTag w c) p)
    (d : Nat) (hd : d<4)
    (inside : ResidueZero.inside 119 (shift (absAt (endTag h r) (endTag w c) p) d))
    (halo : inHalo p d) (e : Nat) (he : e<4) (halo' : inHalo (move p d) e)
    (board' : onBoard (endTag h r) (endTag w c) (move (move p d) e)) :
    let a := numericField (windowField pl H)
    a (arcVar p d)=true → a (arcVar (move p d) e)=true →
    a (sheetVar (move p d))=xor (a (sheetVar p)) ((d==0 && e==3) || (d==3 && e==0)) := by
  let W := windowField pl H
  have fit := siteFits hp
  have fit' := (move_geom fit hd halo).1
  let x : Slots h w r c := slot p fit board
  let y : Slots h w r c := slot (move p d) fit' (move_board hd halo inside)
  let z : Slots h w r c := slot (move (move p d) e) (move_geom fit' he halo').1 board'
  have xy : nextSlot x d=some y := nextSlot_move _ _ hd halo _
  have yz : nextSlot y e=some z := nextSlot_move _ _ he halo' _
  have ad := numeric_arc W x ⟨d,hd⟩
  have ae := numeric_arc W y ⟨e,he⟩
  rw [xy] at ad
  rw [yz] at ae
  change numericField W (arcVar p d)=W.arrow x y at ad
  change numericField W (arcVar (move p d) e)=W.arrow y z at ae
  have sx := numeric_sheet W x
  have sy := numeric_sheet W y
  change numericField W (sheetVar p)=W.sheet x at sx
  change numericField W (sheetVar (move p d))=W.sheet y at sy
  dsimp only
  change numericField W (arcVar p d)=true → _
  rw [ad,ae,sx,sy]
  intro a b
  have eq : decide
      ((dir (pl.point v x) (pl.point v y)=0 ∧ dir (pl.point v y) (pl.point v z)=3) ∨
       (dir (pl.point v x) (pl.point v y)=3 ∧ dir (pl.point v y) (pl.point v z)=0)) =
      ((d==0 && e==3) || (d==3 && e==0)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
    rw [names x y d hd xy,names y z e he yz]
  simpa only [eq] using window_turn pl H x y z a b

/-- For the actual numeric window, only the rim presets and price
clauses remain to be proved. Ownership, uniqueness and the turn sheet
are supplied by the same physical halo. -/
theorem physical_clause_laws {u k h w r c F v q} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q (fanDirection u v))
    (prices : MarkPriceLaws (endTag h r) (endTag w c) H.cornerBit
      (numericField (windowField pl H))) :
    ClauseLaws (endTag h r) (endTag w c) H.cornerBit
      (numericField (windowField pl H)) where
  toMarkPriceLaws := prices
  unique p hp d e hd he ne := physical_unique_law pl H p hp d e hd he ne
  edge p hp b d hd i j := physical_edge_law pl H p hp b d hd i j
  turn p hp b d hd i j e he _ je be :=
    physical_turn_law pl H (fanDirection_names pl v) p hp b d hd i j e he je be

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
