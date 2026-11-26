import GridGraphs.ResidueTwoUpper.OneGap.FanCollisionWide
import GridGraphs.ResidueTwoUpper.OneGap.TwoAncestry

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
open ResidueZero FanSlab L7 Camera Port Port.Halo Short BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan SouthCap.Strip.GridScan.Rooted
local notation "tile'" => Rooted.tile

-- A pin fixes the mask at a tile of the translated owner chart.
private abbrev Pin := Nat × Nat × List Nat
private def board (pins : List Pin) (guard : Nat → Nat → Nat → Bool) :=
  build 15 fun r c => ((List.range 512).filter fun m =>
    accepts (5+(r+1)%3) (5+(c+1)%3) m && pins.all fun (i,j,ms) =>
      r != 3*i || c != 3*j || ms.contains m).flatMap fun m =>
        ((List.range 4).filter fun o => active m o && guard r c o).map (m,·)
def dir {u F} (Q : Flow (n:=N u) F) (v : View) (r c : Nat) :=
  arrow Q.parent v ((r:Nat),(c:Nat))
def center {u F} (Q : Flow (n:=N u) F) (v : View) (r c : Nat) := dir Q v (2+3*r) (2+3*c)
def headDir {u F} (Q : Flow (n:=N u) F) (v : View) (r c : Nat) := dir Q v (1+3*r) (1+3*c)

set_option maxHeartbeats 1000000 in
private theorem readout {u F v} (Q : Flow (n:=N u) F) (price : Prices F v) {a b : Nat}
    (ar : 3≤a ∧ a+9≤11+14*u) (bc : 3≤b ∧ b+9≤11+14*u)
    (pins : List Pin) (guard : Nat → Nat → Nat → Bool)
    (plant : ∀ p∈pins, tile' F v (a+p.1) (b+p.2.1)∈p.2.2)
    (direction : ∀ r<15, ∀ c<15, guard r c (dir Q v (2+3*a+r) (2+3*b+c))) :
    ∀ r<15, ∀ c<15, (square F v (1+3*a+r) (1+3*b+c),dir Q v (2+3*a+r) (2+3*b+c))∈
      atRC (prune 15 10 (board pins guard)) r c := by
  let R := 1+3*a; let C := 1+3*b
  obtain ⟨X,agree,act,sq,ds⟩ := CollisionWide.owner_chart Q price R C 15
    (by dsimp [R]; omega) (by dsimp [C]; omega)
  have owner (r c : Nat) (hr : r<15) (hc : c<15) :
      (X r c).2=dir Q v (2+3*a+r) (2+3*b+c) := by
    rw [ds]; unfold dirsAt dir
    have lt := dir_lt F v Q price (R+(r+1)) (C+(c+1)) (by dsimp [R]; omega) (by dsimp [C]; omega)
    change arrow Q.parent v ((R+(r+1):Nat),(C+(c+1):Nat))%4=_
    rw [Nat.mod_eq_of_lt lt,show R+(r+1)=2+3*a+r by dsimp [R]; omega,
      show C+(c+1)=2+3*b+c by dsimp [C]; omega]
  have kept : Kept 15 X (board pins guard) := by
    intro r hr c hc
    have m := price (R+r) (C+c) (by dsimp [R]; omega) (by dsimp [R]; omega)
      (by dsimp [C]; omega) (by dsimp [C]; omega)
    rw [←sq,show (R+r)%3=(r+1)%3 by dsimp [R]; omega,show (C+c)%3=(c+1)%3 by dsimp [C]; omega] at m
    rw [board,at_build hr hc]
    refine List.mem_flatMap.mpr ⟨(X r c).1,List.mem_filter.mpr ⟨List.mem_range.mpr ?_,
      Bool.and_eq_true_iff.mpr ⟨m,List.all_eq_true.mpr ?_⟩⟩,List.mem_map.mpr ⟨(X r c).2,
      List.mem_filter.mpr ⟨List.mem_range.mpr ?_,Bool.and_eq_true_iff.mpr ⟨act r hr c hc,?_⟩⟩,rfl⟩⟩
    · rw [sq]; exact (unpack _).1
    · rintro ⟨i,j,ms⟩ h
      simp only [Bool.or_eq_true,bne_iff_ne,List.contains_iff_mem]
      by_cases e : r=3*i
      · by_cases g : c=3*j
        · right; rw [sq,e,g,show R+3*i=1+3*(a+i) by dsimp [R]; omega,
            show C+3*j=1+3*(b+j) by dsimp [C]; omega]; exact plant (i,j,ms) h
        · exact .inl (.inr g)
      · exact .inl (.inl e)
    · rw [ds]; exact (dirsAt Q v R C (r+1) (c+1)).isLt
    · rw [owner _ _ hr hc]; exact direction _ hr _ hc
  intro r hr c hc
  have z := prune_kept kept agree 10 r hr c hc
  change (square F v (R+r) (C+c),_)∈_
  rwa [←sq,←owner _ _ hr hc,Prod.mk.eta]

private def rimMasks := [3,6,7,8,12,18,32,144,146]
private def innerMasks := [6,8,32,144]
private def candidates (rim : Bool) := if rim then rimMasks else innerMasks
private def law (w : Word) : Prop :=
  let (a,b,c,d) := w
  a∈shapes → b∈shapes → (c∉shapes → c∈rimMasks) ∧ (c∈shapes → d∉shapes → d∈innerMasks)
private instance (w) : Decidable (law w) := by unfold law; infer_instance
private theorem wordCheck : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (law w))=true := by native_decide
theorem wordAt {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤11+14*u) (ch : c+2≤11+14*u) :
    law (Strip.word (tile' F v) r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := wordCheck ⟨endTag (11+14*u) r-6,by omega⟩ ⟨endTag (11+14*u) c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag (11+14*u) r-6)=_ by exact Nat.add_sub_of_le R.1,
    show 6+(endTag (11+14*u) c-6)=_ by exact Nat.add_sub_of_le C.1] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))

private def pins (rim : Bool) : List Pin :=
  [(1,2,shapes),(2,2,candidates rim)] ++
    (if rim then [(1,3,shapes)] else [(1,1,shapes),(2,1,shapes)])
private def gate (north : Bool) (r c o : Nat) :=
  r != 5 || c != 5 || (o==3)==north
def exits (rim north : Bool) : List (Nat × Nat) :=
  if north then (if rim then [(3,3),(7,3),(144,1)] else [])
  else if rim then [(3,3),(6,3),(7,3),(8,2),(12,2),(18,1),(32,0),(144,1),(146,1)]
  else [(6,3),(8,2),(32,0),(144,1)]
private theorem exitCheck : ∀ rim north : Bool,
    (atRC (prune 15 10 (board (pins rim) (gate north))) 6 6).all
      (fun z => (exits rim north).contains z) := by native_decide

/-- Row-major order in the actual movement window. -/
def First {u} (F : Finset (Site u)) (v : View) (y x W h j i : Nat) :=
  1≤j ∧ j≤h ∧ i≤W ∧ tile' F v (y+j) (x+i)∉shapes ∧
  (∀ d<j, ∀ e≤W, tile' F v (y+d) (x+e)∈shapes) ∧
  ∀ e < i, tile' F v (y+j) (x+e)∈shapes
theorem first_of_bad {u v q y x f W h} {F : Finset (Site u)} (front : Front F v q (11+14*u) y f)
    (left : f≤x) (width : x+W<11+14*u) (bad : ¬Straight F v y x W h) :
    ∃ j i, First F v y x W h j i := by
  classical
  unfold Straight at bad; push Not at bad
  let j := Nat.find bad
  obtain ⟨jh,ex⟩ := Nat.find_spec bad
  let i := Nat.find ex
  obtain ⟨iw,miss⟩ := Nat.find_spec ex
  refine ⟨j,i,?_,jh,iw,miss,?_,?_⟩
  · by_contra! low
    change i≤W at iw
    apply miss
    change tile' F v (y+j) (x+i)∈shapes
    have m : tile' F v y (x+i)=73 := front.1 y le_rfl le_rfl (x+i) (by omega) (by omega)
    rw [show y+j=y by omega,m]
    decide
  · intro d dj e ew; by_contra no
    exact Nat.find_min bad dj ⟨by change j≤h at jh; omega,e,ew,no⟩
  · intro e ei; by_contra no
    exact Nat.find_min ex ei ⟨by change i≤W at iw; omega,no⟩

set_option maxHeartbeats 1500000 in
theorem forced_exit_at {u F v q y x W h j i} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (Q : Flow F) (price : Prices F v) (yl : 4≤y) (xl : 7≤x) (ww : 1≤W)
    (hr : y+h+8≤11+14*u) (wc : x+W+8≤11+14*u) (bad : First F v y x W h j i) :
    (tile' F v (y+j) (x+i),center Q v (y+j) (x+i)) ∈
      exits (decide (i=0)) (headDir Q v (y+j) (x+i)==3) := by
  obtain ⟨jl,jh,iw,miss,upper,west⟩ := bad
  let a := y+j-2; let b := x+i-2; let rim := decide (i=0); let north := headDir Q v (y+j) (x+i)==3
  have A : a+2=y+j := by dsimp [a]; omega
  have B : b+2=x+i := by dsimp [b]; omega
  have U := upper (j-1) (by omega)
  have P : ∀ p∈pins rim, tile' F v (a+p.1) (b+p.2.1)∈p.2.2 := by
    by_cases z : i=0
    · subst i
      have L := wordAt H acy score hk (by omega : 4≤y+(j-1)) (by omega : 4≤x) (by omega) (by omega)
      have law' := L (U 0 (by omega)) (U 1 ww)
      have m := law'.1 (by simpa only [show y+(j-1)+1=y+j by omega,Nat.add_zero] using miss)
      intro p hp; simp [pins,rim] at hp; rcases hp with rfl|rfl|rfl <;> dsimp only
      · exact (show a+1=y+(j-1) by omega) ▸ B ▸ U 0 (by omega)
      · exact A ▸ B ▸ (by simpa only [candidates,ite_true,Nat.add_zero,show y+(j-1)+1=y+j by omega] using m)
      · simpa only [show a+1=y+(j-1) by omega,show b+3=x+1 by omega] using U 1 ww
    · have L := wordAt H acy score hk (by omega : 4≤y+(j-1)) (by omega : 4≤x+(i-1)) (by omega) (by omega)
      have law' := L (U (i-1) (by omega)) (by simpa only [show x+(i-1)+1=x+i by omega] using U i iw)
      have m := law'.2 (by simpa only [show y+(j-1)+1=y+j by omega] using west (i-1) (by omega))
        (by simpa only [show y+(j-1)+1=y+j by omega,show x+(i-1)+1=x+i by omega] using miss)
      intro p hp; simp [pins,rim,z] at hp; rcases hp with rfl|rfl|rfl|rfl <;> dsimp only
      · exact (show a+1=y+(j-1) by omega) ▸ B ▸ U i iw
      · exact A ▸ B ▸ (by simpa only [candidates,Bool.false_eq_true,ite_false,
          show y+(j-1)+1=y+j by omega,show x+(i-1)+1=x+i by omega] using m)
      · simpa only [show a+1=y+(j-1) by omega,show b+1=x+(i-1) by omega] using U (i-1) (by omega)
      · simpa only [A,show b+1=x+(i-1) by omega] using west (i-1) (by omega)
  have z := readout Q price (a:=a) (b:=b) (by dsimp [a]; omega) (by dsimp [b]; omega) (pins rim)
    (gate north) P (by
      intro r _ c _; unfold gate; by_cases e : r=5 ∧ c=5
      · obtain ⟨rfl,rfl⟩ := e
        simp [north,headDir,show 2+3*a+5=1+3*(y+j) by omega,show 2+3*b+5=1+3*(x+i) by omega]
      · simp; omega) 6 (by decide) 6 (by decide)
  have out := List.contains_iff_mem.mp (List.all_eq_true.mp (exitCheck rim north) _ z)
  simpa only [center,Rooted.tile,show 1+3*a+6=1+3*(y+j) by omega,show 1+3*b+6=1+3*(x+i) by omega,
    show 2+3*a+6=2+3*(y+j) by omega,show 2+3*b+6=2+3*(x+i) by omega] using out

theorem no_inner_north {u F v} (Q : Flow (n:=N u) F) {r c : Nat}
    (rr : r+4≤11+14*u) (cc : c+4≤11+14*u)
    (exit : (tile' F v r c,center Q v r c)∈exits false (headDir Q v r c==3)) :
    ¬RootLine F v c r := by
  intro line
  have north : headDir Q v r c=3 := by
    simpa only [headDir,dir,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using
      root_tip F v Q r c (by dsimp [N]; omega) (by dsimp [N]; omega) line
  simp [north,exits] at exit

private def sourcePins (west : Bool) : List Pin :=
  [(1,1,if west then [128,192] else [292]),(1,2,if west then [8,9] else [36]),
   (1,3,if west then [72,73] else [128]),(2,1,[288,292]),(2,2,[2]),(2,3,[72,73])]
private def tags (west : Bool) (r c : Nat) : List Nat :=
  if (r,c)=(2,5) then (if west then [3] else [2]) else
  if (r,c)=(3,6) then (if west then [2] else [0]) else
  if (r,c)=(5,5) then (if west then [0] else [2]) else
  if (r,c)=(5,8) then (if west then [1,3] else [1]) else [0,1,2,3]
private theorem sourceCheck : ∀ west : Bool, ∀ pos∈([(2,5),(3,6),(5,5),(5,8)] : List (Nat×Nat)),
    (atRC (prune 15 10 (board (sourcePins west) (fun _ _ _ => true))) pos.1 pos.2).all
      (fun z => (tags west pos.1 pos.2).contains z.2) := by native_decide

def SourceEdges {u F} (Q : Flow (n:=N u) F) (v : View) (r c : Nat) : Prop :=
  let west := [8,9].contains (tile' F v r c)
  headDir Q v r c∈tags west 2 5 ∧ center Q v r c∈tags west 3 6 ∧
    headDir Q v (r+1) c∈tags west 5 5 ∧ headDir Q v (r+1) (c+1)∈tags west 5 8

set_option maxHeartbeats 1000000 in
theorem source_edges {u F v} (Q : Flow (n:=N u) F) (price : Prices F v) {r c : Nat}
    (rl : 4≤r) (cl : 5≤c) (rh : r+8≤11+14*u) (ch : c+7≤11+14*u)
    (src : TwoAncestry.LiveSource (tile' F v r (c-1)) (tile' F v r c) (tile' F v r (c+1)))
    (run : TwoAncestry.Run (tile' F v (r+1) (c-1)) (tile' F v (r+1) c) (tile' F v (r+1) (c+1))) :
    SourceEdges Q v r c := by
  let a := r-1; let b := c-2
  let west := [8,9].contains (tile' F v r c)
  have P : ∀ p∈sourcePins west, tile' F v (a+p.1) (b+p.2.1)∈p.2.2 := by
    obtain ⟨L,M,R⟩ := run
    have aux {l m n : Nat} (s : TwoAncestry.LiveSource l m n) :
        let w := [8,9].contains m
        l∈(if w then [128,192] else [292]) ∧ m∈(if w then [8,9] else [36]) ∧
        n∈(if w then [72,73] else [128]) := by
      rcases s with ⟨l',rfl|rfl,n'⟩|⟨rfl,rfl,rfl⟩ <;> simp_all
    obtain ⟨l,m,n⟩ := aux src
    intro p hp; simp only [sourcePins,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;>
      simp only [show a+1=r by dsimp [a]; omega,show a+2=r+1 by dsimp [a]; omega,
        show b+1=c-1 by dsimp [b]; omega,show b+2=c by dsimp [b]; omega,show b+3=c+1 by dsimp [b]; omega]
    · exact l
    · exact m
    · exact n
    · simpa using L
    · simpa using M
    · simpa using R
  have live := readout Q price (a:=a) (b:=b) (by dsimp [a]; omega) (by dsimp [b]; omega)
    _ (fun _ _ _ => true) P (fun _ _ _ _ => rfl)
  have at' (i j : Nat) (pos : (i,j)∈([(2,5),(3,6),(5,5),(5,8)] : List (Nat×Nat))) (hi : i<15) (hj : j<15) :=
    List.contains_iff_mem.mp (List.all_eq_true.mp (sourceCheck west (i,j) pos) _ (live i hi j hj))
  have cast (i j R C : Nat) (er : 2+3*a+i=R) (ec : 2+3*b+j=C)
      (pos : (i,j)∈([(2,5),(3,6),(5,5),(5,8)] : List (Nat×Nat))) (hi : i<15) (hj : j<15) :
      dir Q v R C∈tags west i j := by
    subst R; subst C; exact at' i j pos hi hj
  refine ⟨cast 2 5 _ _ ?_ ?_ (by decide) (by decide) (by decide),
    cast 3 6 _ _ ?_ ?_ (by decide) (by decide) (by decide),
    cast 5 5 _ _ ?_ ?_ (by decide) (by decide) (by decide),
    cast 5 8 _ _ ?_ ?_ (by decide) (by decide) (by decide)⟩ <;> dsimp [a,b] <;> omega

theorem owned_history {u F v x R} (Q : Flow (n:=N u) F) (price : Prices F v)
    (xl : 7≤x) (xh : x+7≤11+14*u) (rh : R+8≤11+14*u) (h : TwoAncestry.History F v x R) :
    TwoAncestry.History F v x R (fun r => SourceEdges Q v r (x-2)) := by
  obtain ⟨s,b,h,sl,sb,bh,lt,src,run,two,lower,right,strip,_⟩ := h
  refine ⟨s,b,h,sl,sb,bh,lt,src,run,two,lower,right,strip,?_⟩
  apply source_edges Q price (by omega) (by omega) (by omega) (by omega)
  · simpa only [show x-2-1=x-3 by omega,show x-2+1=x-1 by omega] using src
  · simpa only [show b-1+1=b by omega,show x-2-1=x-3 by omega,show x-2+1=x-1 by omega] using run b le_rfl bh

private def westPins (w : Nat) : List Pin :=
  [(1,1,[w]),(1,2,[128]),(1,3,[72,73]),(2,1,[w]),(2,2,[8]),(2,3,[9,73])]
private theorem westCheck : ∀ w∈[48,56], ∀ p∈([(5,5),(6,3),(6,4),(6,5),(6,6)] : List (Nat×Nat)),
    (atRC (prune 15 10 (board (westPins w) (fun _ _ _ => true))) p.1 p.2).all
      (fun z => z.2==(if p.1=5 then 1 else 2)) := by native_decide

/-- Directions 1 and 2 are south and west in the *same* physical view. -/
def WestExit {u F} (Q : Flow (n:=N u) F) (v : View) (r c : Nat) : Prop :=
  headDir Q v r c=1 ∧ ∀ k<4, dir Q v (2+3*r) (2+3*c-k)=2

theorem west_owners {u F v r c} (Q : Flow (n:=N u) F) (price : Prices F v)
    (rl : 4≤r) (cl : 5≤c) (rh : r+8≤11+14*u) (ch : c+7≤11+14*u)
    (eight : tile' F v (r+1) c=8) (upper : tile' F v r c=128)
    (west : tile' F v r (c-1)=48 ∨ tile' F v r (c-1)=56) (same : tile' F v (r+1) (c-1)=tile' F v r (c-1))
    (ne : tile' F v r (c+1)=72 ∨ tile' F v r (c+1)=73) (se : tile' F v (r+1) (c+1)=9 ∨ tile' F v (r+1) (c+1)=73) :
    WestExit Q v (r+1) c := by
  let a := r-1; let b := c-2; let w := tile' F v r (c-1)
  have P : ∀ p∈westPins w, tile' F v (a+p.1) (b+p.2.1)∈p.2.2 := by
    intro p hp; simp only [westPins,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;>
      simp only [show a+1=r by dsimp [a]; omega,show a+2=r+1 by dsimp [a]; omega,
        show b+1=c-1 by dsimp [b]; omega,show b+2=c by dsimp [b]; omega,show b+3=c+1 by dsimp [b]; omega,
        List.mem_cons,List.not_mem_nil,or_false]
    · rfl
    · exact upper
    · exact ne
    · exact same
    · exact eight
    · exact se
  have live := readout Q price (a:=a) (b:=b) (by dsimp [a]; omega) (by dsimp [b]; omega)
    _ (fun _ _ _ => true) P (fun _ _ _ _ => rfl)
  have hit (i j : Nat) (p : (i,j)∈([(5,5),(6,3),(6,4),(6,5),(6,6)] : List (Nat×Nat))) (hi : i<15) (hj : j<15) :
      dir Q v (2+3*a+i) (2+3*b+j)=(if i=5 then 1 else 2) :=
    beq_iff_eq.mp (List.all_eq_true.mp (westCheck w (by simpa [w] using west) (i,j) p) _ (live _ hi _ hj))
  constructor
  · simpa only [headDir,ite_true,show 2+3*a+5=1+3*(r+1) by dsimp [a]; omega,
      show 2+3*b+5=1+3*c by dsimp [b]; omega] using hit 5 5 (by decide) (by decide) (by decide)
  · intro k h; have idx : (6,6-k)∈([(5,5),(6,3),(6,4),(6,5),(6,6)] : List (Nat×Nat)) := by
      interval_cases k <;> decide
    simpa only [if_neg (show (6:Nat)≠5 by decide),show 2+3*a+6=2+3*(r+1) by dsimp [a]; omega,show 2+3*b+(6-k)=2+3*c-k by dsimp [b]; omega]
      using hit 6 (6-k) idx (by omega) (by omega)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
