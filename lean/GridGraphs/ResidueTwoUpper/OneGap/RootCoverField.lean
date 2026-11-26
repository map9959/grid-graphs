import GridGraphs.ResidueTwoUpper.OneGap.RootedSouthContact

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSlab BoundarySix.Connected

def descent (m n : Nat) : Bool := bit m 3==1 && (bit m 6==1 || bit n 0==1)
def crossbar (m n : Nat) : Bool := bit m 1==1 && bit n 0==1
def labelled (m : Nat) (b : Bool) := 2*m+b.toNat

/-- Label one word using a certified path to the north foot, which
can be forgotten but never spontaneously generated in a lower row. -/
def decorate (top south : Bool) (w : Word) (x y : Bool) : Option Word :=
  let (a,b,c,d) := w
  let z := x && descent a c
  let t := y && descent b d
  if (top && !(x && y && a==73 && b==73)) ||
      (x && y && crossbar a b) || (z && t && crossbar c d) ||
      (south && ((z && bit c 3==1) || (t && bit d 3==1))) then none
  else some (labelled a x,labelled b y,labelled c z,labelled d t)

def labelBank (a b : Nat) (top south : Bool) : List Word :=
  (bankWords a b).flatMap fun w => ([false,true].flatMap fun x =>
    [false,true].filterMap fun y => decorate top south w x y)

def flags (t : Tiles) : Nat → Nat → Bool
  | 0,_ => true
  | r+1,c => flags t r c && descent (t r c) (t (r+1) c)

def field (t : Tiles) : Tiles := fun r c => labelled (t r c) (flags t r c)

theorem label_mem (t : Tiles) (r c a b : Nat) (top south : Bool)
    (adm : word t r c∈bankWords a b)
    (init : top=true → flags t r c=true ∧ flags t r (c+1)=true ∧ t r c=73 ∧ t r (c+1)=73)
    (noBar : ∀ j, r≤j → j≤r+1 → flags t j c=true → flags t j (c+1)=true →
      crossbar (t j c) (t j (c+1))=false)
    (noRim : south=true → ∀ i, c ≤ i → i ≤ c+1 → flags t (r+1) i=true → bit (t (r+1) i) 3≠1) :
    word (field t) r c ∈ labelBank a b top south := by
  apply List.mem_flatMap.mpr
  refine ⟨_,adm,List.mem_flatMap.mpr ⟨flags t r c,by cases flags t r c <;> decide,
    List.mem_filterMap.mpr ⟨flags t r (c+1),by cases flags t r (c+1) <;> decide,?_⟩⟩⟩
  unfold decorate word field
  dsimp only
  rw [if_neg]
  · rfl
  · simp only [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq]
    rintro (((⟨on,wrong⟩|⟨⟨x,y⟩,bar⟩)|⟨⟨z,t'⟩,bar⟩)|⟨on,side⟩)
    · obtain ⟨x,y,m,n⟩ := init on
      simp [x,y,m,n] at wrong
    · rw [noBar r le_rfl (by omega) x y] at bar; contradiction
    · rw [noBar (r+1) (by omega) le_rfl (Bool.and_eq_true_iff.mpr z)
        (Bool.and_eq_true_iff.mpr t')] at bar; contradiction
    · rcases side with ⟨z,bad⟩|⟨z,bad⟩
      · exact noRim on c le_rfl (by omega) (Bool.and_eq_true_iff.mpr z) bad
      · exact noRim on (c+1) (by omega) le_rfl (Bool.and_eq_true_iff.mpr z) bad

/-- A sound field of compatible labels on the *whole* scored suffix,
not only the terminal cap or one movement window. -/
theorem physical_label_bank_from_second {u F v q} (strict : Bool) (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (y f : Nat) (yl : 4≤y) (fl : 4≤f) (fh : f<11+14*u)
    (seed : ∀ i, f ≤ i → i < 11+14*u → (f < i → tile F v y i=73) ∧ RootLine F v i y) :
    let k := 11+14*u
    let t := fun r c => tile F v (y+r) (f+c)
    ∀ r c : Nat, r+2 ≤ k-y → c+2 ≤ k-f →
      word (field t) r c ∈ labelBank (endTag (k-y) r) (endTag (k-f) c)
        ((r==0 && t 0 c==73) && strict) (r+2==k-y) := by
  intro k t
  have rooted (r c : Nat) (cl : c<k-f) (hit : flags t r c=true) : RootLine F v (f+c) (y+r) := by
    induction r with
    | zero => exact (seed _ (by omega) (by dsimp [k] at *; omega)).2
    | succ r ih =>
      obtain ⟨old,m⟩ := Bool.and_eq_true_iff.mp hit
      simp only [descent,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at m
      exact extend_line (ih old) m.1 m.2
  intro r c rl cl
  apply label_mem
  · have mem := board_word H acy score hk (y:=y+r) (x:=f+c) (by omega) (by omega)
      (by dsimp [k] at *; omega) (by dsimp [k] at *; omega)
    have tg (a b : Nat) (ha : a≤k) : endTag k (a+b)=endTag (k-a) b := by
      unfold endTag; split_ifs <;> omega
    simpa only [word,t,Nat.add_assoc,tg y r (by dsimp [k] at *; omega),tg f c (by dsimp [k]; omega),k]
      using mem
  · intro on
    obtain ⟨rr,head⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp on).1
    have z : r=0 := beq_iff_eq.mp rr
    subst r
    exact ⟨rfl,rfl,beq_iff_eq.mp head,
      (seed _ (by omega) (by dsimp [k] at *; omega)).1 (by omega)⟩
  · intro j jl jh n₁ n₂
    apply Bool.eq_false_iff.mpr
    intro bar
    simp only [crossbar,Bool.and_eq_true,beq_iff_eq] at bar
    exact no_crossbar (y:=y+j) (t:=f+c) acy one (by dsimp [k] at *; omega)
      (by dsimp [k] at *; omega) (rooted _ _ (by omega) n₁)
      (by simpa only [Nat.add_assoc] using rooted _ _ (by omega) n₂) bar.1
      (by simpa only [Nat.add_assoc] using bar.2)
  · intro on i il ih hit mid
    have z := beq_iff_eq.mp on
    have row : y+(r+1)=10+14*u := by dsimp [k] at *; omega
    have line := rooted _ _ (by omega) hit
    change bit (tile F v (y+(r+1)) (f+i)) 3=1 at mid
    rw [row] at mid line
    exact no_south_middle H acy one (by omega) (by dsimp [k] at *; omega) line mid

theorem physical_label_bank {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (y f : Nat) (yl : 4≤y) (fl : 4≤f) (fh : f<11+14*u)
    (seed : ∀ i, f ≤ i → i < 11+14*u → tile F v y i=73 ∧ RootLine F v i y) :
    let k := 11+14*u
    let t := fun r c => tile F v (y+r) (f+c)
    ∀ r c : Nat, r+2 ≤ k-y → c+2 ≤ k-f →
      word (field t) r c ∈ labelBank (endTag (k-y) r) (endTag (k-f) c)
        (r==0) (r+2==k-y) := by
  intro k t r c hr hc
  have m := physical_label_bank_from_second true H acy one score hk y f yl fl fh
    (fun i lo hi => ⟨fun _ => (seed i lo hi).1,(seed i lo hi).2⟩) r c hr hc
  simpa only [Nat.add_zero,(seed (f+c) (by omega) (by dsimp [k] at *; omega)).1,
    beq_self_eq_true,Bool.and_true] using m

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
