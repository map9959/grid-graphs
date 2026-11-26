import GridGraphs.NoPitch.TailRows.LetterGeometry
import GridGraphs.NoPitch.TailCoverageGeometry

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget Finset TailCoverage GridGraphs.NoPitch.Dual
variable {k : Nat}

def admissible (x : Site k) (bits : Fin 4 → Bool) (f : Bool) (o : Option (Fin 4)) :=
  (∀ d, bits d → (probe x d.val).isSome) ∧ (∀ d, bits d → !bits (d+1)) ∧
    ∀ d∈o, (probe x d.val).isSome ∧ (f || bits d)
instance (x : Site k) (bits f o) : Decidable (admissible x bits f o) := by unfold admissible; infer_instance

theorem physical_admissible (F : Finset (Site k)) (acy : (G F).IsAcyclic) (x : Site k) :
    admissible x (bitsAt F x) (decide (x∈F)) (out F x) := by
  have bound (d : Fin 4) (h : bitsAt F x d) : (probe x d.val).isSome := by
    cases p : probe x d.val <;> simp_all [bitsAt]
  refine ⟨bound,?_,?_⟩
  · intro d hd
    rw [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr; intro he
    obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp (bound d hd)
    obtain ⟨q,hq⟩ := Option.isSome_iff_exists.mp (bound (d+1) he)
    have c (x y : Site k) (d : Fin 4) (h : probe x d.val=some y) :
        (y.1.val:Int)=x.1.val+(if d.val=1 then 1 else if d.val=3 then -1 else 0) ∧
        (y.2.val:Int)=x.2.val+(if d.val=0 then 1 else if d.val=2 then -1 else 0) := by
      unfold probe at h
      simp only [Option.dite_none_right_eq_some,Option.some.injEq] at h
      obtain ⟨hz,rfl⟩ := h; simp only [Int.toNat_of_nonneg hz.1,Int.toNat_of_nonneg hz.2.1,and_self]
    have a := c _ _ _ hp; have b := c _ _ _ hq
    simp only [bitsAt,hp,hq,Option.any_some,decide_eq_true_eq] at hd he
    apply CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy p q hd he <;>
      fin_cases d <;> norm_num [Fin.add_def] at a b ⊢ <;> omega
  · intro d hd
    have ne : parent F x≠x := fun h => by rw [(out_none F x).mpr h] at hd; cases hd
    have e := (CapBill.parent_step _ (sectionRoot F) (mt (CapBill.parent_fix _ _ x).mpr ne)).1.2
    change x∈F ∨ parent F x∈F at e
    exact ⟨out_inside F x d hd,by simpa [bitsAt,out_points F x d hd] using e⟩

def sKey (x : Site k) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) :=
  8*starCode (N k) x.1.val x.2.val (sampled x bits) o+f.toNat
theorem physical_sKey (F : Finset (Site k)) (o : Site k → Option (Fin 4)) (x : Site k) :
    sKey x (decide (x∈F)) (bitsAt F x) (o x)=Keys.star F o x := by
  have eq : starCode (N k) x.1.val x.2.val (sampled x (bitsAt F x)) (o x)=
      starCode (N k) x.1.val x.2.val (neighbor F x) (o x) := by
    unfold starCode; apply congrArg minimum; funext g
    have h (d : Nat) := sampled_bits F x (⟨direction (invers g) d,by unfold direction; omega⟩ : Fin 4)
    simp only [h]
  unfold sKey Keys.star; rw [eq]

private theorem inAxis {l m i j} (h : Axis l m i j) (u : Int) (hu : -1≤u ∧ u≤1) :
    (0≤(i:Int)+u ∧ ((i:Int)+u).toNat < l+1) ↔ (0≤(j:Int)+u ∧ ((j:Int)+u).toNat < m+1) := by
  rcases h with ⟨_,_,_,lo,hi⟩; unfold Sat at *; omega

theorem one_rep (hk : 19≤k) (x : Site (k+2)) :
    ∃ y : Site k, (∀ d, (probe x d).isSome=(probe y d).isSome) ∧
      (∀ g, fine (N (k+2)) 8 (turn g x).1.val (turn g x).2.val=
        fine (N k) 8 (turn g y).1.val (turn g y).2.val) ∧
      (isJoint x ↔ isJoint y) := by
  have w : 3*(k+2)=3*k+6 := by omega
  have hi := x.1.isLt; have hj := x.2.isLt; unfold N at hi hj
  obtain ⟨a,b,m⟩ := representative (m:=3*k) (by omega) (i:=x.1.val) (j:=x.2.val) (by omega) (by omega)
  let y : Site k := (⟨a,by have := m.row.dst; unfold N; omega⟩,⟨b,by have := m.col.dst; unfold N; omega⟩)
  have hm : Match (3*(k+2)) (3*k) x.1.val x.2.val y.1.val y.2.val := w ▸ m
  refine ⟨y,?_,?_,by simp only [isJoint,hm.row.residue,hm.col.residue]⟩
  · intro d
    let u : Int := if d=1 then 1 else if d=3 then -1 else 0
    let v : Int := if d=0 then 1 else if d=2 then -1 else 0
    have r := inAxis hm.row u (by dsimp [u]; split_ifs <;> decide)
    have c := inAxis hm.col v (by dsimp [v]; split_ifs <;> decide)
    unfold probe; simp only [apply_dite Option.isSome,Option.isSome_some,Option.isSome_none,dite_eq_ite]
    change (if 0≤(x.1.val:Int)+u ∧ 0≤(x.2.val:Int)+v ∧ ((x.1.val:Int)+u).toNat<N (k+2) ∧
      ((x.2.val:Int)+v).toNat<N (k+2) then true else false)=
      (if 0≤(y.1.val:Int)+u ∧ 0≤(y.2.val:Int)+v ∧ ((y.1.val:Int)+u).toNat<N k ∧
        ((y.2.val:Int)+v).toNat<N k then true else false)
    simp only [N]; split <;> split <;> first | rfl | exfalso; tauto
  · intro g
    have vals {n} (x : Site n) : ((turn g x).1.val,(turn g x).2.val)=transform g (N n) x.1.val x.2.val := by
      exact turn_values g x
    rw [show (turn g x).1.val=_ from congrArg Prod.fst (vals x),
      show (turn g x).2.val=_ from congrArg Prod.snd (vals x),
      show (turn g y).1.val=_ from congrArg Prod.fst (vals y),show (turn g y).2.val=_ from congrArg Prod.snd (vals y)]
    exact hm.view w g

abbrev TypeAt (k : Nat) (x : Site k) :=
  (fun d : Nat => (probe x d).isSome,fun g : Fin 8 => fine (N k) 8 (turn g x).1.val (turn g x).2.val,decide (isJoint x))

theorem type_rep (hk : 19≤k) (x : Site k) :
    ∃ y : Site (if k%2=1 then 19 else 20), TypeAt k x=TypeAt _ y := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k≤20
    · interval_cases k <;> exact ⟨x,rfl⟩
    · have eq : k-2+2=k := by omega
      generalize hb : k-2=b at eq
      subst k
      obtain ⟨y,p,v,j⟩ := one_rep (k:=b) (by omega) x
      have z : TypeAt _ x=TypeAt _ y := Prod.ext (funext p) (Prod.ext (funext v) (by simp only [j]))
      obtain ⟨q,hq⟩ := ih b (by omega) (by omega) y
      have par : (b+2)%2=b%2 := by omega
      have baseEq : (if (b+2)%2=1 then 19 else 20 : Nat)=(if b%2=1 then 19 else 20) := by rw [par]
      rw [baseEq]; exact ⟨q,z.trans hq⟩

theorem type_key {b} {x : Site k} {y : Site b} (h : TypeAt _ x=TypeAt _ y)
    (f bits o) : sKey x f bits o=sKey y f bits o := by
  have probeEq := congrArg Prod.fst h
  have fineEq := congrArg (fun t => t.2.1) h
  have p (d : Nat) : (probe x d).isSome=(probe y d).isSome := congrFun probeEq d
  have v (g : Fin 8) : fine (N k) 8 (turn g x).1.val (turn g x).2.val=
      fine (N b) 8 (turn g y).1.val (turn g y).2.val := congrFun fineEq g
  have raw {n} (g : Fin 8) (x : Site n) :
      fine (N n) 8 (transform g (N n) x.1.val x.2.val).1 (transform g (N n) x.1.val x.2.val).2 =
        fine (N n) 8 (turn g x).1.val (turn g x).2.val := by rw [←turn_values g x]
  have sc : starCode (N k) x.1.val x.2.val (sampled x bits) o =
      starCode (N b) y.1.val y.2.val (sampled y bits) o := by
    unfold starCode; apply congrArg minimum; funext g
    simp only [raw,v,sampled,p]
  unfold sKey; rw [sc]

theorem type_adm {b} {x : Site k} {y : Site b} (h : TypeAt _ x=TypeAt _ y)
    {f bits o} (a : admissible x bits f o) : admissible y bits f o := by
  have p (d : Nat) : (probe x d).isSome=(probe y d).isSome := congrFun (congrArg Prod.fst h) d
  exact ⟨fun d hd => p _ ▸ a.1 d hd,a.2.1,fun d hd => ⟨p _ ▸ (a.2.2 d hd).1,(a.2.2 d hd).2⟩⟩

private theorem joint_turn (g : Fin 8) (x : Site k) : isJoint (turn g x) ↔ isJoint x := by
  have a := x.1.isLt; have b := x.2.isLt; unfold N at a b
  have v := turn_values g x
  unfold isJoint
  rw [show (turn g x).1.val=_ from congrArg Prod.fst v,show (turn g x).2.val=_ from congrArg Prod.snd v]
  fin_cases g <;> simp [transform,N] <;> omega

theorem type_view {b} {x : Site k} {y : Site b} (h : TypeAt _ x=TypeAt _ y)
    {V : Type} [Zero V] (A : Nat → Nat → Letter → V) (g f bits) :
    atView A x g f bits=atView A y g f bits := by
  have v : fine (N k) 8 (turn g x).1.val (turn g x).2.val=
      fine (N b) 8 (turn g y).1.val (turn g y).2.val := congrFun (congrArg (fun t => t.2.1) h) g
  simp only [fine,List.cons.injEq] at v
  have joint : isJoint x ↔ isJoint y := by
    have e : decide (isJoint x)=decide (isJoint y) := congrArg (fun t => t.2.2) h
    exact decide_eq_decide.mp e
  change (if isJoint (turn g x) then _ else _)=(if isJoint (turn g y) then _ else _)
  simp only [joint_turn,joint,v.1,v.2.1]

end GridGraphs.NoPitch.TailRows
