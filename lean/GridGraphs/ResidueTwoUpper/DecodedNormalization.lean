import GridGraphs.ResidueTwoUpper.Views

/-! The 37 normalization rows and the negative corner-sink row, in the
actual sparse chart order. Check coefficient semantics on every column,
then sum over the physical occurrences. -/
namespace GridGraphs.ResidueTwoUpper.DecodedNormalization
open Finset NoPitch.Dual NoPitch.Keys PhysicalCounts Views GridGraphs.ResidueTwoUpper.Star

def tag (i : Fin 38) : Nat := #[0,0,1,2,3,4,6,19,20,21,22,24,36,37,38,40,52,54,68,70,85,88,102,136,
  2,18,19,21,34,35,37,51,52,53,55,69,85,87][i.val]!
def dp (i : Fin 38) := if i.val<24 then 6 else 5
def pos (k : Nat) := if k%2=1 then k/1024 else k/200000
def contribution (i : Fin 38) (k : Nat) :=
  let p := pos k
  let n := units (dp i) (p/16) (p%16) (tag i)
  if decide (i.val<24) != (k%2==0) then 0 else
    if i.val=1 then (if k/2%5=0 then 4*n else 0) else n

def colCheck (D : Chart) := D.cols.all fun c => decide (∀ i : Fin 38,
  coeff i c.terms*(c.units:Int)=contribution i c.key)
theorem checked : colCheck periodThree := by native_decide

theorem min_view (f : Fin 8 → Nat) : ∃ g, minimum f=f g := by
  have go (l : List Nat) (a : Nat) : l.foldl min a ∈ a::l := by
    induction l generalizing a with
    | nil => simp
    | cons b l ih =>
      have h := ih (min a b)
      rcases List.mem_cons.mp h with h|h
      · rcases le_total a b with le|le <;> simp_all
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  rcases List.mem_cons.mp (go (List.ofFn f) (f 0)) with h|h
  · exact ⟨0,h⟩
  · obtain ⟨g,h⟩ := List.mem_ofFn.mp h
    exact ⟨g,h.symm⟩

private theorem digits {b : Dir → Nat} (h : ∀ d, b d<10) (g : Fin 8) (u : Nat) :
    let n := (List.finRange 4).foldl (fun z d => 10*z+b (Fin.ofNat 4 (direction (invers g) d))) u
    n/10000=u := by
  let v (j : Nat) := b (Fin.ofNat 4 (direction (invers g) j))
  change (10*(10*(10*(10*u+v 0)+v 1)+v 2)+v 3)/10000=u
  unfold v
  have hh (d : Nat) := h (Fin.ofNat 4 (direction (invers g) d))
  have := hh 0; have := hh 1; have := hh 2; have := hh 3
  omega

theorem star_pos {s i j} (f b o) :
    ∃ g, pos (key s i j f (letter s i j b) o)=fine s 6 (transform g s i j) := by
  obtain ⟨g,e⟩ := min_view (encoding s i j f (letter s i j b) o)
  refine ⟨g,?_⟩
  have dig (d : Dir) : letter s i j b d<10 := by unfold letter; split <;> cases b d <;> decide
  have code := digits dig g (2*fine s 6 (transform g s i j)+f.toNat)
  have arrow : ((o.map (fun d : Dir => (d.val : Nat))).map (fun d => direction g d+1)).getD 0 <5 := by
    cases o <;> simp [direction]; omega
  unfold pos key; rw [e]
  simp only [Nat.mul_mod_right,zero_ne_one,if_false]
  unfold encoding; dsimp only at code ⊢
  unfold Views.fine at code ⊢
  have hb : f.toNat<2 := by cases f <;> decide
  cases o <;> dsimp at code arrow ⊢ <;> omega

theorem patch_pos {s i j} (m : Fin 512) :
    ∃ g, pos (PatchColumns.key s i j m)=fine s 5 (transform g s i j) := by
  have bound : ∀ (m : Fin 512) (g : Fin 8), PatchColumns.rotate m g<512 := by native_decide
  obtain ⟨g,e⟩ := min_view (fun g => fine s 5 (transform g s i j)*512+PatchColumns.rotate m g)
  refine ⟨g,?_⟩
  change pos (2*minimum (fun g => Views.fine s 5 (transform g s i j)*512+PatchColumns.rotate m g)+1)=_
  rw [e]
  unfold pos
  have := bound m g
  split_ifs <;> omega

private theorem tag_lt (i : Fin 38) : tag i<256 := by revert i; decide

private theorem invariant {d t} (hd : d=5 ∨ d=6) (x : Site (2*d+8+3*t)) (k : Nat)
    (h : ∃ g, pos k=fine (2*d+8+3*t) d (transform g (2*d+8+3*t) x.1 x.2))
    (i : Fin 38) : units d (pos k/16) (pos k%16) (tag i)=
      units d (Location.axis (2*d+8+3*t) d x.1) (Location.axis (2*d+8+3*t) d x.2) (tag i) := by
  obtain ⟨g,h⟩ := h
  have bound (x : Fin (2*d+8+3*t)) : Location.axis (2*d+8+3*t) d x <2*d+3 := by
    have := x.isLt; unfold Location.axis; split_ifs <;> omega
  rw [h,fine_image x.1.isLt x.2.isLt]
  exact units_invariant hd (bound _) (bound _) g ⟨_,tag_lt i⟩

def tally {s} (d : Nat) (x : Site s) (z : Nat) := units d (Location.axis s d x.1) (Location.axis s d x.2) z

variable {t} (F : Finset (Site (N t))) (ac : (Forced F).IsAcyclic)

theorem decompose (i : Fin 38) (j : Fin periodThree.rows.size) (hi : j.val=i.val) :
    lhs periodThree (vector F ac) j =
    (∑ x : Site (N t), contribution i (starKey F ac x)) +
    ∑ x : Site (S t), contribution i (patchKey F x) := by
  simp only [lhs,vector,mul_add,sum_add_distrib]
  have col {k a} (e : locate periodThree (index periodThree) k=some a) :
      coeff j periodThree.cols[a].terms*(periodThree.cols[a].units:Int)=contribution i k := by
    have h := Array.all_eq_true_iff_forall_mem.mp checked _ (Array.getElem_mem a.isLt)
    rw [hi,←locate_key e]
    exact of_decide_eq_true h i
  apply congrArg₂ (·+·)
  · apply scatter_sum; intro x
    obtain ⟨a,e,_⟩ := star_entry F ac x
    exact ⟨a,e,col e⟩
  · apply scatter_sum; intro x
    obtain ⟨a,e⟩ := Option.isSome_iff_exists.mp (PatchColumns.physical_patch_found (t:=t)
      x.1.isLt x.2.isLt F ac)
    exact ⟨a,e,col e⟩

theorem key_even (x) : starKey F ac x%2=0 := by unfold starKey key; omega
theorem key_odd (x) : patchKey F x%2=1 := by unfold patchKey PatchColumns.key; omega

theorem star_units (x) (i : Fin 38) :
    units 6 (pos (starKey F ac x)/16) (pos (starKey F ac x)%16) (tag i)=tally 6 x (tag i) :=
  invariant (d:=6) (t:=t) (Or.inr rfl) x _ (star_pos ..) i
private theorem patch_units (x) (i : Fin 38) :
    units 5 (pos (patchKey F x)/16) (pos (patchKey F x)%16) (tag i)=tally 5 x (tag i) :=
  invariant (d:=5) (t:=t) (Or.inl rfl) x _ (patch_pos _) i

def mass (i : Fin 38) (t : Nat) := Normalization.axisMass (dp i) t (tag i/16) *
  Normalization.axisMass (dp i) t (tag i%16)

theorem normalized (i : Fin 38) (j : Fin periodThree.rows.size) (hi : j.val=i.val) (nc : i.val≠1) :
    lhs periodThree (vector F ac) j=8*mass i t := by
  rw [decompose F ac i j hi]
  let a : Fin 16 := ⟨tag i/16,by have := tag_lt i; omega⟩
  let b : Fin 16 := ⟨tag i%16,by omega⟩
  have z : a.val*16+b.val=tag i := by dsimp [a,b]; omega
  by_cases h : i.val<24
  · have total := sum_units (t:=t) (d:=6) (Or.inr rfl) a b
    rw [z] at total
    simp [contribution,key_even F ac,key_odd F,dp,h,nc,star_units,tally,mass] at *
    simpa [a,b,mul_assoc] using total
  · have total := sum_units (t:=t) (d:=5) (Or.inl rfl) a b
    rw [z] at total
    simp [contribution,key_even F ac,key_odd F,dp,h,nc,patch_units,tally,mass] at *
    simpa [a,b,mul_assoc] using total

end GridGraphs.ResidueTwoUpper.DecodedNormalization
