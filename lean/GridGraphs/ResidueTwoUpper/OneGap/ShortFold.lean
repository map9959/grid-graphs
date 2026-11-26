import GridGraphs.ResidueTwoUpper.OneGap.ShortPhysical

/-! Keep the short isolate fixed and insert only strictly east of it.
Widths through 203 use their actual chart. From side 245 on, both
coordinates use a single three-site loop; no physical masks are
identified across different visits to that loop. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7 ResidueZero Stencil FanSlab

def baseU (u : Nat) := min u 5
def extra (u : Nat) := 42*(u-baseU u)
def foldAt (p d i : Nat) := if i<p then i else if i<p+3+d then p+(i-p)%3 else i-d
def folded (u : Nat) (far : Bool) (p i : Nat) :=
  let s := 33+42*u
  let b := 33+42*baseU u
  if far then b-1-foldAt p (extra u) (s-1-i) else foldAt p (extra u) i

private theorem sizes (u : Nat) : 33+42*u=33+42*baseU u+extra u ∧ extra u%3=0 ∧
    (extra u=0 ∨ baseU u=5) := by simp only [extra,baseU]; omega

private theorem room {u p i} (hi : i<33+42*u) (hp : p=12 ∨ p=180) :
    foldAt p (extra u) i<33+42*baseU u := by
  have := sizes u
  unfold foldAt; split_ifs <;> omega

def axisFold (u : Nat) (w : View) (r c : Nat) : Nat × Nat :=
  (folded u w.rowFar (if w.swap then 180 else 12) r,
   folded u w.colFar (if w.swap then 12 else 180) c)

theorem inside_fold {u r c} (w : View) (hr : r<33+42*u) (hc : c<33+42*u) :
    (axisFold u w r c).1<33+42*baseU u ∧ (axisFold u w r c).2<33+42*baseU u := by
  have each (i : Nat) (hi : i<33+42*u) (p : Nat) (hp : p=12 ∨ p=180) (f : Bool) :
      folded u f p i<33+42*baseU u := by
    cases f <;> simp only [folded,Bool.false_eq_true,if_false,if_true]
    · exact room hi hp
    · omega
  exact ⟨each _ hr _ (by split <;> simp) _,each _ hc _ (by split <;> simp) _⟩

theorem chart_fold {u r c} (w : View) (hr : r<33+42*u) (hc : c<33+42*u) :
    let (a,b) := axisFold u w r c
    let t := unview w (33+42*u) r c
    unview w (33+42*baseU u) a b=(foldAt 12 (extra u) t.1,foldAt 180 (extra u) t.2) := by
  have E (p i : Nat) (hi : i<33+42*u) (hp : p=12 ∨ p=180) :
      33+42*baseU u-1-(33+42*baseU u-1-foldAt p (extra u) (33+42*u-1-i))=
        foldAt p (extra u) (33+42*u-1-i) := by
    have := room (u:=u) (i:=33+42*u-1-i) (by omega) hp; omega
  cases w with | mk f g k => cases f <;> cases g <;> cases k <;>
    simp only [axisFold,unview,folded,Bool.false_eq_true,if_false,if_true,
      E _ _ hr (Or.inl rfl),E _ _ hr (Or.inr rfl),E _ _ hc (Or.inl rfl),E _ _ hc (Or.inr rfl)]

private theorem threshold (u i q : Nat) (short : q<57) :
    (foldAt 180 (extra u) i)%3=i%3 ∧
    (foldAt 180 (extra u) i=1+3*q ↔ i=1+3*q) ∧ (foldAt 180 (extra u) i<1+3*q ↔ i<1+3*q) := by
  have := sizes u; unfold foldAt; split_ifs <;> omega

theorem seed_fold (u q : Nat) (w : View) (r c m : Nat) (hr : r<33+42*u) (hc : c<33+42*u)
    (short : q<57) :
    let t := axisFold u w r c
    seedOK (35+42*u) q w r c m=seedOK (35+42*baseU u) q w t.1 t.2 m := by
  have sid (b : Nat) : 35+42*b-2=33+42*b := by omega
  have y (i : Nat) : foldAt 12 (extra u) i=1 ↔ i=1 := by unfold foldAt; split_ifs <;> omega
  unfold seedOK; simp only [sid,chart_fold w hr hc,y,(threshold u _ q short).1,
    (threshold u _ q short).2.1,(threshold u _ q short).2.2]

private theorem reduce_axis {u i p} (hi : i<33+42*u) (hp : p=12 ∨ p=180) (f : Bool) (t : Nat) (ht : t≤1) :
    let a := folded u f p i
    rep (21+2*(t:Int)) (4+14*(u:Int)) (i+t:Nat)=
      rep (21+2*(t:Int)) (4+14*(baseU u:Int)) (a+t:Nat) := by
  have := sizes u
  dsimp only
  cases f <;> simp only [folded,Bool.false_eq_true,if_false,if_true,foldAt,rep,Nat.cast_add] <;>
    split_ifs <;> omega

/-- Both local price lookups survive the same geometric folding as the
seed. State labels (mask, mark, neighbors, direction) are untouched. -/
theorem price_fold {u r c} (w : View) (hr : r<33+42*u) (hc : c<33+42*u) (m f nb o : Nat) :
    let t := axisFold u w r c
    twoOrbitPatch (35+42*(u:Int)) (r,c) m=twoOrbitPatch (35+42*(baseU u:Int)) (t.1,t.2) m ∧
    twoOrbitStar (35+42*(u:Int)) (center r c) f nb o=twoOrbitStar (35+42*(baseU u:Int)) (center t.1 t.2) f nb o := by
  let t := axisFold u w r c
  have R := reduce_axis hr (by split <;> simp : (if w.swap then 180 else 12)=12 ∨ _=180) w.rowFar
  have C := reduce_axis hc (by split <;> simp : (if w.swap then 12 else 180)=12 ∨ _=180) w.colFar
  have p : representative 21 (4+14*(u:Int)) ((r:Int),(c:Int))=
      representative 21 (4+14*(baseU u:Int)) ((t.1:Int),(t.2:Int)) := by
    exact Prod.ext (by simpa [representative,t,axisFold] using R 0 (by decide))
      (by simpa [representative,t,axisFold] using C 0 (by decide))
  have s : representative 23 (4+14*(u:Int)) (center r c)=
      representative 23 (4+14*(baseU u:Int)) (center t.1 t.2) := by
    exact Prod.ext (by simpa [center,representative,t,axisFold] using R 1 (by decide))
      (by simpa [center,representative,t,axisFold] using C 1 (by decide))
  have n (v : Nat) : 35+42*(v:Int)=23+3*(4+14*(v:Int)) := by ring
  have a (v : Nat) : 35+42*(v:Int)-2=21+3*(4+14*(v:Int)) := by ring
  constructor
  · simp only [twoOrbitPatch,a,patchLocation_transport (b:=21) (by decide) (j:=4+14*(u:Int)) (by positivity),
      patchLocation_transport (b:=21) (by decide) (j:=4+14*(baseU u:Int)) (by positivity),p,t]
  · simp only [twoOrbitStar,n,starLocation_transport (b:=23) (by decide) (j:=4+14*(u:Int)) (by positivity),
      starLocation_transport (b:=23) (by decide) (j:=4+14*(baseU u:Int)) (by positivity),s,t]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
