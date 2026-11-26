import GridGraphs.Constructions.ResidueTwo.LowerZipper

namespace GridGraphs.ResidueTwoLower

abbrev holeDual (n : Nat) (m : Mask) :=
  uuDualGraph (Finset.univ.filter (fun v : GridVertex n n => m v.1 v.2 = false))

private abbrev cell (n i j : Nat) (hi : i<n-1) (hj : j<n-1) : GridFace n n :=
  .cell ⟨i,hi⟩ ⟨j,hj⟩

private theorem north {n i j} (hi : i<n-1) (hj : j<n-1) (pos : 0 < i)
    {m : Mask} (a : m i j=false) (b : m i (j+1)=false) :
    (holeDual n m).Adj (cell n i j hi hj) (cell n (i-1) j (by omega) hj) := by
  let e : HorizontalGridEdge n n := ⟨⟨i,by omega⟩,⟨j,hj⟩⟩
  refine ⟨?_,Or.inl ⟨e,?_,?_,Or.inr ⟨?_,?_⟩⟩⟩
  · simp [cell,Fin.ext_iff]; omega
  · simpa [e,horizontalPrimalEndpoints] using a
  · simpa [e,horizontalPrimalEndpoints] using b
  · simp [cell,e,horizontalDualEndpoints,show i+1≠n by omega]
  · simp [cell,e,horizontalDualEndpoints,show i≠0 by omega]

private theorem east {n i j} (hi : i<n-1) (hj : j+1<n-1)
    {m : Mask} (a : m i (j+1)=false) (b : m (i+1) (j+1)=false) :
    (holeDual n m).Adj (cell n i j hi (by omega)) (cell n i (j+1) hi hj) := by
  let e : VerticalGridEdge n n := ⟨⟨i,hi⟩,⟨j+1,by omega⟩⟩
  refine ⟨?_,Or.inr ⟨e,?_,?_,Or.inl ⟨?_,?_⟩⟩⟩
  · simp [cell,Fin.ext_iff]
  · simpa [e,verticalPrimalEndpoints] using a
  · simpa [e,verticalPrimalEndpoints] using b
  · simp [cell,e,verticalDualEndpoints]
  · simp [cell,e,verticalDualEndpoints,show j+1+1≠n by omega]

/-- A local descent certificate. Step straight up, or take one step
along the row to reach a free vertical lane. -/
def climbs (n : Nat) (m : Mask) (i j : Nat) : Prop :=
  (m i j=false ∧ m i (j+1)=false) ∨
  (j+1<n-1 ∧ m i (j+1)=false ∧ m (i+1) (j+1)=false ∧ m i (j+2)=false) ∨
  (0<j ∧ m i j=false ∧ m (i+1) j=false ∧ m i (j-1)=false)

theorem climbs_route {n i j} {m : Mask} (hi : i<n-1) (hj : j<n-1) (pos : 0 < i)
    (h : climbs n m i j) :
    ∃ c : Fin (n-1), (holeDual n m).Reachable (cell n i j hi hj)
      (.cell ⟨i-1,by omega⟩ c) := by
  rcases h with ⟨a,b⟩ | ⟨hc,a,b,d⟩ | ⟨hc,a,b,d⟩
  · exact ⟨_,(north hi hj pos a b).reachable⟩
  · exact ⟨_,(east hi hc a b).reachable.trans (north hi hc pos a d).reachable⟩
  · have eq : j-1+1=j := by omega
    have e := east (m := m) (j := j-1) hi (by omega) (by simpa [eq] using a)
      (by simpa [eq] using b)
    have u := north (m := m) (j := j-1) hi (by omega) pos d (by simpa [eq] using a)
    exact ⟨_,by simpa only [eq] using e.symm.reachable.trans u.reachable⟩

/-- Every face between consecutive regular rows has a physical descent.
This includes faces touching the boundaries and both sides of the tip gap. -/
theorem regular_climbs (k a i j : Nat) (bound : a+2≤k) (hj : j<3*k+1)
    (m : Mask) (top : m i=regular (3*a)) (bot : m (i+1)=regular (3*a)) :
    climbs (3*k+2) m i j := by
  unfold climbs
  rw [top,bot]
  simp [regular,leftRail,rightRail]
  omega

/-- Arbitrarily many stationary pitches can flank a band seam. Only columns
near one of the two tip positions can fail the local descent there. -/
theorem band_seam_climbs (k a b i j p q : Nat) (w x d e : Bool)
    (ha : a+2≤k) (hj : j<3*k+1)
    (far : (j+4 < 3*a ∧ j+4 < 3*b) ∨ (3*a+7 < j ∧ 3*b+7 < j))
    (m : Mask) (top : m i = fun c => band (3*a) p c w d)
    (bot : m (i+1) = fun c => band (3*b) q c x e) :
    climbs (3*k+2) m i j := by
  have stable (s t : Nat) (u v : Bool) (c : Nat)
      (h : (c+1<3*s ∧ c+1<3*a) ∨ (3*s+5<c ∧ 3*a+5<c)) :
      band (3*s) t c u v = regular (3*a) c := by
    unfold band
    split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
      simp [regular,leftRail,rightRail] <;> omega
  have ref := regular_climbs k a i j ha hj (fun _ => regular (3*a)) rfl rfl
  unfold climbs at ref ⊢
  rw [top,bot]
  simp only
  simpa only [stable a p w d j (by omega),stable a p w d (j+1) (by omega),
    stable a p w d (j+2) (by omega),stable a p w d (j-1) (by omega),
    stable b q x e j (by omega),stable b q x e (j+1) (by omega)] using
    (show _ from ref)

/-- It suffices to route top-row faces and the faces where local ascent
is blocked. The descent can change lanes, so the induction is on rows. -/
theorem routes_of_blocked {n} {m : Mask}
    (blocked : ∀ r c : Fin (n-1), r.val=0 ∨ ¬climbs n m r c →
      (holeDual n m).Reachable (.cell r c) .out) (r c : Fin (n-1)) :
    (holeDual n m).Reachable (.cell r c) .out := by
  induction r using (measure Fin.val).wf.induction generalizing c with
  | h r ih =>
    by_cases boundary : r.val=0
    · exact blocked r c (.inl boundary)
    by_cases h : climbs n m r c
    · obtain ⟨v,path⟩ := climbs_route r.isLt c.isLt (by omega) h
      exact path.trans (ih _ (show r.val-1<r.val by omega) v)
    · exact blocked r c (.inr h)

end GridGraphs.ResidueTwoLower
