import GridGraphs.Geometry.GridExpandedContour
import GridGraphs.Geometry.GridCrosscutCycle

/-! # Expanded-contour routing at the southwest and northeast corners -/

namespace GridGraphs

open SimpleGraph

namespace GridExpandedContour

variable {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]

theorem southwest_succ_east_reverse (hn : 2 ≤ n) (d : GridDirectionalDart T)
    (hsource : d.source = (⟨n - 1, by omega⟩, ⟨0, by omega⟩))
    (hdirection : d.direction = .east) :
    succ (T := T) (slotOfDart d.reverse) =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .south) := by
  rw [succ_slotOfDart]
  simp [GridDirectionalDart.reverse, hsource, hdirection]
  rfl

theorem southwest_succ_south (hn : 2 ≤ n) :
    succ (T := T) ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .south) =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .west) := by
  apply succ_of_not_occupied
  rw [Occupied, GridDirectionalDart.mem_directionsAt]
  rintro ⟨w, hw, -⟩
  have hnot : ¬n - 1 + 1 < n := by omega
  simp [gridNeighbor?, hnot] at hw

theorem southwest_succ_west (hn : 2 ≤ n) :
    succ (T := T) ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .west) =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .north) := by
  apply succ_of_not_occupied
  simp [Occupied, GridDirectionalDart.mem_directionsAt, gridNeighbor?]

theorem southwest_succ_succ_east_reverse (hn : 2 ≤ n)
    (d : GridDirectionalDart T)
    (hsource : d.source = (⟨n - 1, by omega⟩, ⟨0, by omega⟩))
    (hdirection : d.direction = .east) :
    succ (T := T) (succ (T := T) (slotOfDart d.reverse)) =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .west) := by
  rw [southwest_succ_east_reverse hn d hsource hdirection,
    southwest_succ_south hn]

theorem southwest_succ_succ_succ_east_reverse (hn : 2 ≤ n)
    (d : GridDirectionalDart T)
    (hsource : d.source = (⟨n - 1, by omega⟩, ⟨0, by omega⟩))
    (hdirection : d.direction = .east) :
    succ (T := T) (succ (T := T) (succ (T := T) (slotOfDart d.reverse))) =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .north) := by
  rw [southwest_succ_succ_east_reverse hn d hsource hdirection,
    southwest_succ_west hn]

theorem southwest_succ_north_reverse (hn : 2 ≤ n) (d : GridDirectionalDart T)
    (hsource : d.source = (⟨n - 1, by omega⟩, ⟨0, by omega⟩))
    (hdirection : d.direction = .north) :
    succ (T := T) (slotOfDart d.reverse) =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .east) := by
  rw [succ_slotOfDart]
  simp [GridDirectionalDart.reverse, hsource, hdirection]
  rfl

theorem northeast_succ_west_reverse (hn : 2 ≤ n) (d : GridDirectionalDart T)
    (hsource : d.source = (⟨0, by omega⟩, ⟨n - 1, by omega⟩))
    (hdirection : d.direction = .west) :
    succ (T := T) (slotOfDart d.reverse) =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .north) := by
  rw [succ_slotOfDart]
  simp [GridDirectionalDart.reverse, hsource, hdirection]
  rfl

theorem northeast_succ_north (hn : 2 ≤ n) :
    succ (T := T) ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .north) =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .east) := by
  apply succ_of_not_occupied
  rw [Occupied, GridDirectionalDart.mem_directionsAt]
  rintro ⟨w, hw, -⟩
  simp [gridNeighbor?] at hw

theorem northeast_succ_east (hn : 2 ≤ n) :
    succ (T := T) ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .east) =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .south) := by
  apply succ_of_not_occupied
  rw [Occupied, GridDirectionalDart.mem_directionsAt]
  rintro ⟨w, hw, -⟩
  have hnot : ¬n - 1 + 1 < n := by omega
  simp [gridNeighbor?, hnot] at hw

theorem northeast_succ_succ_west_reverse (hn : 2 ≤ n)
    (d : GridDirectionalDart T)
    (hsource : d.source = (⟨0, by omega⟩, ⟨n - 1, by omega⟩))
    (hdirection : d.direction = .west) :
    succ (T := T) (succ (T := T) (slotOfDart d.reverse)) =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .east) := by
  rw [northeast_succ_west_reverse hn d hsource hdirection,
    northeast_succ_north hn]

theorem northeast_succ_succ_succ_west_reverse (hn : 2 ≤ n)
    (d : GridDirectionalDart T)
    (hsource : d.source = (⟨0, by omega⟩, ⟨n - 1, by omega⟩))
    (hdirection : d.direction = .west) :
    succ (T := T) (succ (T := T) (succ (T := T) (slotOfDart d.reverse))) =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .south) := by
  rw [northeast_succ_succ_west_reverse hn d hsource hdirection,
    northeast_succ_east hn]

theorem northeast_succ_south_reverse (hn : 2 ≤ n) (d : GridDirectionalDart T)
    (hsource : d.source = (⟨0, by omega⟩, ⟨n - 1, by omega⟩))
    (hdirection : d.direction = .south) :
    succ (T := T) (slotOfDart d.reverse) =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .west) := by
  rw [succ_slotOfDart]
  simp [GridDirectionalDart.reverse, hsource, hdirection]
  rfl

end GridExpandedContour

/-! ## Long boundary walks avoiding a corner -/

def southwestLongBoundaryStart (hn : 2 ≤ n) : GridBoundaryPosition n n :=
  ⟨if n = 2 then 0 else 3 * n - 2, by
    unfold gridBoundaryLength
    split_ifs <;> omega⟩

def northeastLongBoundaryStart (hn : 2 ≤ n) : GridBoundaryPosition n n :=
  ⟨n, by unfold gridBoundaryLength; omega⟩

theorem southwestLongBoundaryStart_vertex (hn : 2 ≤ n) :
    gridBoundaryVertex hn hn (southwestLongBoundaryStart hn) =
      (⟨n - 2, by omega⟩, ⟨0, by omega⟩) := by
  by_cases h2 : n = 2
  · subst n
    rfl
  · rw [gridBoundaryVertex_left hn hn _ (by
      simp [southwestLongBoundaryStart, h2]
      omega)]
    apply Prod.ext <;> apply Fin.ext <;>
      simp [southwestLongBoundaryStart, h2, gridBoundaryLength]
    omega

theorem southwestLongBoundary_offset (hn : 2 ≤ n) :
    cyclicOffset (gridBoundaryLength_pos hn hn)
        (southwestLongBoundaryStart hn) (4 * n - 6) =
      ⟨3 * n - 4, by unfold gridBoundaryLength; omega⟩ := by
  by_cases h2 : n = 2
  · subst n
    rfl
  apply Fin.ext
  simp only [southwestLongBoundaryStart, h2, if_false]
  change (3 * n - 2 + (4 * n - 6)) % gridBoundaryLength n n = 3 * n - 4
  have hsum : 3 * n - 2 + (4 * n - 6) =
      gridBoundaryLength n n + (3 * n - 4) := by
    simp [gridBoundaryLength]
    omega
  have hlt : 3 * n - 4 < gridBoundaryLength n n := by
    unfold gridBoundaryLength
    omega
  rw [hsum, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hlt

theorem southwestLongBoundaryEnd_vertex (hn : 2 ≤ n) :
    gridBoundaryVertex hn hn
        (cyclicOffset (gridBoundaryLength_pos hn hn)
          (southwestLongBoundaryStart hn) (4 * n - 6)) =
      (⟨n - 1, by omega⟩, ⟨1, by omega⟩) := by
  by_cases h2 : n = 2
  · subst n
    rw [southwestLongBoundary_offset hn]
    norm_num [gridBoundaryVertex]
  · rw [southwestLongBoundary_offset hn]
    rw [gridBoundaryVertex_bottom hn hn _ (by
      change ¬3 * n - 4 < n + n - 1
      omega) (by
      change 3 * n - 4 < n + 2 * n - 2
      omega)]
    apply Prod.ext <;> apply Fin.ext <;> simp
    omega

def southwestLongBoundaryWalk (hn : 2 ≤ n) :
    (gridGraph n n).Walk
      (⟨n - 2, by omega⟩, ⟨0, by omega⟩)
      (⟨n - 1, by omega⟩, ⟨1, by omega⟩) :=
  (gridBoundaryForwardWalk hn hn (southwestLongBoundaryStart hn)
    (4 * n - 6)).copy
      (southwestLongBoundaryStart_vertex hn)
      (southwestLongBoundaryEnd_vertex hn)

theorem southwestLongBoundaryWalk_on_boundary (hn : 2 ≤ n)
    {x : GridVertex n n} (hx : x ∈ (southwestLongBoundaryWalk hn).support) :
    IsGridBoundary x := by
  rw [southwestLongBoundaryWalk, Walk.support_copy,
    mem_support_gridBoundaryForwardWalk_iff] at hx
  obtain ⟨t, -, rfl⟩ := hx
  exact gridBoundaryVertex_isBoundary hn hn _

theorem southwestCorner_not_mem_longBoundaryWalk (hn : 2 ≤ n) :
    ((⟨n - 1, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) ∉
      (southwestLongBoundaryWalk hn).support := by
  intro hx
  rw [southwestLongBoundaryWalk, Walk.support_copy,
    mem_support_gridBoundaryForwardWalk_iff] at hx
  obtain ⟨t, ht, hv⟩ := hx
  by_cases h2 : n = 2
  · subst n
    interval_cases t <;> norm_num [southwestLongBoundaryStart, cyclicOffset,
      gridBoundaryLength, gridBoundaryVertex] at hv
  have hn3 : 3 ≤ n := by omega
  let cornerPosition : GridBoundaryPosition n n :=
    ⟨3 * n - 3, by unfold gridBoundaryLength; omega⟩
  have hcorner : gridBoundaryVertex hn hn cornerPosition =
      ((⟨n - 1, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) := by
    rw [gridBoundaryVertex_bottom hn hn cornerPosition (by
      dsimp [cornerPosition]
      omega) (by
      dsimp [cornerPosition]
      omega)]
    apply Prod.ext <;> apply Fin.ext <;> simp [cornerPosition]
    omega
  have hp := gridBoundaryVertex_injective hn hn (hcorner.trans hv)
  have hi := congrArg Fin.val hp
  change 3 * n - 3 =
    ((southwestLongBoundaryStart hn).val + t) % gridBoundaryLength n n at hi
  simp [southwestLongBoundaryStart, h2] at hi
  by_cases htwrap : t < n - 2
  · rw [Nat.mod_eq_of_lt] at hi
    · omega
    · simp [gridBoundaryLength]
      omega
  · have hsum : 3 * n - 2 + t =
        gridBoundaryLength n n + (t - (n - 2)) := by
      simp [gridBoundaryLength]
      omega
    have hrem : t - (n - 2) < gridBoundaryLength n n := by
      have hle : t - (n - 2) ≤ (4 * n - 6) - (n - 2) :=
        Nat.sub_le_sub_right ht (n - 2)
      unfold gridBoundaryLength
      omega
    rw [hsum, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hrem] at hi
    omega

theorem southwestDartSource_not_mem_longBoundaryWalk
    {T : SimpleGraph (GridVertex n n)} (hn : 2 ≤ n)
    (d : GridDirectionalDart T)
    (hsource : d.source = (⟨n - 1, by omega⟩, ⟨0, by omega⟩)) :
    d.source ∉ (southwestLongBoundaryWalk hn).support := by
  rw [hsource]
  exact southwestCorner_not_mem_longBoundaryWalk hn

theorem northeastLongBoundaryStart_vertex (hn : 2 ≤ n) :
    gridBoundaryVertex hn hn (northeastLongBoundaryStart hn) =
      (⟨1, by omega⟩, ⟨n - 1, by omega⟩) := by
  rw [gridBoundaryVertex_right hn hn _ (by
    simp [northeastLongBoundaryStart]) (by
      change n < n + n - 1
      omega)]
  apply Prod.ext <;> apply Fin.ext <;>
    simp [northeastLongBoundaryStart]

theorem northeastLongBoundary_offset (hn : 2 ≤ n) :
    cyclicOffset (gridBoundaryLength_pos hn hn)
        (northeastLongBoundaryStart hn) (4 * n - 6) =
      ⟨n - 2, by unfold gridBoundaryLength; omega⟩ := by
  apply Fin.ext
  change (n + (4 * n - 6)) % gridBoundaryLength n n = n - 2
  have hsum : n + (4 * n - 6) =
      gridBoundaryLength n n + (n - 2) := by
    simp [gridBoundaryLength]
    omega
  have hlt : n - 2 < gridBoundaryLength n n := by
    unfold gridBoundaryLength
    omega
  rw [hsum, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hlt

theorem northeastLongBoundaryEnd_vertex (hn : 2 ≤ n) :
    gridBoundaryVertex hn hn
        (cyclicOffset (gridBoundaryLength_pos hn hn)
          (northeastLongBoundaryStart hn) (4 * n - 6)) =
      (⟨0, by omega⟩, ⟨n - 2, by omega⟩) := by
  rw [northeastLongBoundary_offset hn]
  rw [gridBoundaryVertex_top hn hn _ (by
    change n - 2 < n
    omega)]

def northeastLongBoundaryWalk (hn : 2 ≤ n) :
    (gridGraph n n).Walk
      (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
      (⟨0, by omega⟩, ⟨n - 2, by omega⟩) :=
  (gridBoundaryForwardWalk hn hn (northeastLongBoundaryStart hn)
    (4 * n - 6)).copy
      (northeastLongBoundaryStart_vertex hn)
      (northeastLongBoundaryEnd_vertex hn)

theorem northeastLongBoundaryWalk_on_boundary (hn : 2 ≤ n)
    {x : GridVertex n n} (hx : x ∈ (northeastLongBoundaryWalk hn).support) :
    IsGridBoundary x := by
  rw [northeastLongBoundaryWalk, Walk.support_copy,
    mem_support_gridBoundaryForwardWalk_iff] at hx
  obtain ⟨t, -, rfl⟩ := hx
  exact gridBoundaryVertex_isBoundary hn hn _

theorem northeastCorner_not_mem_longBoundaryWalk (hn : 2 ≤ n) :
    ((⟨0, by omega⟩, ⟨n - 1, by omega⟩) : GridVertex n n) ∉
      (northeastLongBoundaryWalk hn).support := by
  intro hx
  rw [northeastLongBoundaryWalk, Walk.support_copy,
    mem_support_gridBoundaryForwardWalk_iff] at hx
  obtain ⟨t, ht, hv⟩ := hx
  let cornerPosition : GridBoundaryPosition n n :=
    ⟨n - 1, by unfold gridBoundaryLength; omega⟩
  have hcorner : gridBoundaryVertex hn hn cornerPosition =
      ((⟨0, by omega⟩, ⟨n - 1, by omega⟩) : GridVertex n n) := by
    rw [gridBoundaryVertex_top hn hn cornerPosition (by
      dsimp [cornerPosition]
      omega)]
  have hp := gridBoundaryVertex_injective hn hn (hcorner.trans hv)
  have hi := congrArg Fin.val hp
  change n - 1 =
    ((northeastLongBoundaryStart hn).val + t) % gridBoundaryLength n n at hi
  simp [northeastLongBoundaryStart] at hi
  by_cases htwrap : t < 3 * n - 4
  · rw [Nat.mod_eq_of_lt] at hi
    · omega
    · simp [gridBoundaryLength]
      omega
  · have hsum : n + t =
        gridBoundaryLength n n + (t - (3 * n - 4)) := by
      simp [gridBoundaryLength]
      omega
    have hrem : t - (3 * n - 4) < gridBoundaryLength n n := by
      have hle : t - (3 * n - 4) ≤ (4 * n - 6) - (3 * n - 4) :=
        Nat.sub_le_sub_right ht (3 * n - 4)
      unfold gridBoundaryLength
      omega
    rw [hsum, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hrem] at hi
    omega

theorem northeastDartSource_not_mem_longBoundaryWalk
    {T : SimpleGraph (GridVertex n n)} (hn : 2 ≤ n)
    (d : GridDirectionalDart T)
    (hsource : d.source = (⟨0, by omega⟩, ⟨n - 1, by omega⟩)) :
    d.source ∉ (northeastLongBoundaryWalk hn).support := by
  rw [hsource]
  exact northeastCorner_not_mem_longBoundaryWalk hn

end GridGraphs
