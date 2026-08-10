import GridGraphs.GridChannelContourRealization

/-!
# Canonical boundary germs for shore sweeps

The `n + 3` canonical demands start at distinct side-labelled boundary
incidences.  These labels distinguish the two incidences at a corner.
-/

namespace GridGraphs

namespace CanonicalShoreDemand

/-- Boundary vertex and side from which a canonical shore demand enters the
grid. -/
def boundaryIncidence {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n) :
    CanonicalShoreDemand axis n → GridVertex n n × OuterBoundarySide :=
  match axis with
  | .rows => fun q => match q with
      | .inl r => ((r, ⟨0, by omega⟩), .left)
      | .inr i =>
          if i.val = 0 then
            ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .top)
          else if i.val = 1 then
            ((⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩), .right)
          else
            ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .bottom)
  | .columns => fun q => match q with
      | .inl c => ((⟨0, by omega⟩, c), .top)
      | .inr i =>
          if i.val = 0 then
            ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .right)
          else if i.val = 1 then
            ((⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩), .bottom)
          else
            ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .left)

/-- Canonical demands have distinct boundary germs, including distinct side
labels when two germs use the same corner vertex. -/
theorem boundaryIncidence_injective {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n) :
    Function.Injective (boundaryIncidence axis hn) := by
  intro a b hab
  cases axis with
  | rows =>
      rcases a with a | a <;> rcases b with b | b
      · congr 1
        exact congrArg (fun x => x.1.1) hab
      · fin_cases b <;> simp [boundaryIncidence] at hab
      · fin_cases a <;> simp [boundaryIncidence] at hab
      · fin_cases a <;> fin_cases b <;> simp [boundaryIncidence] at hab ⊢
  | columns =>
      rcases a with a | a <;> rcases b with b | b
      · congr 1
        exact congrArg (fun x => x.1.2) hab
      · fin_cases b <;> simp [boundaryIncidence] at hab
      · fin_cases a <;> simp [boundaryIncidence] at hab
      · fin_cases a <;> fin_cases b <;> simp [boundaryIncidence] at hab ⊢

/-- The side label of a canonical germ is incident with its boundary vertex. -/
theorem boundaryIncidence_side_incidence {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (q : CanonicalShoreDemand axis n) :
    let p := boundaryIncidence axis hn q
    match p.2 with
    | .top => p.1.1.val = 0
    | .bottom => p.1.1.val + 1 = n
    | .left => p.1.2.val = 0
    | .right => p.1.2.val + 1 = n := by
  cases axis with
  | rows =>
      rcases q with q | q
      · simp [boundaryIncidence]
      · fin_cases q <;> simp [boundaryIncidence] <;> omega
  | columns =>
      rcases q with q | q
      · simp [boundaryIncidence]
      · fin_cases q <;> simp [boundaryIncidence] <;> omega

/-- Canonical demands whose boundary germ already lies in cotree support and
therefore terminates directly at a split outer port. -/
noncomputable def directExits {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] :
    Finset (CanonicalShoreDemand axis n) := by
  classical
  exact Finset.univ.filter fun q =>
    (boundaryIncidence axis hn q).1 ∈ supportFinset (gridGraph n n \ T)

/-- The actual split outer port used by a directly terminating canonical
germ. -/
noncomputable def directExitOuterPort {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (q : ↥(directExits axis hn T)) : GridCotreeOuterPort T := by
  classical
  let p := boundaryIncidence axis hn q.1
  have hpU : p.1 ∈ supportFinset (gridGraph n n \ T) := by
    exact (Finset.mem_filter.mp q.2).2
  have hpSide := boundaryIncidence_side_incidence axis hn q.1
  change (match p.2 with
    | .top => p.1.1.val = 0
    | .bottom => p.1.1.val + 1 = n
    | .left => p.1.2.val = 0
    | .right => p.1.2.val + 1 = n) at hpSide
  change OuterBoundaryPort (supportFinset (gridGraph n n \ T))
  rcases hside : p.2 with _ | _ | _ | _
  · exact Sum.inl ⟨p.1, Finset.mem_filter.mpr ⟨hpU, by simpa [hside] using hpSide⟩⟩
  · exact Sum.inr (Sum.inl
      ⟨p.1, Finset.mem_filter.mpr ⟨hpU, by simpa [hside] using hpSide⟩⟩)
  · exact Sum.inr (Sum.inr (Sum.inl
      ⟨p.1, Finset.mem_filter.mpr ⟨hpU, by simpa [hside] using hpSide⟩⟩))
  · exact Sum.inr (Sum.inr (Sum.inr
      ⟨p.1, Finset.mem_filter.mpr ⟨hpU, by simpa [hside] using hpSide⟩⟩))

@[simp] theorem directExitOuterPort_vertex {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (q : ↥(directExits axis hn T)) :
    (directExitOuterPort axis hn T q).vertex =
      (boundaryIncidence axis hn q.1).1 := by
  classical
  rcases q with ⟨q, hq⟩
  cases axis with
  | rows =>
      rcases q with q | q
      · simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.vertex]
      · fin_cases q <;>
          simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.vertex]
  | columns =>
      rcases q with q | q
      · simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.vertex]
      · fin_cases q <;>
          simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.vertex]

@[simp] theorem directExitOuterPort_side {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (q : ↥(directExits axis hn T)) :
    (directExitOuterPort axis hn T q).side =
      (boundaryIncidence axis hn q.1).2 := by
  classical
  rcases q with ⟨q, hq⟩
  cases axis with
  | rows =>
      rcases q with q | q
      · simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.side]
      · fin_cases q <;>
          simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.side]
  | columns =>
      rcases q with q | q
      · simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.side]
      · fin_cases q <;>
          simp [directExitOuterPort, boundaryIncidence, OuterBoundaryPort.side]

/-- Directly terminating canonical germs use distinct split outer ports. -/
noncomputable def directExitEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] :
    ↥(directExits axis hn T) ↪ GridCotreeOuterPort T where
  toFun := directExitOuterPort axis hn T
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply boundaryIncidence_injective axis hn
    apply Prod.ext
    · simpa using congrArg OuterBoundaryPort.vertex hab
    · simpa using congrArg OuterBoundaryPort.side hab

end CanonicalShoreDemand

end GridGraphs
