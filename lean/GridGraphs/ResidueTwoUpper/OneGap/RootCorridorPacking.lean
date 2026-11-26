import GridGraphs.ResidueTwoUpper.OneGap.ScoredRootCorridor

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero L7 FanSlab FanBoot Camera Port BoundarySix.Connected FanBoot.SouthCap

/-- A bad tile lies strictly below an actually planted row, inside a
10-by-10 rooted window. Coordinates are physical tile coordinates. -/
def BadAt {u} (F : Finset (Site u)) (w : View) (q f : Nat) (p : Nat × Nat) : Prop :=
  ∃ j<(11+14*u-21)/4,
    Front F w q (11+14*u) (4+4*j) (f+3*j) ∧
    4+4*j < p.1 ∧ p.1 ≤ 4+4*j+9 ∧ f+3*j ≤ p.2 ∧ p.2 ≤ f+3*j+9 ∧
    square F w (1+3*p.1) (1+3*p.2)∉shapes

def corridorCount (u q : Nat) := 1+((11+14*u+3)/4-(max 3 (q+1)+12))/16

def PackedFailures {u} (F : Finset (Site u)) (w : View) (q : Nat) : Prop :=
  ∃ tile : Fin (corridorCount u q) → Nat × Nat, Function.Injective tile ∧
    ∀ i, BadAt F w q (max 3 (q+1)+12+16*i.val) (tile i)

/-- Each legal eastward shift has its own obstruction. Separation
uses `4*column-3*row`, so different steps or overlapping row ranges
cannot make two corridors count the same physical tile twice. -/
theorem disjoint_root_failures {u : Nat} {F : Finset (Site u)} {P w q} (S : Short.Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (noSouth : ¬SouthEnd F w q)
    (space : 4*(max 3 (q+1)+12)≤11+14*u+3) (hk : 59≤11+14*u) :
    PackedFailures F w q := by
  classical
  let f := max 3 (q+1)+12
  have find (i : Fin (corridorCount u q)) : ∃ p, BadAt F w q (f+16*i.val) p := by
    have bound := i.isLt
    unfold corridorCount at bound
    obtain ⟨j,jl,fr,notGood,_⟩ := first_root_failure_at S acy score one noSouth (f+16*i.val)
      (by dsimp [f]; omega) (by dsimp [f]; omega) hk
    unfold Straight at notGood
    push Not at notGood
    obtain ⟨r,hr,c,hc,mask⟩ := notGood
    have rp : r≠0 := by
      rintro rfl
      have col : f+16*i.val+3*j+c<11+14*u := by dsimp [f]; omega
      have m := fr.1 _ le_rfl le_rfl _ (by omega) col
      simp only [Nat.add_zero,m] at mask
      exact mask (by decide)
    exact ⟨(4+4*j+r,f+16*i.val+3*j+c),j,jl,fr,by dsimp; omega,by dsimp; omega,
      by dsimp; omega,by dsimp; omega,mask⟩
  choose tile belongs using find
  refine ⟨tile,?_,belongs⟩
  intro i l eq
  obtain ⟨a,_,_,al,ah,bl,bh,_⟩ := belongs i
  obtain ⟨b,_,_,cl,ch,dl,dh,_⟩ := belongs l
  rw [eq] at al ah bl bh
  apply Fin.ext
  omega

/-- Pigeonhole version: even with some bad tiles, one rooted route
reaches the cap if the available routes outnumber the possible bad
locations. Only tiles in a rooted frontier window need be covered. -/
theorem south_of_sparse_failures {u : Nat} {F : Finset (Site u)} {P w q} (S : Short.Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1)
    (space : 4*(max 3 (q+1)+12)≤11+14*u+3) (hk : 59≤11+14*u)
    (bad : Finset (Nat × Nat)) (few : bad.card<corridorCount u q)
    (covers : ∀ i : Fin (corridorCount u q), ∀ p,
      BadAt F w q (max 3 (q+1)+12+16*i.val) p → p∈bad) : SouthEnd F w q := by
  by_contra noSouth
  obtain ⟨tile,inj,belongs⟩ := disjoint_root_failures S acy score one noSouth space hk
  let name (i : Fin (corridorCount u q)) : ↥bad := ⟨tile i,covers i _ (belongs i)⟩
  have le := Fintype.card_le_of_injective name
    (fun i j eq => inj (congrArg Subtype.val eq))
  exact (Nat.not_le_of_gt few) (by simpa using le)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
