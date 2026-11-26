import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPrices

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

/-- Physical coordinate of a halo site, numbered from six sites before
the plaquette origin. The complete halo has offsets `0..17`. -/
def haloSite (k extent i d : Nat) : Nat := (1+3*(k-extent+i))-6+d

def atlasSite (extent i d : Nat) : Nat :=
  (1+3*repTile (endTag extent i))-6+d

/-- The entire halo, including the last two sites beyond the
patch-origin range, transports with its actual rim and depth-one ring.
The middle tag represents no rim *unless* a halo offset reaches it;
the arithmetic here is what rules that out for the tested offsets. -/
theorem halo_site_geometry {u k extent i d : Nat} (ke : k=11+14*u) (hk : 53≤k)
    (he : extent+4≤k) (hi : i+2≤extent) (hd : d≤17) :
    let n := 35+42*u
    let x := haloSite k extent i d
    let b := atlasSite extent i d
    2≤x ∧ 2≤b ∧ (x<n ↔ b<119) ∧ (x%3=b%3) ∧
    ∀ a : Nat, a≤6 → (x+a+1=n ↔ b+a+1=119) := by
  dsimp only
  unfold haloSite atlasSite endTag repTile
  split_ifs <;> constructor <;> try omega
  all_goals constructor <;> try omega
  all_goals constructor <;> try omega
  all_goals constructor <;> try omega

/-- Board clipping commutes with taking a physical halo. In particular
the finite checker should not introduce ghost marks after the last row
or column of a clipped halo. -/
theorem halo_box_geometry {u k h w r c a b : Nat}
    (ke : k=11+14*u) (hk : 53≤k)
    (hh : h+4≤k) (hw : w+4≤k) (hr : r+2≤h) (hc : c+2≤w)
    (ha : a≤17) (hb : b≤17) :
    let n := 35+42*u
    let x := haloSite k h r a
    let y := haloSite k w c b
    let X := atlasSite h r a
    let Y := atlasSite w c b
    ((x<n ∧ y<n) ↔ (X<119 ∧ Y<119)) ∧
    ((x+1=n ∨ y+1=n) ↔ (X+1=119 ∨ Y+1=119)) ∧
    ((x+2=n ∨ y+2=n) ↔ (X+2=119 ∨ Y+2=119)) := by
  have R := halo_site_geometry ke hk hh hr ha
  have C := halo_site_geometry ke hk hw hc hb
  exact ⟨and_congr R.2.2.1 C.2.2.1,
    or_congr (R.2.2.2.2 0 (by decide)) (C.2.2.2.2 0 (by decide)),
    or_congr (R.2.2.2.2 1 (by decide)) (C.2.2.2.2 1 (by decide))⟩

/-- Translation of halo offsets preserves adjacency, not merely the
position of a patch origin. This lets the same forced/unforced edge
bits be used on the physical halo and in the catalogue window. -/
theorem halo_adj_geometry (k h w r c a b d e : Nat)
    {n m : Nat}
    (A : haloSite k h r a < n) (B : haloSite k w c b < n)
    (D : haloSite k h r d < n) (E : haloSite k w c e < n)
    (A' : atlasSite h r a < m) (B' : atlasSite w c b < m)
    (D' : atlasSite h r d < m) (E' : atlasSite w c e < m) :
    GridGraphs.adjacent n n (⟨_,A⟩,⟨_,B⟩) (⟨_,D⟩,⟨_,E⟩) ↔
    GridGraphs.adjacent m m (⟨_,A'⟩,⟨_,B'⟩) (⟨_,D'⟩,⟨_,E'⟩) := by
  simp only [GridGraphs.adjacent, Fin.ext_iff]
  unfold haloSite atlasSite
  omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
