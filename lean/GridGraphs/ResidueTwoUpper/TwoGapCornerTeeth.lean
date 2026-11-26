import GridGraphs.ResidueTwoUpper.TwoGapCornerBox

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
open ResidueZero Stencil Words BoundarySix.Connected

theorem transported (u : Nat) (c : Corner) (r k : Fin 3) (m : Fin 512) :
    twoOrbitPatch (35+42*(u:Int)) (coord (origin (n:=35+42*u) (by omega) c r k)) m=
      twoOrbitPatch 23 (coord (origin (n:=23) (by decide) c r k)) m := by
  let j : Int := 4+14*u
  have N : 35+42*(u:Int)=23+3*j := by dsimp [j]; ring
  have eq : representative 21 j (coord (origin (n:=35+42*u) (by omega) c r k))=
      coord (origin (n:=23) (by decide) c r k) := by
    have hr := r.isLt; have hk := k.isLt
    rcases c with ⟨a,b⟩; cases a <;> cases b <;> ext <;>
      dsimp [representative,rep,coord,origin,loc,j] <;> split_ifs <;> omega
  simp only [twoOrbitPatch,N,show 23+3*j-2=21+3*j by ring,
    patchLocation_transport (b:=21) (by decide) (j:=j) (by dsimp [j]; positivity),eq]
  rfl

def tag (c : Corner) (m r k : Nat) := bit m (3*rev c.1 r+rev c.2 k)
private theorem checkCorner : ∀ (c : Corner) (m : Fin 512),
    maskOK m → twoOrbitPatch 23 (coord (origin (n:=23) (by decide) c 0 0)) m=0 →
    tag c m 0 0=1 → tag c m 1 1=0 → tag c m 1 2=0 → tag c m 2 1=0 →
    let w := 8*tag c m 0 1+4*tag c m 0 2+2*tag c m 1 0+tag c m 2 0
    w∈[3,7,12,13] → (tag c m 2 2=1 ↔ w=3 ∨ w=12) := by native_decide

/-- Direct physical corner test: open corner teeth exist and closed corner
teeth are absent. No spanning-tree assumption on the whole square. -/
theorem corner_tooth {u : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (c : Corner) :
    let hn : 35≤35+42*u := by omega
    site hn c 2 2∈F ↔ physicalWord hn F c=3 ∨ physicalWord hn F c=12 := by
  let n := 35+42*u
  have hn : 35≤n := by dsimp [n]; omega
  obtain ⟨P,d,step,_,_,zero,good,cases'⟩ := Frame.frame_of_score u F acy score
  obtain ⟨_,v,_,rfl⟩ := cases'.resolve_left (by omega)
  let a := origin (n:=n) (by omega) c 0 0
  let m := maskAt F a
  let w := physicalWord hn F c
  have wOK := physicalWord_ok hn F P good c
  have cm := corners_marked u F acy score
  have line (x) := (Frame.star_geometry hn F P step x (good (.inl x))).1
  have emp (x) := (Frame.star_geometry hn F P step x (good (.inl x))).2.1
  have price := zero (.inr a) (fun eq => by cases eq)
  change twoOrbitPatch (35+42*(u:Int)) (coord a) m=0 at price
  rw [transported] at price
  have g (i j : Fin 3) : tag c m i j=(decide (site hn c ⟨i,by omega⟩ ⟨j,by omega⟩∈F)).toNat := by
    let q := 3*rev c.1 i+rev c.2 j
    have I := i.isLt; have J := j.isLt
    have lim : q<9 := by unfold q rev; split_ifs <;> omega
    have b := bit_site hn F c 0 0 ⟨q,lim⟩
    have R : row c 0 ⟨q,lim⟩=⟨i,by omega⟩ := by apply Fin.ext; dsimp [row,q,rev]; split_ifs <;> omega
    have K : col c 0 ⟨q,lim⟩=⟨j,by omega⟩ := by apply Fin.ext; dsimp [col,q,rev]; split_ifs <;> omega
    rw [R,K] at b; exact b
  have val (i j : Fin 3) := (g i j).trans (cell_physical hn F c cm line emp _ _).symm
  have pass := checkCorner c m (physical_mask_ok F acy ..) price
    ((val 0 0).trans (by rfl)) ((val 1 1).trans (by rfl)) ((val 1 2).trans (by rfl)) ((val 2 1).trans (by rfl))
  have wbits : ∀ t : Nat, t∈[3,7,12,13] → 8*bit t 3+4*bit t 2+2*bit t 1+bit t 0=t := by
    intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl <;> decide
  have packed : 8*tag c m 0 1+4*tag c m 0 2+2*tag c m 1 0+tag c m 2 0=w := by
    convert wbits w wOK using 1
    have a : tag c m 0 1=bit w 3 := val 0 1
    have b : tag c m 0 2=bit w 2 := val 0 2
    have d : tag c m 1 0=bit w 1 := val 1 0
    have e : tag c m 2 0=bit w 0 := val 2 0
    rw [a,b,d,e]
  dsimp only at pass
  rw [packed] at pass
  have fin := pass wOK
  have pt : tag c m 2 2=(decide (site hn c 2 2∈F)).toNat := g 2 2
  rw [pt] at fin
  simpa [w] using fin

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
