import GridGraphs.ResidueTwoUpper.TwoGapWords
import GridGraphs.ResidueTwoUpper.TwoGapCrop

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
open Words ResidueZero Stencil BoundarySix.Connected

def site {n} (hn : 35≤n) (c : Corner) (r k : Fin 5) : GridVertex n n :=
  (⟨loc n c.1 r.val,by have := r.isLt; unfold loc; split <;> omega⟩,
   ⟨loc n c.2 k.val,by have := k.isLt; unfold loc; split <;> omega⟩)
def origin {n} (hn : 23≤n) (c : Corner) (r k : Fin 3) : origins n :=
  (⟨loc (n-2) c.1 r.val,by have := r.isLt; unfold loc; split <;> omega⟩,
   ⟨loc (n-2) c.2 k.val,by have := k.isLt; unfold loc; split <;> omega⟩)
def rev (far : Bool) (i : Nat) := if far then 2-i else i
def row (c : Corner) (r : Fin 3) (q : Fin 9) : Fin 5 :=
  ⟨r.val+rev c.1 (q.val/3),by have := r.isLt; have := q.isLt; unfold rev; split <;> omega⟩
def col (c : Corner) (k : Fin 3) (q : Fin 9) : Fin 5 :=
  ⟨k.val+rev c.2 (q.val%3),by have := k.isLt; have := q.isLt; unfold rev; split <;> omega⟩

theorem bit_site {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner)
    (r k : Fin 3) (q : Fin 9) :
    bit (maskAt F (origin (by omega) c r k)) q=
      (decide (site hn c (row c r q) (col c k q)∈F)).toNat := by
  let a : origins n := origin (by omega) c r k
  have b := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega) (by have := a.2.isLt; omega) q
  have eq : coord a+offset q=coord (site hn c (row c r q) (col c k q)) := by
    have R := r.isLt; have K := k.isLt; have Q := q.isLt
    rcases c with ⟨x,y⟩; cases x <;> cases y <;> ext <;>
      dsimp [coord,site,row,col,origin,a,offset,loc,rev] <;> omega
  change bit (maskAt F a) q=(marked F (coord a+offset q)).toNat at b
  rw [b,eq,marked_at]

def innerBit (c : Corner) (m r k : Nat) := bit m (3*rev c.1 (r-2)+rev c.2 (k-2))
def cell (c : Corner) (w m r k : Nat) :=
  if r=0 then (if k=1 then bit w 3 else if k=2 then bit w 2 else 1)
  else if k=0 then (if r=1 then bit w 1 else if r=2 then bit w 0 else 1)
  else if r=1 ∨ k=1 then 0 else innerBit c m r k

theorem cell_physical {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner)
    (corners : ∀ x, isCorner x → x∈F)
    (line : ∀ x, Frame.straight n (coord x) → x∈F)
    (empty : ∀ x, Frame.depthAt n (coord x)=1 → x∉F) (r k : Fin 5) :
    cell c (physicalWord hn F c) (maskAt F (origin (by omega) c 2 2)) r k =
      (decide (site hn c r k∈F)).toNat := by
  have R := r.isLt; have K := k.isLt
  have arm (a : Arm) (j : Fin 3) : bits hn F a j≤1 := by unfold bits; cases decide ((atArm hn a j).1∈F) <;> decide
  have enc : ∀ a b d e : Fin 2, let w := 8*a.val+4*b.val+2*d.val+e.val
    bit w 3=a.val ∧ bit w 2=b.val ∧ bit w 1=d.val ∧ bit w 0=e.val := by decide +kernel
  have eq := enc ⟨_,Nat.lt_succ_of_le (arm (c,false) 1)⟩ ⟨_,Nat.lt_succ_of_le (arm (c,false) 2)⟩
    ⟨_,Nat.lt_succ_of_le (arm (c,true) 1)⟩ ⟨_,Nat.lt_succ_of_le (arm (c,true) 2)⟩
  change bit (physicalWord hn F c) 3=_ ∧ bit (physicalWord hn F c) 2=_ ∧ bit (physicalWord hn F c) 1=_ ∧ bit (physicalWord hn F c) 0=_ at eq
  have geom (r k : Fin 5) : Frame.depthAt n (coord (site hn c r k))=min (r.val:Int) k.val ∧
      max (Frame.depth (n-1) (coord (site hn c r k)).1) (Frame.depth (n-1) (coord (site hn c r k)).2)
        =max (r.val:Int) k.val := by
    have R := r.isLt; have K := k.isLt
    rcases c with ⟨a,b⟩; cases a <;> cases b <;>
      simp only [Frame.depthAt,Frame.depth,coord,site,loc] <;> dsimp <;> omega
  unfold cell
  split_ifs with rz k1 k2 kz r1 r2 rim
  · rw [eq.1]; simp [bits,site,atArm,rz,k1]
  · rw [eq.2.1]; simp [bits,site,atArm,rz,k2]
  · by_cases kz : k.val=0
    · have cc : isCorner (site hn c r k) := by
        rcases c with ⟨a,b⟩; cases a <;> cases b <;> dsimp [isCorner,site,loc]; all_goals omega
      simp [corners _ cc]
    · have s := geom r k; have good : Frame.straight n (coord (site hn c r k)) := ⟨by omega,by omega⟩
      simp [line _ good]
  · rw [eq.2.2.1]; simp [bits,site,atArm,kz,r1]
  · rw [eq.2.2.2]; simp [bits,site,atArm,kz,r2]
  · have s := geom r k; have good : Frame.straight n (coord (site hn c r k)) := ⟨by omega,by omega⟩
    simp [line _ good]
  · have s := geom r k; simp [empty _ (by omega : Frame.depthAt n (coord (site hn c r k))=1)]
  · let q := 3*rev c.1 (r.val-2)+rev c.2 (k.val-2)
    have lim : q<9 := by unfold q rev; split_ifs <;> omega
    have b := bit_site hn F c 2 2 ⟨q,lim⟩
    have RR : row c 2 ⟨q,lim⟩=r := by apply Fin.ext; dsimp [row,q,rev]; split_ifs <;> omega
    have CC : col c 2 ⟨q,lim⟩=k := by apply Fin.ext; dsimp [col,q,rev]; split_ifs <;> omega
    rw [RR,CC] at b; exact b

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
