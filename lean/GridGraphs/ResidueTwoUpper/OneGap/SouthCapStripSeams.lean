import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayMatrix

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

inductive SidePair where | north | south | west | east

def sideKey : SidePair → Word → Nat
  | .north,(a,b,_,_) => a+512*b
  | .south,(_,_,c,d) => c+512*d
  | .west,(a,_,c,_) => a+512*c
  | .east,(_,b,_,d) => b+512*d

private def keys (side : SidePair) (ws : List Word) : Std.HashSet Nat :=
  Std.HashSet.ofList (ws.map (sideKey side))

private theorem key_mem (side : SidePair) {w : Word} {ws : List Word} (hw : w∈ws) :
    (keys side ws).contains (sideKey side w)=true := by
  apply Std.HashSet.contains_iff_mem.mpr
  simpa [keys] using (List.mem_map_of_mem (f := sideKey side) hw)

def seamPass (h : Nat) (m : MatrixBank) : MatrixBank :=
  matrixOf h fun r c =>
    let D := matrixRead m
    let n := keys .south (D (r-1) c)
    let s := keys .north (D (r+1) c)
    let w := keys .east (D r (c-1))
    let e := keys .west (D r (c+1))
    (D r c).filter fun v =>
      (r==0 || n.contains (sideKey .north v)) &&
      (r+2==h || s.contains (sideKey .south v)) &&
      (c==0 || w.contains (sideKey .west v)) &&
      (c+2==width h || e.contains (sideKey .east v))

abbrev MatrixAdmits (h : Nat) (m : MatrixBank) (t : Tiles) :=
  Admitted h (width h) (memBank (matrixRead m)) t

theorem seamPass_sound {h m t} (ok : MatrixAdmits h m t) :
    MatrixAdmits h (seamPass h m) t := by
  intro r c hr hc
  change word t r c ∈ matrixRead (seamPass h m) r c
  rw [seamPass,matrixRead_of _ _ _ _ hr hc]
  apply List.mem_filter.mpr
  refine ⟨ok r c hr hc,?_⟩
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · by_cases z : r=0
    · exact Or.inl z
    · right
      simpa only [sideKey,word,show r-1+1=r by omega] using
        key_mem .south (ok (r-1) c (by omega) hc)
  · by_cases z : r+2=h
    · exact Or.inl z
    · exact Or.inr (key_mem .north (ok (r+1) c (by omega) hc))
  · by_cases z : c=0
    · exact Or.inl z
    · right
      simpa only [sideKey,word,show c-1+1=c by omega] using
        key_mem .east (ok r (c-1) hr (by omega))
  · by_cases z : c+2=width h
    · exact Or.inl z
    · exact Or.inr (key_mem .west (ok r (c+1) hr (by omega)))

def seams (h : Nat) (m : MatrixBank) : Nat → MatrixBank
  | 0 => m
  | n+1 => seamPass h (seams h m n)

theorem seams_sound {h m t} (ok : MatrixAdmits h m t) (n : Nat) :
    MatrixAdmits h (seams h m n) t := by
  induction n with
  | zero => exact ok
  | succ n ih => exact seamPass_sound ih

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
