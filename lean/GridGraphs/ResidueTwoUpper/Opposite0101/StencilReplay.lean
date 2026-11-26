import GridGraphs.ResidueTwoUpper.Opposite0101.Strip

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero Stencil BoundarySix.Connected

def starEntry (v : Bool) (j r f nb : Nat) : Bool := (sTab v j r).testBit (f+2*nb)
def patchEntry (v : Bool) (j r m : Nat) : Bool := (pTab v j r).testBit m

/-- These directions need not agree between different stars in the
transfer: the true direction suffices to witness membership. -/
theorem starReplay : ∀ (v : Bool) (j : Fin 35) (r : Fin 6) (f : Fin 2)
    (nb : Fin 16) (o : Fin 5), let p := xy v (r.val:Int) (j.val:Int)
    let w := twoOrbitStar 35 p f nb o
    starOK 35 p f nb o →
    (Frame.ends 34 p.1 p.2 → f.val=1) →
    (w=0 ∨ ((r.val=0 ∨ j.val=0 ∨ j.val=34) ∧ w=full)) →
    starEntry v j r f nb := by dsimp only; unfold Frame.ends; native_decide

theorem patchReplay : ∀ (v : Bool) (j : Fin 33) (r : Fin 5) (m : Fin 512),
    maskOK m → twoOrbitPatch 35 (xy v (r.val:Int) (j.val:Int)) m=0 → patchEntry v j r m := by
  native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
