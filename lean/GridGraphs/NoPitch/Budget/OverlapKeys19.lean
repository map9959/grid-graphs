import GridGraphs.NoPitch.Budget.Flow19
import GridGraphs.NoPitch.Budget.edgeTokens
import GridGraphs.NoPitch.Budget.starPatchTokens
import GridGraphs.NoPitch.Budget.pairTokens

namespace GridGraphs.NoPitch.LocalBoard19
open PitchCut Keys FaceRows GridGraphs.NoPitch.Dual Finset

def coarse {n : Nat} (x : Fin n × Fin n) :=
  let clip4 (v : Int) := ((max (-4) (min 4 v))+4).toNat
  [axis n 4 x.1.val,axis n 4 x.2.val,clip4 ((x.1.val:Int)-x.2.val),
    clip4 ((x.1.val:Int)+x.2.val+1-n)]

def tagMap (tokens : Array Nat) (start : Nat) : Std.HashMap Nat Terms := Id.run do
  let mut tab : Std.HashMap Nat Terms := ∅
  for h : i in [:tokens.size] do
    let k := tokens[i]
    let key := k/2
    tab := tab.insert key ((start+i,if k%2=0 then 1 else -1)::tab[key]?.getD [])
  return tab
abbrev Table := Std.HashMap Nat Terms
def event (T : Table) {m n : Nat} (x : Fin m × Fin m) (y : Fin n × Fin n) (dir word : Nat) :=
  T[pack (coarse x++coarse y++[dir])*64+word]?.getD []
abbrev Signs := Terms × Terms
def diff (s : Signs) := s.1++negTerms s.2
def combine (as : List Signs) : Signs := ((as.flatMap Prod.fst),(as.flatMap Prod.snd))
def coefSigns (i : Nat) (s : Signs) := coeff i s.1-coeff i s.2

def opp (d : Fin 4) := d+2
def dirView (g : Fin 8) (d : Fin 4) : Fin 4 := Fin.ofNat 4 (direction g d.val)
def edgeWord (a b : Bool) (points : Bool) :=
  3*(2*a.toNat+b.toNat)+(if a || b then (if points then 2 else 0) else 1)
def edgePos (T : Table) (x y : X) (g : Fin 8) (d : Fin 4) (f h heads : Bool) : Signs :=
  let u := small 19 g x
  let v := small 19 g y
  let z := dirView g d
  if z.val<2 then (event T u v z.val (edgeWord f h heads),[])
  else ([],event T v u (z.val-2) (edgeWord h f (!heads)))
def aroundEdge (T : Table) (x : X) (d : Fin 4) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) : Signs :=
  match probe x d.val with
  | none => ([],[])
  | some y => combine ((List.finRange 8).map fun g => edgePos T x y g d f (bits d) (o==some d))
def aroundStar (T : Table) (x : X) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) :=
  combine ((List.finRange 4).map fun d => aroundEdge T x d f bits o)
def edgeFamily (i : Nat) := 13 ≤ i && i ≤ 343
def edgeCheck (D : Chart) :=
  let T := tagMap edgeTokens 13
  let w := contribution D (index D) (prices D edgeFamily)
  decide (∀ x f bits o, permissible x bits f o →
    let s := aroundStar T x f bits o
    balanced (w (localStar x f bits o) ++ negTerms s.1 ++ s.2))
theorem edgeCheck19 : edgeCheck chart19 := by native_decide

end GridGraphs.NoPitch.LocalBoard19
