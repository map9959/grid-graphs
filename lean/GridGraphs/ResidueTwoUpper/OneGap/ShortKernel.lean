import Std

/-! Standalone executable part of the paired-owner scan. Importing only
Std allows Lake's ordinary `:dynlib` facet to precompile it separately.
`ShortKernelProof` checks definitional agreement with the proved rules. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.Kernel
abbrev L := Nat × Nat
abbrev G := Array (Array (List L))
abbrev Z := L × L
abbrev S := Array (Array (List Z))
def get {α : Type} (a : Array (Array (List α))) (r c : Nat) := ((a[r]?.getD #[])[c]?).getD []
def grid {α : Type} (h w : Nat) (f : Nat → Nat → List α) :=
  Array.ofFn fun r : Fin h => Array.ofFn fun c : Fin w => f r c
def port (out : Bool) (d : Nat) (z : L) :=
  let m := z.1
  let a := match d with | 0 => m &&& 438 | 1 => m &&& 504 | 2 => (m &&& 219) <<< 1 | _ => (m &&& 63) <<< 3
  let f := (m >>> 4)%2+((m >>> ([5,7,3,1][d]!))%2)>0
  2*a+(xor (out && decide f) (z.2==d)).toNat
def retain (d e : Nat) (xs ys : List L) :=
  let k := (xs.map (port true d)).toArray
  ys.filter fun y => k.contains (port false e y)
def step (s : Nat) (vert rev : Bool) (a : G) (r c : Nat) :=
  let x := if rev then s-1-r else r
  let y := if rev then s-1-c else c
  let t := if vert then r else c
  if t=0 then a else
    let i := if vert then (if rev then x+1 else x-1) else x
    let j := if vert then y else (if rev then y+1 else y-1)
    let d := vert.toNat+2*rev.toNat
    let v := retain d ((d+2)%4) (get a i j) (get a x y)
    a.setIfInBounds x ((a[x]?.getD #[]).setIfInBounds y v)
def pass (s : Nat) (v b : Bool) (A : G) :=
  (List.finRange s).foldl (fun G (r : Fin s) => (List.finRange s).foldl
    (fun H (c : Fin s) => step s v b H r c) G) A
def prune (s : Nat) : Nat → G → G
  | 0,A => A
  | t+1,A => prune s t (pass s true true (pass s false true (pass s true false (pass s false false A))))

def bonds (A B : List L) (d : Nat) : List Z := A.flatMap fun a =>
  (B.filter fun b => port true d a==port false (d+2) b).map (a,·)
def first (s : Nat) (v : Bool) (a : G) :=
  grid (s-v.toNat) (s-(!v).toNat) fun r c => bonds (get a r c) (get a (r+v.toNat) (c+(!v).toNat)) v.toNat
def key (v send : Bool) (d : Nat) (z : Z) :=
  if d%2=v.toNat then
    let a := if d<2 then z.2 else z.1
    5*a.1+a.2
  else 2048*port send d z.1+port send d z.2
def narrow (v : Bool) (d : Nat) (a b : List Z) :=
  let keys := Std.HashSet.ofList (a.map (key v true d))
  b.filter fun z => keys.contains (key v false ((d+2)%4) z)
def near (r c d : Nat) := match d with
  | 0 => (r,c+1) | 1 => (r+1,c) | 2 => (r,c-1) | _ => (r-1,c)
def fits (h w r c d : Nat) := match d with
  | 0 => c+1<w | 1 => r+1<h | 2 => 0<c | _ => 0<r
instance (h w r c d) : Decidable (fits h w r c d) := by unfold fits; split <;> infer_instance
def cut (h w : Nat) (v : Bool) (d : Nat) (a : S) (r c : Nat) :=
  let x := if d<2 then r else h-1-r
  let y := if d<2 then c else w-1-c
  let e := (d+2)%4
  if fits h w x y e then
    let z := near x y e
    a.setIfInBounds x ((a[x]?.getD #[]).setIfInBounds y (narrow v d (get a z.1 z.2) (get a x y)))
  else a
def ppass (h w : Nat) (v : Bool) (d : Nat) (a : S) :=
  (List.range h).foldl (fun b r => (List.range w).foldl (fun g c => cut h w v d g r c) b) a
def tighten (h w : Nat) (v : Bool) : Nat → S → S
  | 0,a => a
  | k+1,a =>
    let b := (List.range 4).foldl (fun g d => ppass h w v d g) a
    if a==b then b else tighten h w v k b
def drop (s : Nat) (v : Bool) (a : S) (b : G) := grid s s fun r c =>
  let dr := v.toNat; let dc := (!v).toNat
  let fore := Std.HashSet.ofList ((get a r c).map Prod.fst)
  let back := Std.HashSet.ofList ((get a (r-dr) (c-dc)).map Prod.snd)
  (get b r c).filter fun z =>
    (!(r+dr<s && c+dc<s) || fore.contains z) && (!(dr≤r && dc≤c) || back.contains z)
def sweep (s : Nat) (v : Bool) (k : Nat) (a : G) :=
  drop s v (tighten (s-v.toNat) (s-(!v).toNat) v k (first s v a)) a
def empty (s : Nat) (a : G) :=
  (List.finRange s).any fun (r : Fin s) => (List.finRange s).any fun (c : Fin s) => (get a r c).isEmpty
def run (s : Nat) (budget : Nat) (a : G) : Bool :=
  match budget with
  | 0 => empty s a
  | t+1 => let H := sweep s false 35 a
           empty s H || run s t (sweep s true 35 H)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.Kernel
