import Std

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary.Kernel
abbrev Grid := Array (Array (List Nat))
def get (G : Grid) (r c : Nat) := (G[r]!)[c]!
def key (d m : Nat) := match d with
  | 0 => m &&& 438 | 1 => m &&& 504 | 2 => (m &&& 219) <<< 1 | _ => (m &&& 63) <<< 3
def keys (d : Nat) (xs : List Nat) := Std.HashSet.ofList (xs.map (key d))
def pass (h w : Nat) (G : Grid) : Grid :=
  Array.ofFn fun r : Fin h => Array.ofFn fun c : Fin w =>
    let n := keys 1 (get G (r.val-1) c)
    let s := keys 3 (get G (min (h-1) (r.val+1)) c)
    let l := keys 0 (get G r (c.val-1))
    let e := keys 2 (get G r (min (w-1) (c.val+1)))
    (get G r c).filter fun m =>
      (r.val==0 || n.contains (key 3 m)) && (r.val+1==h || s.contains (key 1 m)) &&
      (c.val==0 || l.contains (key 2 m)) && (c.val+1==w || e.contains (key 0 m))
def prune (h w : Nat) : Nat → Grid → Grid
  | 0,G => G
  | n+1,G => prune h w n (pass h w G)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary.Kernel
