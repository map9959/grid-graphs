import GridGraphs.Constructions.ResidueTwo.LowerTurnRegion

namespace GridGraphs.ResidueTwoLower.Poly

private inductive Item | e (v : Exp) | p (v : Region)

private def consume (xs : List Item) (s : String) : Option (List Item) :=
  match s,xs with
  | "F",_ => some (.p .no::xs) | "T",_ => some (.p .yes::xs)
  | "t",_ => some (.e .t::xs) | "i",_ => some (.e .i::xs) | "j",_ => some (.e .j::xs)
  | "&",.p b::.p a::ls => some (.p (.both a b)::ls)
  | "|",.p b::.p a::ls => some (.p (.either a b)::ls)
  | "G",.e b::.e a::ls => some (.p (.ge a b)::ls)
  | "L",.e b::.e a::ls => some (.p (.ge b a)::ls)
  | "=", .e b::.e a::ls => some (.p (.both (.ge a b) (.ge b a))::ls)
  | "g",.e b::.e a::ls => some (.p (.ge a (.add b (.lit 1)))::ls)
  | "l",.e b::.e a::ls => some (.p (.ge b (.add a (.lit 1)))::ls)
  | "~",.e a::ls => some (.e (.mul (-1) a)::ls)
  | "+",.e b::.e a::ls => some (.e (.add a b)::ls)
  | "-",.e b::.e a::ls => some (.e (.add a (.mul (-1) b))::ls)
  | "*",.e b::.e (.lit k)::ls => some (.e (.mul k b)::ls)
  | "*",.e (.lit k)::.e b::ls => some (.e (.mul k b)::ls)
  | "/",.e (.lit k)::.e b::ls => some (.e (.div b k)::ls)
  | "%",.e (.lit k)::.e b::ls => some (.e (.mod b k)::ls)
  | _,_ => return .e (.lit (←s.toInt?))::xs

def parse (s : String) : Option Region := do
  let [.p p] ← (s.splitOn " ").foldlM consume [] | none
  return p

abbrev Chart := Array (Array Region)

def decode (s : String) : Option Chart := do
  let ps ← (s.trimAscii.toString.splitOn "\n").mapM parse
  guard (ps.length%4==0)
  return ((List.range (ps.length/4)).map (fun i => ((ps.drop (4*i)).take 4).toArray)).toArray

def rid : Turn.Dir → Nat
  | .east => 0 | .south => 1 | .west => 2 | .north => 3

def offset : Turn.Dir → ℤ × ℤ
  | .east => (0,1) | .south => (1,0) | .west => (0,-1) | .north => (-1,0)

def Reg (chart : Chart) (k : Nat) (d : Turn.Dir) : Region :=
  ((chart[k]?).bind (fun a => a[rid d]?)).getD .no

def allowed (chart : Chart) (s : Nat) (d : Turn.Dir) (t : ℤ) (v : Turn.Pt) :=
  (Reg chart s d).eval t v.1 v.2

/- Check all locally dangerous edges. Because the encoded interior layers
may have been simplified on the forced-edge domain, both endpoints of
the transition must be in layer zero. -/
def trial (chart : Chart) (s : Nat) (d e : Turn.Dir) (straight : Bool) : List Lit :=
  let o := offset d
  [⟨Reg chart 0 d,0,0,true⟩,⟨Reg chart 0 e,o.1,o.2,true⟩,
   ⟨Reg chart (if straight then s+1 else s) e,o.1,o.2,true⟩,
   ⟨Reg chart (s+1) d,0,0,false⟩]

def dirs := [Turn.Dir.east,.south,.west,.north]

def chartOK (chart : Chart) : Bool :=
  (List.range chart.size).all fun s => dirs.all fun d =>
    check (trial chart s d d true) && check (trial chart s d (Turn.turnL d) false)
      && check (trial chart s d (Turn.turnR d) false)

/-- Slice syntax used to replay only a selected range of layers without
changing the soundness theorem for the full ordered chart. -/
def layerOK (chart : Chart) (s : Nat) : Bool :=
  dirs.all fun d => check (trial chart s d d true) &&
    check (trial chart s d (Turn.turnL d) false) &&
    check (trial chart s d (Turn.turnR d) false)

theorem chartOK_iff (chart : Chart) : chartOK chart=true ↔
    ∀ s<chart.size, layerOK chart s=true := by simp [chartOK,layerOK]

end GridGraphs.ResidueTwoLower.Poly
