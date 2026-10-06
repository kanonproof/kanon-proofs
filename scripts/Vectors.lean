import KanonProofs.Lots
import KanonProofs.Reference
/-! Writes the reference vectors: `lake env lean scripts/Vectors.lean` prints one JSON document per engine. -/
open Kanon

/-- A small deterministic generator, so the vectors never change unless a model changes. -/
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random numbers below `bound`, and the next seed. -/
def draws (s : Nat) (n bound : Nat) : List Nat × Nat :=
  (List.range n).foldl (fun (acc, s) _ => let s' := lcg s; (acc ++ [s' % bound], s')) ([], s)

def jlist (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def brCases : String := Id.run do
  let mut s := 7
  let mut out : List String := []
  for i in [0:240] do
    let (k, s1) := draws s 1 4; s := s1
    let n := k.head! + 1
    -- Mostly everyday amounts; every fifth case reaches the higher bands.
    let bound := if i % 5 == 0 then 4000000000 else 4000000
    let (vs, s2) := draws s n bound; s := s2
    let (cs, s3) := draws s n bound; s := s3
    let sales := (vs.zip cs).map fun (v, c) => Reference.Sale.mk v c
    let js := sales.map fun x => s!"\{\"value\": {x.value}, \"cost\": {x.cost}}"
    out := out ++ [s!"\{\"sales\": {jlist js}, \"bp\": {Reference.brMonthBp sales}}"]
  return jlist out

def toInt (n : Nat) (half : Nat) : Int := (n : Int) - half

def zaCases : String := Id.run do
  let mut s := 11
  let mut out : List String := []
  for i in [0:240] do
    let (k, s1) := draws s 1 4; s := s1
    let (gs, s2) := draws s (k.head! + 1) 60000000; s := s2
    let gains := gs.map (toInt · 30000000)
    let (b, s3) := draws s 1 6000000; s := s3
    let excl := if i % 2 == 0 then 5000000 else 4000000
    let bf := if i % 3 == 0 then 0 else b.head!
    let r := Reference.zaYear gains excl bf
    out := out ++ [s!"\{\"gains\": {jlist (gains.map toString)}, \"exclusion\": {excl}, \"broughtForward\": {bf}, \"aggregate\": {r.aggregate}, \"assessedLoss\": {r.assessedLoss}, \"net\": {r.net}}"]
  return jlist out

def lotCases : String := Id.run do
  let mut s := 13
  let mut out : List String := []
  for _ in [0:240] do
    let (k, s1) := draws s 1 4; s := s1
    let n := k.head! + 1
    let (qs, s2) := draws s n 1000000; s := s2
    let (cs, s3) := draws s n 100000000; s := s3
    let lots := (List.range n).map fun j => Lots.Lot.mk j (qs[j]! + 1) cs[j]!
    let total := lots.foldl (fun a l => a + l.qty) 0
    let (q, s4) := draws s 1 (total + total / 4 + 1); s := s4
    let r := Lots.sell lots q.head!
    let js := lots.map fun l => s!"\{\"acquired\": {l.acquired}, \"qty\": {l.qty}, \"cost\": {l.cost}}"
    out := out ++ [s!"\{\"lots\": {jlist js}, \"sell\": {q.head!}, \"sold\": {r.1}, \"cost\": {r.2.1}, \"leftQty\": {Lots.totalQty r.2.2}, \"leftCost\": {Lots.totalCost r.2.2}}"]
  return jlist out

#eval IO.println s!"\{\"br\": {brCases},\n\"za\": {zaCases},\n\"lots\": {lotCases}}"
