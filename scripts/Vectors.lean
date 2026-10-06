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


/-- 2026 figures (Rev. Proc. 2025-32), in cents. -/
def us2026 : List (String × Reference.UsSchedule) := [
  ("single", ⟨[(1240000, 1000), (5040000, 1200), (10570000, 2200), (20177500, 2400), (25622500, 3200), (64060000, 3500)], 3700, 4945000, 54550000⟩),
  ("mfj", ⟨[(2480000, 1000), (10080000, 1200), (21140000, 2200), (40355000, 2400), (51245000, 3200), (76870000, 3500)], 3700, 9890000, 61370000⟩)]

def usCases : String := Id.run do
  let mut s := 17
  let mut out : List String := []
  for i in [0:240] do
    let (st, sch) := us2026[i % 2]!
    let (t, s1) := draws s 1 (if i % 3 == 0 then 90000000 else 10000000); s := s1
    let taxable := t.head!
    let (g, s2) := draws s 1 (taxable + 1); s := s2
    let gain := if i % 4 == 0 then 0 else g.head!
    out := out ++ [s!"\{\"status\": \"{st}\", \"taxable\": {taxable}, \"gain\": {gain}, \"bp\": {Reference.usBp taxable gain sch}, \"regularBp\": {Reference.regularBp taxable sch}}"]
  return jlist out

def jpCases : String := Id.run do
  let mut s := 19
  let mut out : List String := []
  for _ in [0:240] do
    let (o, s1) := draws s 2 1000000; s := s1
    let openQty := o[0]!
    let openCost := if openQty == 0 then 0 else o[1]! * 3
    let (k, s2) := draws s 1 6; s := s2
    let mut held := openQty
    let mut ts : List Reference.JpTrade := []
    let mut js : List String := []
    for _ in [0:k.head! + 1] do
      let (r, s3) := draws s 3 1000000; s := s3
      if r[0]! % 2 == 0 || held == 0 then
        let q := r[1]! + 1
        ts := ts ++ [.buy q (r[2]! * 5)]; js := js ++ [s!"\{\"kind\": \"buy\", \"qty\": {q}, \"cost\": {r[2]! * 5}}"]; held := held + q
      else
        let q := r[1]! % held + 1
        ts := ts ++ [.sell q]; js := js ++ [s!"\{\"kind\": \"sell\", \"qty\": {q}}"]; held := held - q
    let (tn, td) := Reference.jpTotal openQty openCost ts
    let (mn, md) := Reference.jpMoving openQty openCost ts
    out := out ++ [s!"\{\"openQty\": {openQty}, \"openCost\": {openCost}, \"trades\": {jlist js}, \"total\": [\"{tn}\", \"{td}\"], \"moving\": [\"{mn}\", \"{md}\"]}"]
  return jlist out

def ukCases : String := Id.run do
  let mut s := 23
  let mut out : List String := []
  for _ in [0:240] do
    let (k, s1) := draws s 1 6; s := s1
    let mut day := 0
    let mut days : List Reference.UkDay := []
    for j in [0:k.head! + 2] do
      let (r, s2) := draws s 6 100000; s := s2
      day := day + r[0]! % 25 + (if j == 0 then 0 else 1)
      let buy := if r[1]! % 3 == 0 then 0 else r[2]! + 1
      let sell := if j == 0 || r[3]! % 2 == 0 then 0 else r[4]! % 90000 + 1
      days := days ++ [⟨day, buy, buy * (r[5]! % 50 + 1), sell, sell * (r[5]! % 70 + 1)⟩]
    let r := Reference.ukMatch days
    let jd := days.map fun d => s!"\{\"day\": {d.day}, \"buy\": {d.buy}, \"buyCost\": {d.buyCost}, \"sell\": {d.sell}, \"proceeds\": {d.proceeds}}"
    let jo := r.disposals.map fun (d, q, p, c) => s!"\{\"day\": {d}, \"sold\": {q}, \"proceeds\": {p}, \"cost\": {c}}"
    out := out ++ [s!"\{\"days\": {jlist jd}, \"disposals\": {jlist jo}, \"poolQty\": {r.poolQty}, \"poolCost\": {r.poolCost}}"]
  return jlist out

def thCases : String := Id.run do
  let mut s := 29
  let mut out : List String := []
  for i in [0:240] do
    let (r, s1) := draws s 3 600000000; s := s1
    let net := if i % 5 == 0 then r[0]! % 20000000 else r[0]!
    let a := if i % 3 == 0 then 0 else r[1]! % 400000000
    out := out ++ [s!"\{\"net\": {net}, \"other\": {a}, \"bp\": {Reference.thTaxBp net a}}"]
  return jlist out

#eval IO.println s!"\{\"br\": {brCases},\n\"za\": {zaCases},\n\"lots\": {lotCases},\n\"us\": {usCases},\n\"jp\": {jpCases},\n\"uk\": {ukCases},\n\"th\": {thCases}}"
