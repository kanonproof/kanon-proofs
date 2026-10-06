/-!
# Lots: conservation (#3) and own-wallet moves (#4)

Model of KANON's lot ledger (`src/lib/engine/lots.ts`). Quantities are whole smallest units
(satoshis, wei) and costs whole cents, so every equation is exact.

A sale takes coins oldest-first. A partly used lot keeps `cost - slicedCost`, exactly as the
production code does, so no cent of cost is created or lost.
-/

namespace Kanon.Lots

structure Lot where
  acquired : Nat   -- day number
  qty : Nat
  cost : Nat
  deriving Repr, DecidableEq

def totalQty : List Lot → Nat
  | [] => 0
  | l :: ls => l.qty + totalQty ls

def totalCost : List Lot → Nat
  | [] => 0
  | l :: ls => l.cost + totalCost ls

/-- Cost of taking `t` coins out of a lot: proportional, rounded down. -/
def sliceCost (l : Lot) (t : Nat) : Nat := l.cost * t / l.qty

theorem sliceCost_le (l : Lot) (t : Nat) (h : t ≤ l.qty) : sliceCost l t ≤ l.cost := by
  unfold sliceCost
  rcases Nat.eq_zero_or_pos l.qty with hq | hq
  · simp [hq]
  · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm l.qty]; exact Nat.mul_le_mul_left _ h)

/-- Sell `q` coins oldest-first. Returns (coins sold, cost of the coins sold, lots left). -/
def sell : List Lot → Nat → Nat × Nat × List Lot
  | [], _ => (0, 0, [])
  | l :: ls, q =>
    if q = 0 then (0, 0, l :: ls)
    else if q < l.qty then
      (q, sliceCost l q, { l with qty := l.qty - q, cost := l.cost - sliceCost l q } :: ls)
    else
      let r := sell ls (q - l.qty)
      (l.qty + r.1, l.cost + r.2.1, r.2.2)

/-- **#3 Lot conservation (quantity).** Coins sold + coins left = coins before. -/
theorem sell_qty (ls : List Lot) (q : Nat) :
    (sell ls q).1 + totalQty (sell ls q).2.2 = totalQty ls := by
  induction ls generalizing q with
  | nil => simp [sell, totalQty]
  | cons l ls ih =>
    unfold sell
    by_cases h0 : q = 0
    · simp [h0, totalQty]
    · by_cases hlt : q < l.qty
      · simp [h0, hlt, totalQty]; omega
      · simp only [h0, hlt, if_false]
        have := ih (q - l.qty)
        simp [totalQty]; omega

/-- **#3 Lot conservation (cost).** Cost of coins sold + cost still held = cost before. -/
theorem sell_cost (ls : List Lot) (q : Nat) :
    (sell ls q).2.1 + totalCost (sell ls q).2.2 = totalCost ls := by
  induction ls generalizing q with
  | nil => simp [sell, totalCost]
  | cons l ls ih =>
    unfold sell
    by_cases h0 : q = 0
    · simp [h0, totalCost]
    · by_cases hlt : q < l.qty
      · have := sliceCost_le l q (Nat.le_of_lt hlt)
        simp [h0, hlt, totalCost]; omega
      · simp only [h0, hlt, if_false]
        have := ih (q - l.qty)
        simp [totalCost]; omega

/-- **#3** A sale never sells more than is held, and sells exactly `q` when enough is held. -/
theorem sell_exact (ls : List Lot) (q : Nat) (h : q ≤ totalQty ls) : (sell ls q).1 = q := by
  induction ls generalizing q with
  | nil => simp [totalQty] at h; simp [sell, h]
  | cons l ls ih =>
    unfold sell
    by_cases h0 : q = 0
    · simp [h0]
    · by_cases hlt : q < l.qty
      · simp [h0, hlt]
      · simp only [h0, hlt, if_false]
        have := ih (q - l.qty) (by simp [totalQty] at h; omega)
        omega

theorem sell_le (ls : List Lot) (q : Nat) : (sell ls q).1 ≤ totalQty ls := by
  have := sell_qty ls q; omega

/-! ## #4 Moving coins between your own wallets -/

structure Held where
  wallet : Nat
  lot : Lot
  deriving Repr, DecidableEq

/-- A move between the user's own wallets relabels the wallet and touches nothing else. -/
def move (to : Nat) (hs : List Held) : List Held := hs.map fun h => { h with wallet := to }

/-- **#4** A move is never a sale: every lot keeps its date, quantity and cost. -/
theorem move_keeps_lots (to : Nat) (hs : List Held) : (move to hs).map Held.lot = hs.map Held.lot := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [move] at *

/-- **#4** After a move, every lot is in the destination wallet. -/
theorem move_dest (to : Nat) (hs : List Held) : ∀ h ∈ move to hs, h.wallet = to := by
  intro h hm; simp [move] at hm; obtain ⟨x, _, rfl⟩ := hm; rfl

/-- Matching arrivals to departures: each arrival can be used once. Greedy, like the money map. -/
def matchOnce (p : Nat → Nat → Bool) : List Nat → List Nat → List (Nat × Nat)
  | [], _ => []
  | o :: os, ins =>
    match ins.find? (p o) with
    | some i => (o, i) :: matchOnce p os (ins.erase i)
    | none => matchOnce p os ins

theorem matchOnce_sub (p : Nat → Nat → Bool) (os ins : List Nat) :
    ∀ x ∈ (matchOnce p os ins).map Prod.snd, x ∈ ins := by
  induction os generalizing ins with
  | nil => simp [matchOnce]
  | cons o os ih =>
    simp only [matchOnce]
    split
    · next i hi =>
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨a, ha⟩
      · exact List.mem_of_find?_eq_some hi
      · exact List.mem_of_mem_erase (ih _ x (by simp; exact ⟨a, ha⟩))
    · exact ih ins

/-- **#4** Each transfer matches once: no arrival is paired with two departures. -/
theorem matchOnce_nodup (p : Nat → Nat → Bool) (os ins : List Nat) (h : ins.Nodup) :
    ((matchOnce p os ins).map Prod.snd).Nodup := by
  induction os generalizing ins with
  | nil => simp [matchOnce]
  | cons o os ih =>
    simp only [matchOnce]
    split
    · next i hi =>
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih _ (h.erase i)⟩
      exact (List.Nodup.not_mem_erase h) (matchOnce_sub p os (ins.erase i) i hm)
    · exact ih ins h

end Kanon.Lots
