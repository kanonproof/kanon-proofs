import KanonProofs.Lots
import KanonProofs.CashOut
import KanonProofs.FeeSplit
import KanonProofs.ReserveCap
import KanonProofs.Ladder
import KanonProofs.Completeness
import KanonProofs.HoldCheck
import KanonProofs.Payments
import KanonProofs.Brackets
import KanonProofs.Years
import KanonProofs.UkMatch
import KanonProofs.Matching
import KanonProofs.Guard
import KanonProofs.Reference
import KanonProofs.Rounding
import KanonProofs.PriceImpact
import KanonProofs.Grouping
import KanonProofs.Fresh
import KanonProofs.Rotation
import KanonProofs.Grade
import KanonProofs.LookAhead
import KanonProofs.Spread
import KanonProofs.Ranking
import KanonProofs.StockToken
import KanonProofs.Split

/-!
# Tightened models and gap-closing theorems

This file closes the gaps listed in `AUDIT.md`. It imports every module that the root file `KanonProofs.lean`
imports (it cannot import the root `KanonProofs` itself, because the root imports this file: that would be an
import cycle), so it sees exactly the same definitions.

* Part A: the six gap-closing theorems of the audit, re-proved against the current files.
* Part B: for findings F1, F5, F6, F8, F9, F12, F3 and F2, a stronger model (new names, next to the old one), or
  the explicit hypothesis under which the old definition already behaves, with the property the README promises.

No existing definition or theorem is changed.
-/

namespace Kanon.Tightened

/-! ## Part A — gap-closing theorems carried over from the audit -/

section PartA

open Kanon.LookAhead in
theorem foldl_max_ge (p : Nat → Nat) : ∀ (l : List Nat) (acc : Nat),
    acc ≤ l.foldl (fun m d => max m (p d)) acc ∧ ∀ d ∈ l, p d ≤ l.foldl (fun m d => max m (p d)) acc
  | [], acc => by simp
  | x :: xs, acc => by
    obtain ⟨h1, h2⟩ := foldl_max_ge p xs (max acc (p x))
    refine ⟨by simp only [List.foldl]; omega, ?_⟩
    intro d hd
    simp only [List.foldl, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · omega
    · exact h2 d hd

open Kanon.LookAhead in
/-- **#15, stronger than `peak_attained`.** For a non-empty window the best price is always one of the
prices in the window (no "or 0" escape). -/
theorem peak_attained_nonempty (p : Nat → Nat) (start t : Nat) (h : start ≤ t) :
    ∃ d, start ≤ d ∧ d ≤ t ∧ peak p start t = p d := by
  rcases peak_attained p start t with h0 | h1
  · refine ⟨start, Nat.le_refl _, h, ?_⟩
    have := (foldl_max_ge p (List.range' start (t + 1 - start)) 0).2 start
      (by rw [List.mem_range'_1]; omega)
    unfold peak at h0 ⊢
    omega
  · exact h1

open Kanon.Grouping in
theorem flatten_insert_perm (m : Mv) :
    ∀ g : List (Nat × List Mv), (flatten (Kanon.Grouping.insert m g)).Perm (m :: flatten g)
  | [] => by simp [Kanon.Grouping.insert, flatten]
  | (k, ms) :: rest => by
    unfold Kanon.Grouping.insert
    split
    · simp [flatten]
    · simp only [flatten]
      exact ((flatten_insert_perm m rest).append_left ms).trans List.perm_middle

open Kanon.Grouping in
/-- **#27, stronger than `group_keeps_count`.** The piles hold exactly the file's movements, rearranged:
nothing dropped, nothing duplicated, nothing altered. -/
theorem group_perm (ms : List Mv) : (flatten (group ms)).Perm ms := by
  induction ms with
  | nil => simp [group, flatten]
  | cons m ms ih => exact (flatten_insert_perm m _).trans (ih.cons m)

open Kanon.Rotation in
/-- **#31.** "No part exceeds the whole" holds on the new-cost side too. -/
theorem new_cost_part_at_most_price (s : Swap) : ∀ p ∈ newCost s, p ≤ s.T := parts_le _ _ _ _

open Kanon.PriceImpact in
/-- **#12.** A pool holding coins and cash is never fully drained by one sale. -/
theorem payout_lt_reserve (B Q q k : Nat) (hB : 0 < B) (hQ : 0 < Q) : payout B Q q k < Q := by
  unfold payout
  have hd : 0 < denom B q k := by unfold denom; have := Nat.mul_pos (by decide : 0 < 10000) hB; omega
  apply Nat.div_lt_of_lt_mul
  have : 0 < 10000 * B * Q := Nat.mul_pos (Nat.mul_pos (by decide) hB) hQ
  have e : denom B q k * Q = 10000 * B * Q + Q * (q * k) := by
    unfold denom; rw [Nat.add_mul, Nat.mul_comm (q * k) Q]
  rw [e]; omega

open Kanon.Rounding in
/-- **#6.** Exactly half a cent rounds up, just under half rounds down, and rounding up never adds a cent to an
exact amount. -/
theorem rounding_spot_checks :
    halfUp 100 50 = 1 ∧ halfUp 100 49 = 0 ∧ halfUp 100 150 = 2 ∧ up 100 200 = 2 ∧ up 100 201 = 3 := by
  decide

open Kanon.Ladder in
/-- **#21.** The UK tax year is right for every day: January to 5 April belong to the year before,
6 April to December to the year itself. -/
theorem uk_tax_year_all_days (y m d : Nat) :
    ukTaxYear y m d = if m < 4 ∨ (m = 4 ∧ d ≤ 5) then y - 1 else y := by
  unfold ukTaxYear
  by_cases h1 : m < 4 ∨ (m = 4 ∧ d ≤ 5)
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1, if_pos (by omega)]

end PartA

/-! ## Part B — stronger models -/

/-! ### F1 (#10, #11): the chosen cash-out plan is valid, sells the amount asked, and is no dearer than the default -/

section F1
open Kanon.Lots Kanon.CashOut

/-- A computable check for `Valid`: lot numbers distinct, each names an existing lot and sells at most what it holds. -/
def validB (lots : List Lot) (p : Plan) : Bool :=
  decide ((p.map Prod.fst).Nodup) && p.all (fun s => match lots[s.1]? with
    | some l => decide (s.2 ≤ l.qty)
    | none => false)

theorem validB_iff (lots : List Lot) (p : Plan) : validB lots p = true ↔ Valid lots p := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Valid]
  refine and_congr Iff.rfl (forall_congr' fun s => imp_congr_right fun _ => ?_)
  cases hl : lots[s.1]? with
  | none => simp
  | some l => simp

/-- A candidate the planner may pick: valid, and selling exactly the `q` coins asked for. -/
def admissible (lots : List Lot) (q : Nat) (p : Plan) : Bool := validB lots p && planQty p == q

/-- **The tightened planner.** The cheapest plan among the admissible candidates, starting from the
oldest-first plan (which is therefore always in the running). -/
def safePlan (tax : Plan → Nat) (lots : List Lot) (q : Nat) (cands : List Plan) : Plan :=
  cheapest tax (fifoPlan lots 0 q) (cands.filter (admissible lots q))

theorem cheapest_eq_pick (tax : Plan → Nat) : ∀ (best : Plan) (cs : List Plan),
    cheapest tax best cs = Kanon.Split.pick tax best cs
  | _, [] => rfl
  | best, c :: cs => by simp only [cheapest, Kanon.Split.pick]; exact cheapest_eq_pick tax _ cs

/-- The planner returns the oldest-first plan or one of the admissible candidates. -/
theorem safePlan_mem (tax : Plan → Nat) (lots : List Lot) (q : Nat) (cands : List Plan) :
    safePlan tax lots q cands = fifoPlan lots 0 q ∨ admissible lots q (safePlan tax lots q cands) = true := by
  have h := Kanon.Split.pick_mem tax (fifoPlan lots 0 q) (cands.filter (admissible lots q))
  rw [← cheapest_eq_pick] at h
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mp h).2

/-- **F1, #10 for the chosen plan.** The plan the planner shows is always valid. -/
theorem safePlan_valid (tax : Plan → Nat) (lots : List Lot) (q : Nat) (cands : List Plan) :
    Valid lots (safePlan tax lots q cands) := by
  rcases safePlan_mem tax lots q cands with h | h
  · rw [h]; exact fifoPlan_valid lots q
  · simp only [admissible, Bool.and_eq_true] at h
    exact (validB_iff _ _).mp h.1

/-- **F1, #10 for the chosen plan.** When the coins are there, the plan shown sells exactly the amount asked. -/
theorem safePlan_qty (tax : Plan → Nat) (lots : List Lot) (q : Nat) (cands : List Plan)
    (h : q ≤ totalQty lots) : planQty (safePlan tax lots q cands) = q := by
  rcases safePlan_mem tax lots q cands with e | e
  · rw [e]; exact fifoPlan_hits lots 0 q h
  · simp only [admissible, Bool.and_eq_true, beq_iff_eq] at e
    exact e.2

/-- **F1, #11 for the chosen plan.** Its tax is never higher than the oldest-first default's. -/
theorem safePlan_le_default (tax : Plan → Nat) (lots : List Lot) (q : Nat) (cands : List Plan) :
    tax (safePlan tax lots q cands) ≤ tax (fifoPlan lots 0 q) :=
  cheapest_le_start _ _ _

/-- **F1.** And it is no dearer than any admissible candidate it was offered. -/
theorem safePlan_le_admissible (tax : Plan → Nat) (lots : List Lot) (q : Nat) (cands : List Plan)
    (c : Plan) (hc : c ∈ cands) (ha : admissible lots q c = true) :
    tax (safePlan tax lots q cands) ≤ tax c := by
  unfold safePlan; rw [cheapest_eq_pick]
  exact Kanon.Split.pick_le tax _ _ c (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, ha⟩))

/-- **F1.** The audit's two counterexamples no longer happen: the empty plan and the plan naming a lot that does
not exist are both refused, and the oldest-first plan is shown. -/
theorem safePlan_refuses_audit_examples :
    let lots : List Lot := [⟨1, 100, 5000⟩]
    let default := fifoPlan lots 0 50
    safePlan planQty lots 50 [[]] = default ∧
    safePlan (fun p => if p = default then 1 else 0) lots 50 [[(7, 50)]] = default := by
  decide

end F1

/-! ### F5 (#5): an average-cost sale that can never take more coins or cost than the pool holds -/

section F5
open Kanon.Matching

/-- Coins a capped sale of `q` actually takes: never more than the pool holds. -/
def avgQtySafe (p : Pool) (q : Nat) : Nat := min q p.qty

/-- Cost taken by the capped sale. -/
def avgTakeSafe (p : Pool) (q : Nat) : Nat := avgTake p (avgQtySafe p q)

/-- The pool after the capped sale. -/
def avgSellSafe (p : Pool) (q : Nat) : Pool := avgSell p (avgQtySafe p q)

/-- **F5.** For every `q`, the capped sale takes no more coins than the pool holds. -/
theorem avgSafe_qty_le (p : Pool) (q : Nat) : avgQtySafe p q ≤ p.qty := Nat.min_le_right _ _

/-- **F5.** For every `q`, the capped sale takes no more cost than the pool holds. -/
theorem avgSafe_cost_le (p : Pool) (q : Nat) : avgTakeSafe p q ≤ p.cost := by
  have := avg_conserves p (avgQtySafe p q) (avgSafe_qty_le p q)
  unfold avgTakeSafe; omega

/-- **F5.** For every `q`, coins taken plus coins left is exactly the pool's coins. -/
theorem avgSafe_qty_conserves (p : Pool) (q : Nat) : avgQtySafe p q + (avgSellSafe p q).qty = p.qty := by
  have := avgSafe_qty_le p q
  simp only [avgSellSafe, avgSell]; omega

/-- **F5.** For every `q`, cost taken plus cost left is exactly the pool's cost. -/
theorem avgSafe_cost_conserves (p : Pool) (q : Nat) : avgTakeSafe p q + (avgSellSafe p q).cost = p.cost :=
  avg_conserves p _ (avgSafe_qty_le p q)

/-- **F5.** For every `q`, what is left keeps the pool's average price (as `avg_kept`, with no `q ≤ qty`). -/
theorem avgSafe_kept (p : Pool) (q : Nat) (hn : 0 < p.qty) :
    p.cost * (p.qty - avgQtySafe p q) ≤ (avgSellSafe p q).cost * p.qty ∧
    (avgSellSafe p q).cost * p.qty < p.cost * (p.qty - avgQtySafe p q) + p.qty :=
  avg_kept p _ (avgSafe_qty_le p q) hn

/-- **F5.** When the pool holds enough, the capped sale is exactly the old one. -/
theorem avgSafe_eq_old (p : Pool) (q : Nat) (h : q ≤ p.qty) :
    avgQtySafe p q = q ∧ avgTakeSafe p q = avgTake p q ∧ avgSellSafe p q = avgSell p q := by
  have e : avgQtySafe p q = q := Nat.min_eq_left h
  simp only [avgTakeSafe, avgSellSafe, e, and_self]

/-- **F5.** The audit's example: selling 20 from a pool of 10 coins costing 1,000 now takes 10 coins and 1,000. -/
theorem avgSafe_audit_example :
    avgQtySafe ⟨10, 1000⟩ 20 = 10 ∧ avgTakeSafe ⟨10, 1000⟩ 20 = 1000 := by decide

end F5

/-! ### F6 (#5): oldest first by acquisition date -/

section F6
open Kanon.Lots

/-- How many lots (from the front of the list) an oldest-first sale of `q` touches. -/
def usedLen : List Lot → Nat → Nat
  | [], _ => 0
  | l :: ls, q => if q = 0 then 0 else if q < l.qty then 1 else usedLen ls (q - l.qty) + 1

/-- The structure of a sale: the lots after the first `usedLen` are left exactly as they were; the lots
before supply every coin sold, and at most one of them survives, cut down, with the same date. -/
theorem sell_used_untouched (ls : List Lot) (q : Nat) :
    ∃ cut : List Lot, cut.length ≤ 1 ∧
      (sell ls q).2.2 = cut ++ ls.drop (usedLen ls q) ∧
      (sell ls q).1 + totalQty cut = totalQty (ls.take (usedLen ls q)) ∧
      ∀ c ∈ cut, ∃ u ∈ ls.take (usedLen ls q), c.acquired = u.acquired := by
  induction ls generalizing q with
  | nil => exact ⟨[], by simp, by simp [sell, usedLen], by simp [sell, usedLen, totalQty], by simp⟩
  | cons l ls ih =>
    by_cases h0 : q = 0
    · exact ⟨[], by simp, by simp [sell, usedLen, h0], by simp [sell, usedLen, h0, totalQty], by simp⟩
    · by_cases hlt : q < l.qty
      · refine ⟨[{ l with qty := l.qty - q, cost := l.cost - sliceCost l q }], by simp,
          by simp [sell, usedLen, h0, hlt], ?_, ?_⟩
        · simp [sell, usedLen, h0, hlt, totalQty]; omega
        · simp [usedLen, h0, hlt]
      · obtain ⟨cut, hlen, hrest, hqty, hdate⟩ := ih (q - l.qty)
        refine ⟨cut, hlen, ?_, ?_, ?_⟩
        · simp only [sell, usedLen, h0, hlt, if_false, List.drop_succ_cons]; exact hrest
        · simp only [sell, usedLen, h0, hlt, if_false, List.take_succ_cons, totalQty]; omega
        · intro c hc
          obtain ⟨u, hu, e⟩ := hdate c hc
          refine ⟨u, ?_, e⟩
          simp only [usedLen, h0, hlt, if_false, List.take_succ_cons]
          exact List.mem_cons_of_mem _ hu

/-- Lots sorted oldest first (by acquisition day). -/
def SortedByDate (ls : List Lot) : Prop := ls.Pairwise (fun a b => a.acquired ≤ b.acquired)

/-- **F6 (on the old `sell`, under an explicit sortedness hypothesis).** If the lots are sorted by acquisition
date, every lot an oldest-first sale leaves untouched was acquired no earlier than every lot it used. -/
theorem sell_untouched_not_older (ls : List Lot) (q : Nat) (hs : SortedByDate ls) :
    ∀ u ∈ ls.take (usedLen ls q), ∀ v ∈ ls.drop (usedLen ls q), u.acquired ≤ v.acquired := by
  have h := hs
  unfold SortedByDate at h
  rw [← List.take_append_drop (usedLen ls q) ls, List.pairwise_append] at h
  exact h.2.2

/-- The lots in acquisition-date order. -/
def byDate (ls : List Lot) : List Lot := ls.mergeSort (fun a b => decide (a.acquired ≤ b.acquired))

theorem byDate_sorted (ls : List Lot) : SortedByDate (byDate ls) := by
  have := List.pairwise_mergeSort (le := fun a b : Lot => decide (a.acquired ≤ b.acquired))
    (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) ls
  simpa [SortedByDate, byDate] using this

theorem totalQty_perm {a b : List Lot} (h : a.Perm b) : totalQty a = totalQty b := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [totalQty, ih]
  | swap x y l => simp [totalQty]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem totalCost_perm {a b : List Lot} (h : a.Perm b) : totalCost a = totalCost b := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [totalCost, ih]
  | swap x y l => simp [totalCost]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The tightened oldest-first sale.** Sorts the lots by acquisition date first, then sells oldest first. -/
def sellByDate (ls : List Lot) (q : Nat) : Nat × Nat × List Lot := sell (byDate ls) q

/-- **F6.** With no hypothesis on the input order: every lot `sellByDate` leaves untouched was acquired no
earlier than every lot it used. -/
theorem sellByDate_untouched_not_older (ls : List Lot) (q : Nat) :
    ∀ u ∈ (byDate ls).take (usedLen (byDate ls) q), ∀ v ∈ (byDate ls).drop (usedLen (byDate ls) q),
      u.acquired ≤ v.acquired :=
  sell_untouched_not_older _ q (byDate_sorted ls)

/-- **F6.** Sorting first keeps conservation: coins and cost sold plus left equal what the user held. -/
theorem sellByDate_conserves (ls : List Lot) (q : Nat) :
    (sellByDate ls q).1 + totalQty (sellByDate ls q).2.2 = totalQty ls ∧
    (sellByDate ls q).2.1 + totalCost (sellByDate ls q).2.2 = totalCost ls := by
  have hp := List.mergeSort_perm ls (fun a b : Lot => decide (a.acquired ≤ b.acquired))
  refine ⟨?_, ?_⟩
  · rw [← totalQty_perm hp]; exact sell_qty _ q
  · rw [← totalCost_perm hp]; exact sell_cost _ q

/-- **F6.** The audit's example: with lots `[day 30, day 1]`, the sale of 5 now takes the day-1 lot. -/
theorem sellByDate_audit_example :
    sellByDate [⟨30, 5, 500⟩, ⟨1, 5, 100⟩] 5 = (5, 100, [⟨30, 5, 500⟩]) := by
  simp [sellByDate, byDate, List.mergeSort, sell]

end F6

/-! ### F8 (#5): UK matching over a sequence of sales, threading the 30-day window and the pool -/

section F8
open Kanon.UkMatch

/-- A purchase: its coins and their cost (cents). -/
structure Buy where
  qty : Nat
  cost : Nat
  deriving Repr, DecidableEq

/-- Cost of taking `t` coins from a purchase: its share, rounded down (same rule as the pool's `poolCost`). -/
def buyCost (b : Buy) (t : Nat) : Nat := poolCost b.cost b.qty t

/-- Take up to `w` coins from the window's purchases, earliest first:
(coins taken from each, cost taken, purchases left, still wanted). -/
def takeC : Nat → List Buy → List Nat × Nat × List Buy × Nat
  | w, [] => ([], 0, [], w)
  | w, b :: bs =>
    let t := min w b.qty
    let r := takeC (w - t) bs
    (t :: r.1, buyCost b t + r.2.1, ⟨b.qty - t, b.cost - buyCost b t⟩ :: r.2.2.1, r.2.2.2)

/-- What is carried from one sale to the next: the purchases left in the 30-day window, and the pool. -/
structure UkState where
  window : List Buy
  poolQty : Nat
  poolCost : Nat
  deriving Repr, DecidableEq

/-- One day: coins sold and the purchase made that same day. -/
structure UkDay where
  sell : Nat
  buy : Buy
  deriving Repr, DecidableEq

/-- How one sale was matched, and the cost it was given. -/
structure UkSale where
  sameDay : Nat
  thirtyDay : List Nat
  fromPool : Nat
  unknown : Nat
  cost : Nat
  deriving Repr, DecidableEq

/-- One sale: same day, then the 30-day window, then the pool (as `matchSale`), returning the updated state.
What is left of the same-day purchase joins the pool. -/
def ukStep (st : UkState) (d : UkDay) : UkSale × UkState :=
  let m := min d.sell d.buy.qty
  let t := takeC (d.sell - m) st.window
  let p := min t.2.2.2 st.poolQty
  let pc := poolCost st.poolCost st.poolQty p
  (⟨m, t.1, p, t.2.2.2 - p, buyCost d.buy m + t.2.1 + pc⟩,
   ⟨t.2.2.1, st.poolQty - p + (d.buy.qty - m), st.poolCost - pc + (d.buy.cost - buyCost d.buy m)⟩)

/-- **The tightened UK matcher.** A whole sequence of sales, each one seeing what the earlier ones left. -/
def ukRun : UkState → List UkDay → List UkSale × UkState
  | st, [] => ([], st)
  | st, d :: ds => ((ukStep st d).1 :: (ukRun (ukStep st d).2 ds).1, (ukRun (ukStep st d).2 ds).2)

def qtyOf (bs : List Buy) : List Nat := bs.map Buy.qty

def costSum : List Buy → Nat
  | [] => 0
  | b :: bs => b.cost + costSum bs

theorem buyCost_le (b : Buy) (t : Nat) (h : t ≤ b.qty) : buyCost b t ≤ b.cost := pool_cost_le _ _ _ h

/-- On quantities, `takeC` is exactly the bank's `take`. -/
theorem takeC_qty (w : Nat) (bs : List Buy) :
    (takeC w bs).1 = (take w (qtyOf bs)).1 ∧ qtyOf (takeC w bs).2.2.1 = (take w (qtyOf bs)).2.1 ∧
      (takeC w bs).2.2.2 = (take w (qtyOf bs)).2.2 := by
  induction bs generalizing w with
  | nil => simp [takeC, take, qtyOf]
  | cons b bs ih =>
    obtain ⟨h1, h2, h3⟩ := ih (w - min w b.qty)
    simp only [qtyOf] at h2
    simp [takeC, take, qtyOf, h1, h2, h3]

/-- On quantities, each step is exactly the bank's `matchSale`. -/
theorem ukStep_is_matchSale (st : UkState) (d : UkDay) :
    let s := (ukStep st d).1
    let o := matchSale d.sell d.buy.qty (qtyOf st.window) st.poolQty
    s.sameDay = o.sameDay ∧ s.thirtyDay = o.thirtyDay ∧ s.fromPool = o.fromPool ∧ s.unknown = o.unknown := by
  obtain ⟨h1, -, h3⟩ := takeC_qty (d.sell - min d.sell d.buy.qty) st.window
  simp [ukStep, matchSale, h1, h3]

/-- Per purchase in the window: taken now plus left over is what it had. -/
theorem takeC_each (w : Nat) (bs : List Buy) (i : Nat) :
    (takeC w bs).1.getD i 0 + (qtyOf (takeC w bs).2.2.1).getD i 0 = (qtyOf bs).getD i 0 := by
  induction bs generalizing w i with
  | nil => simp [takeC, qtyOf]
  | cons b bs ih =>
    cases i with
    | zero => simp [takeC, qtyOf]; omega
    | succ i => simpa [takeC, qtyOf] using ih (w - min w b.qty) i

theorem takeC_sum (w : Nat) (bs : List Buy) :
    total (takeC w bs).1 + (takeC w bs).2.2.2 = w ∧
    total (takeC w bs).1 + total (qtyOf (takeC w bs).2.2.1) = total (qtyOf bs) ∧
    (takeC w bs).2.1 + costSum (takeC w bs).2.2.1 = costSum bs := by
  induction bs generalizing w with
  | nil => simp [takeC, total, qtyOf, costSum]
  | cons b bs ih =>
    obtain ⟨h1, h2, h3⟩ := ih (w - min w b.qty)
    have := buyCost_le b (min w b.qty) (Nat.min_le_right _ _)
    have := Nat.min_le_left w b.qty
    have := Nat.min_le_right w b.qty
    simp only [qtyOf] at h2
    simp only [takeC, total, qtyOf, List.map_cons, costSum]
    omega

/-- **F8.** Each sale's parts add up exactly to what it sold. -/
theorem ukStep_parts (st : UkState) (d : UkDay) :
    let s := (ukStep st d).1
    s.sameDay + total s.thirtyDay + s.fromPool + s.unknown = d.sell := by
  have := (takeC_sum (d.sell - min d.sell d.buy.qty) st.window).1
  have := Nat.min_le_left d.sell d.buy.qty
  simp only [ukStep]
  have := Nat.min_le_left (takeC (d.sell - min d.sell d.buy.qty) st.window).2.2.2 st.poolQty
  omega

/-- Coins matched by a sale (everything but the unknown part). -/
def matched (s : UkSale) : Nat := s.sameDay + total s.thirtyDay + s.fromPool

def sumBy (f : UkSale → Nat) : List UkSale → Nat
  | [] => 0
  | s :: ss => f s + sumBy f ss

def buyQty : List UkDay → Nat
  | [] => 0
  | d :: ds => d.buy.qty + buyQty ds

def buyCostSum : List UkDay → Nat
  | [] => 0
  | d :: ds => d.buy.cost + buyCostSum ds

/-- One step conserves coins and cost. -/
theorem ukStep_conserves (st : UkState) (d : UkDay) :
    matched (ukStep st d).1 + total (qtyOf (ukStep st d).2.window) + (ukStep st d).2.poolQty =
      total (qtyOf st.window) + st.poolQty + d.buy.qty ∧
    (ukStep st d).1.cost + costSum (ukStep st d).2.window + (ukStep st d).2.poolCost =
      costSum st.window + st.poolCost + d.buy.cost := by
  obtain ⟨-, h2, h3⟩ := takeC_sum (d.sell - min d.sell d.buy.qty) st.window
  have := Nat.min_le_right d.sell d.buy.qty
  have := buyCost_le d.buy (min d.sell d.buy.qty) (Nat.min_le_right _ _)
  have hp := Nat.min_le_right (takeC (d.sell - min d.sell d.buy.qty) st.window).2.2.2 st.poolQty
  have := pool_cost_le st.poolCost st.poolQty _ hp
  simp only [ukStep, matched]
  omega

/-- **F8, no purchase in the window is used beyond its size across the whole sequence.** For every purchase
`i` of the starting window: what all the sales took from it, plus what is still left of it, is exactly what
was bought. -/
theorem ukRun_each_buy_once (ds : List UkDay) (st : UkState) (i : Nat) :
    (((ukRun st ds).1.map (fun s => s.thirtyDay.getD i 0)).sum) + (qtyOf (ukRun st ds).2.window).getD i 0 =
      (qtyOf st.window).getD i 0 := by
  induction ds generalizing st with
  | nil => simp [ukRun]
  | cons d ds ih =>
    have h1 := ih (ukStep st d).2
    have h2 := takeC_each (d.sell - min d.sell d.buy.qty) st.window i
    simp only [ukRun, List.map_cons, List.sum_cons]
    simp only [ukStep] at h1 ⊢
    omega

/-- **F8, the same-day purchase.** No sale uses more of its same-day purchase than was bought. -/
theorem ukRun_sameDay_le (ds : List UkDay) (st : UkState) :
    sumBy UkSale.sameDay (ukRun st ds).1 ≤ buyQty ds := by
  induction ds generalizing st with
  | nil => simp [ukRun, sumBy, buyQty]
  | cons d ds ih =>
    have := ih (ukStep st d).2
    have := Nat.min_le_right d.sell d.buy.qty
    simp only [ukRun, sumBy, buyQty]
    simp only [ukStep] at *
    omega

/-- **F8, coins conserved over the whole sequence.** Every coin matched to a sale, plus what is left in the
window and the pool, is exactly what the window and pool held at the start plus everything bought: no
purchase (window, pool or same-day) is used for more than its quantity. -/
theorem ukRun_qty_conserved (ds : List UkDay) (st : UkState) :
    sumBy matched (ukRun st ds).1 + total (qtyOf (ukRun st ds).2.window) + (ukRun st ds).2.poolQty =
      total (qtyOf st.window) + st.poolQty + buyQty ds := by
  induction ds generalizing st with
  | nil => simp [ukRun, sumBy, buyQty]
  | cons d ds ih =>
    have h1 := ih (ukStep st d).2
    have h2 := (ukStep_conserves st d).1
    simp only [ukRun, sumBy, buyQty]
    omega

/-- **F8, cost conserved over the whole sequence.** The cost given to all the sales, plus the cost still in the
window and the pool, is exactly the starting cost plus the cost of everything bought. -/
theorem ukRun_cost_conserved (ds : List UkDay) (st : UkState) :
    sumBy UkSale.cost (ukRun st ds).1 + costSum (ukRun st ds).2.window + (ukRun st ds).2.poolCost =
      costSum st.window + st.poolCost + buyCostSum ds := by
  induction ds generalizing st with
  | nil => simp [ukRun, sumBy, buyCostSum]
  | cons d ds ih =>
    have h1 := ih (ukStep st d).2
    have h2 := (ukStep_conserves st d).2
    simp only [ukRun, sumBy, buyCostSum]
    omega

/-- **F8, every sale's parts add up.** In the whole sequence, each sale's same-day, 30-day, pool and unknown parts
add up exactly to what it sold. -/
theorem ukRun_parts (ds : List UkDay) (st : UkState) :
    (ukRun st ds).1.length = ds.length ∧
    ∀ p ∈ (ukRun st ds).1.zip ds, p.1.sameDay + total p.1.thirtyDay + p.1.fromPool + p.1.unknown = p.2.sell := by
  induction ds generalizing st with
  | nil => simp [ukRun]
  | cons d ds ih =>
    obtain ⟨hl, hp⟩ := ih (ukStep st d).2
    refine ⟨by simp [ukRun, hl], ?_⟩
    intro p hmem
    simp only [ukRun, List.zip_cons_cons, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ukStep_parts st d
    · exact hp p hmem

/-- **F8.** The audit's example: two sales of 10, with one 5-coin buy in the window and a 5-coin pool. Threaded,
the two sales together are matched to 10 coins (not 20), and the second sale's 10 coins have no known cost. -/
theorem ukRun_audit_example :
    let r := ukRun ⟨[⟨5, 500⟩], 5, 500⟩ [⟨10, ⟨0, 0⟩⟩, ⟨10, ⟨0, 0⟩⟩]
    sumBy matched r.1 = 10 ∧ sumBy UkSale.unknown r.1 = 10 ∧ sumBy UkSale.cost r.1 = 1000 := by
  decide

end F8

/-! ### F9 (#13): a pro-rata split whose total is computed from the pools -/

section F9
open Kanon.Split

/-- Total coins across the pools. -/
def sumI : List Int → Int
  | [] => 0
  | b :: bs => b + sumI bs

theorem sumI_nonneg : ∀ (pools : List Int), (∀ b ∈ pools, 0 ≤ b) → 0 ≤ sumI pools
  | [], _ => by simp [sumI]
  | b :: bs, h => by
    have := sumI_nonneg bs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h b (List.mem_cons_self ..)
    simp only [sumI]; omega

/-- **The tightened split.** The bank's `prorata`, with `total` computed from the pools instead of passed in. -/
def prorataPools (sell : Int) (pools : List Int) : List (Int × Int) := prorata sell (sumI pools) pools 0

/-- Invariant of the split: if what earlier pools took is at most their share, every later part is between 0 and
the amount sold. -/
theorem prorata_bounds (sell T : Int) (hs : 0 ≤ sell) (hT : 0 < T) :
    ∀ (pools : List Int) (given P : Int), (∀ b ∈ pools, 0 ≤ b) → 0 ≤ given → 0 ≤ P →
      given * T ≤ sell * P → P + sumI pools ≤ T → ∀ x ∈ prorata sell T pools given, 0 ≤ x.2 ∧ x.2 ≤ sell
  | [], _, _, _, _, _, _, _ => by simp [prorata]
  | [b], given, P, hp, hg, hP, hinv, hsum => by
    intro x hx
    simp only [prorata, List.mem_singleton] at hx
    subst hx
    have hb := hp b (List.mem_cons_self ..)
    simp only [sumI] at hsum
    have h1 : sell * P ≤ sell * T := Int.mul_le_mul_of_nonneg_left (by omega) hs
    have h2 : given ≤ sell := Int.le_of_mul_le_mul_right (by omega) hT
    simp only; omega
  | b :: c :: rest, given, P, hp, hg, hP, hinv, hsum => by
    intro x hx
    have hb := hp b (List.mem_cons_self ..)
    have hrest : ∀ y ∈ c :: rest, 0 ≤ y := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have hcr := sumI_nonneg (c :: rest) hrest
    simp only [sumI] at hsum hcr
    have hbT : b ≤ T := by omega
    have q0 : 0 ≤ sell * b / T := Int.ediv_nonneg (Int.mul_nonneg hs hb) (by omega)
    have q1 : sell * b / T * T ≤ sell * b := Int.ediv_mul_le _ (by omega)
    have q2 : sell * b ≤ sell * T := Int.mul_le_mul_of_nonneg_left hbT hs
    have q3 : sell * b / T ≤ sell := Int.le_of_mul_le_mul_right (by omega) hT
    simp only [prorata, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨q0, q3⟩
    · refine prorata_bounds sell T hs hT (c :: rest) (given + sell * b / T) (P + b) hrest (by omega) (by omega)
        ?_ (by simp only [sumI]; omega) x hx
      rw [Int.add_mul, Int.mul_add]; omega

/-- With all pools empty the split puts everything in the last pool. -/
theorem prorata_zero_total (sell : Int) : ∀ (pools : List Int),
    ∀ x ∈ prorata sell 0 pools 0, x.2 = 0 ∨ x.2 = sell
  | [] => by simp [prorata]
  | [b] => by simp [prorata]
  | b :: c :: rest => by
    intro x hx
    simp only [prorata, Int.ediv_zero, Int.add_zero, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact prorata_zero_total sell (c :: rest) x (by simpa using hx)

/-- **F9 (on the old `prorata`, under the explicit hypothesis `total = sumI pools`).** When the amount sold and
every pool are non-negative and the total is the pools' total, every part is non-negative and at most the amount
sold. -/
theorem prorata_parts_bounded (sell : Int) (pools : List Int) (hs : 0 ≤ sell) (hp : ∀ b ∈ pools, 0 ≤ b) :
    ∀ x ∈ prorata sell (sumI pools) pools 0, 0 ≤ x.2 ∧ x.2 ≤ sell := by
  intro x hx
  have hT := sumI_nonneg pools hp
  by_cases h0 : sumI pools = 0
  · rw [h0] at hx
    rcases prorata_zero_total sell pools x hx with h | h <;> omega
  · exact prorata_bounds sell (sumI pools) hs (by omega) pools 0 0 hp (Int.le_refl _) (Int.le_refl _)
      (by simp) (by omega) x hx

/-- **F9.** Every part of `prorataPools` is non-negative and at most the amount sold. -/
theorem prorataPools_bounded (sell : Int) (pools : List Int) (hs : 0 ≤ sell) (hp : ∀ b ∈ pools, 0 ≤ b) :
    ∀ x ∈ prorataPools sell pools, 0 ≤ x.2 ∧ x.2 ≤ sell :=
  prorata_parts_bounded sell pools hs hp

/-- **F9.** The parts of `prorataPools` add up exactly to the amount sold. -/
theorem prorataPools_exact (sell : Int) (pools : List Int) (h : pools ≠ []) :
    sold (prorataPools sell pools) = sell :=
  prorata_exact sell _ pools h

/-- The split shown, with the total computed from the pools. -/
def shownPools (loss : List (Int × Int) → Nat) (sell deepest : Int) (rest : List Int) : List (Int × Int) :=
  shown loss sell (sumI (deepest :: rest)) deepest rest

/-- **F9.** Whatever is shown sells a non-negative amount, at most the amount sold, into each pool, and the
parts add up exactly. -/
theorem shownPools_bounded (loss : List (Int × Int) → Nat) (sell deepest : Int) (rest : List Int)
    (hs : 0 ≤ sell) (hp : ∀ b ∈ deepest :: rest, 0 ≤ b) :
    (∀ x ∈ shownPools loss sell deepest rest, 0 ≤ x.2 ∧ x.2 ≤ sell) ∧
    sold (shownPools loss sell deepest rest) = sell := by
  refine ⟨?_, shown_exact _ _ _ _ _⟩
  unfold shownPools shown
  have all : ∀ c ∈ candidates sell (sumI (deepest :: rest)) (deepest :: rest),
      ∀ x ∈ c, 0 ≤ x.2 ∧ x.2 ≤ sell := by
    intro c hc
    unfold candidates at hc
    rcases List.mem_append.mp hc with h | h
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
      intro x hx; simp at hx; subst hx; simp only; omega
    · simp at h; subst h; exact prorata_parts_bounded sell _ hs hp
  generalize candidates sell (sumI (deepest :: rest)) (deepest :: rest) = cs at all
  cases cs with
  | nil => simp
  | cons c cs => exact all _ (pick_mem loss c cs)

/-- **F9.** The audit's example: pools of 10 and 10 now split a sale of 100 as 50 and 50. -/
theorem prorataPools_audit_example : prorataPools 100 [10, 10] = [(10, 50), (10, 50)] := by decide

end F9

/-! ### F12 (#28): a date later than today counts as stale -/

section F12
open Kanon.Fresh

/-- **The tightened freshness rule.** Stale if the date can't be read, if it is later than today, or if it is
past its limit. -/
def staleT (today : Nat) (n : Checked) : Bool :=
  match n.asOf with
  | none => true
  | some d => decide (today < d ∨ today - d > n.limit)

def displayT (today : Nat) (n : Checked) : Shown := ⟨n.value, staleT today n⟩

def forAgentT (today : Nat) (ns : List Checked) : List Checked := ns.filter (fun n => !staleT today n)

/-- **F12.** A number dated later than today is always shown with the "stale" label. -/
theorem future_is_labelled (today : Nat) (n : Checked) (d : Nat) (h : n.asOf = some d) (future : today < d) :
    (displayT today n).staleLabel = true := by
  simp [displayT, staleT, h, future]

/-- **F12.** A number dated later than today is never given to the agent. -/
theorem future_never_for_agent (today : Nat) (ns : List Checked) (n : Checked) (d : Nat)
    (h : n.asOf = some d) (future : today < d) : n ∉ forAgentT today ns := by
  intro hn
  simp only [forAgentT, List.mem_filter] at hn
  simp [staleT, h, future] at hn

/-- **F12, existing guarantee kept.** A number older than its limit is never shown without the label. -/
theorem old_is_labelledT (today : Nat) (n : Checked) (d : Nat) (h : n.asOf = some d) (old : today - d > n.limit) :
    (displayT today n).staleLabel = true := by
  simp [displayT, staleT, h, old]

/-- **F12, existing guarantee kept.** A number whose date can't be read is always labelled stale. -/
theorem undated_is_labelledT (today : Nat) (n : Checked) (h : n.asOf = none) :
    (displayT today n).staleLabel = true := by
  simp [displayT, staleT, h]

/-- **F12, existing guarantee kept.** The label never changes the number itself. -/
theorem label_keeps_valueT (today : Nat) (n : Checked) : (displayT today n).value = n.value := rfl

/-- **F12, existing guarantee kept and strengthened.** Everything the agent is given has a date, that date is not
later than today, and it is within its limit. -/
theorem agent_never_gets_staleT (today : Nat) (ns : List Checked) :
    ∀ n ∈ forAgentT today ns, ∃ d, n.asOf = some d ∧ d ≤ today ∧ today - d ≤ n.limit := by
  intro n hn
  simp only [forAgentT, List.mem_filter] at hn
  obtain ⟨_, hs⟩ := hn
  cases h : n.asOf with
  | none => simp [staleT, h] at hs
  | some d =>
    refine ⟨d, rfl, ?_⟩
    simp [staleT, h] at hs
    omega

/-- **F12.** The new rule labels everything the old rule labelled. -/
theorem stale_implies_staleT (today : Nat) (n : Checked) (h : stale today n = true) : staleT today n = true := by
  unfold stale at h; unfold staleT
  cases e : n.asOf with
  | none => rfl
  | some d => rw [e] at h; simp at h ⊢; omega

/-- **F12.** For a number not dated in the future, the new rule is the old one. -/
theorem staleT_eq_stale (today : Nat) (n : Checked) (h : ∀ d, n.asOf = some d → d ≤ today) :
    staleT today n = stale today n := by
  unfold stale staleT
  cases e : n.asOf with
  | none => rfl
  | some d => have := h d e; simp; omega

/-- **F12, `stale_stays_stale` kept, under an explicit hypothesis.** A number that was stale on day `t₁` for being
undated or too old (not for being dated after `t₁`) stays stale on every later day. -/
theorem staleT_stays_stale (t₁ t₂ : Nat) (n : Checked) (later : t₁ ≤ t₂)
    (notFuture : ∀ d, n.asOf = some d → d ≤ t₁) (h : staleT t₁ n = true) : staleT t₂ n = true := by
  unfold staleT at h ⊢
  cases e : n.asOf with
  | none => rfl
  | some d => have := notFuture d e; rw [e] at h; simp at h ⊢; omega

/-- **F12.** Without that hypothesis `stale_stays_stale` cannot hold for any rule that labels future dates: a rate
dated day 150 is stale on day 100 (dated in the future) and fresh on day 150. -/
theorem staleT_future_then_fresh :
    staleT 100 ⟨2500, some 150, 14⟩ = true ∧ staleT 150 ⟨2500, some 150, 14⟩ = false := by decide

/-- **F12.** The audit's example: the rate dated day 10,000 is now labelled on day 100 and day 9,000, and is
not given to the agent. -/
theorem staleT_audit_example :
    staleT 100 ⟨2500, some 10000, 14⟩ = true ∧ (forAgentT 100 [⟨2500, some 10000, 14⟩]).length = 0 ∧
    staleT 9000 ⟨2500, some 10000, 14⟩ = true := by decide

end F12

/-! ### F3 (#5): holding period on calendar dates -/

section F3

/-- A calendar date. -/
structure Date where
  y : Nat
  m : Nat
  d : Nat
  deriving Repr, DecidableEq

/-- `a` is strictly before `b` (year, then month, then day). -/
def Date.Before (a b : Date) : Prop := a.y < b.y ∨ (a.y = b.y ∧ (a.m < b.m ∨ (a.m = b.m ∧ a.d < b.d)))

/-- `a` is on or before `b`. -/
def Date.OnOrBefore (a b : Date) : Prop := a.y < b.y ∨ (a.y = b.y ∧ (a.m < b.m ∨ (a.m = b.m ∧ a.d ≤ b.d)))

instance (a b : Date) : Decidable (Date.Before a b) := by unfold Date.Before; infer_instance
instance (a b : Date) : Decidable (Date.OnOrBefore a b) := by unfold Date.OnOrBefore; infer_instance

/-- The one-year anniversary of a purchase: same month and day a year later; a 29 February purchase has its
anniversary on 28 February. -/
def anniversary (a : Date) : Date := if a.m = 2 ∧ a.d = 29 then ⟨a.y + 1, 2, 28⟩ else ⟨a.y + 1, a.m, a.d⟩

/-- **The tightened holding-period test.** Held more than a year: sold after the one-year anniversary. -/
def heldOverYear (bought sold : Date) : Bool := decide (Date.Before (anniversary bought) sold)

/-- **F3.** The two cases from the audit are now separated: bought 1 Jan 2024 and sold 1 Jan 2025 (exactly one
year) is not held over a year; bought 1 Jan 2023 and sold 2 Jan 2024 is. Both are 366 days apart. -/
theorem heldOverYear_leap_cases :
    heldOverYear ⟨2024, 1, 1⟩ ⟨2025, 1, 1⟩ = false ∧ heldOverYear ⟨2023, 1, 1⟩ ⟨2024, 1, 2⟩ = true := by decide

/-- **F3.** A 29 February purchase: sold on 28 February next year is not over a year; on 1 March it is. -/
theorem heldOverYear_feb29 :
    heldOverYear ⟨2024, 2, 29⟩ ⟨2025, 2, 28⟩ = false ∧ heldOverYear ⟨2024, 2, 29⟩ ⟨2025, 3, 1⟩ = true := by decide

/-- **F3.** Monotone in the sale date: if a sale counts as held over a year, so does any later sale. -/
theorem heldOverYear_mono (bought s₁ s₂ : Date) (hs : Date.OnOrBefore s₁ s₂)
    (h : heldOverYear bought s₁ = true) : heldOverYear bought s₂ = true := by
  unfold heldOverYear at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  unfold Date.OnOrBefore at hs
  unfold Date.Before at h ⊢
  omega

open Kanon.Matching in
/-- For contrast, the bank's day-count test (`sellSplit` on day numbers, day 0 = 1 Jan 2023) gives the two audit
cases the same answer for every threshold `days`. -/
theorem day_count_cannot_separate (days : Nat) :
    (sellSplit 731 days [⟨365, 1, 0⟩] 1).1 = (sellSplit 366 days [⟨0, 1, 0⟩] 1).1 := by
  simp [sellSplit]

end F3

/-! ### F2 (#17): the guard knows which numbers are money -/

section F2
open Kanon.Guard

/-- How a number is written in the answer. -/
inductive Kind
  | money
  | percent
  | bare
  deriving Repr, DecidableEq

/-- An answer whose numbers carry how they are written. -/
structure TAnswer where
  numbers : List (Nat × Kind)
  words : List Nat

/-- Only a number written bare can pass as a count or a year. -/
def freeT (x : Nat × Kind) : Bool := x.2 == Kind.bare && free x.1

def sourcedT (data : List Nat) (x : Nat × Kind) : Bool := freeT x || data.any (close x.1)

/-- **The tightened checker.** -/
def checkT (banned data : List Nat) (a : TAnswer) : Bool :=
  a.numbers.all (sourcedT data) && a.words.all (fun w => !banned.contains w)

def fallbackT (safeWords : List Nat) : TAnswer := ⟨[], safeWords⟩

def respondT (banned data safeWords : List Nat) : List TAnswer → TAnswer
  | [] => fallbackT safeWords
  | a :: rest => if checkT banned data a then a else respondT banned data safeWords rest

/-- **F2.** Whatever is shown passes the tightened checker, for any number of tries. -/
theorem shownT_passes (banned data safeWords : List Nat) (h : safeWords.all (fun w => !banned.contains w) = true) :
    ∀ tries : List TAnswer, checkT banned data (respondT banned data safeWords tries) = true := by
  intro tries
  induction tries with
  | nil => simp [checkT, fallbackT, respondT] at *; exact h
  | cons a rest ih =>
    unfold respondT
    by_cases hc : checkT banned data a = true
    · simp [hc]
    · simp [hc]; exact ih

/-- **F2.** Every number shown flagged as money (or as a percentage) is within tolerance of an engine number. -/
theorem shownT_money_sourced (banned data safeWords : List Nat)
    (h : safeWords.all (fun w => !banned.contains w) = true) (tries : List TAnswer) :
    ∀ x ∈ (respondT banned data safeWords tries).numbers, x.2 ≠ Kind.bare → ∃ d ∈ data, close x.1 d = true := by
  intro x hx hk
  have := shownT_passes banned data safeWords h tries
  simp only [checkT, Bool.and_eq_true, List.all_eq_true] at this
  have hs := this.1 x hx
  simp only [sourcedT, freeT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hs
  rcases hs with hf | hs
  · exact absurd hf.1 hk
  · exact hs

/-- **F2.** In particular, every money-flagged number shown is close to an engine number. -/
theorem shownT_money_close (banned data safeWords : List Nat)
    (h : safeWords.all (fun w => !banned.contains w) = true) (tries : List TAnswer) (n : Nat)
    (hn : (n, Kind.money) ∈ (respondT banned data safeWords tries).numbers) : ∃ d ∈ data, close n d = true :=
  shownT_money_sourced banned data safeWords h tries _ hn (fun h => Kind.noConfusion h)

/-- **F2.** Every number shown is a bare small count or year, or close to an engine number. -/
theorem shownT_numbers_sourced (banned data safeWords : List Nat)
    (h : safeWords.all (fun w => !banned.contains w) = true) (tries : List TAnswer) :
    ∀ x ∈ (respondT banned data safeWords tries).numbers,
      (x.2 = Kind.bare ∧ free x.1 = true) ∨ ∃ d ∈ data, close x.1 d = true := by
  intro x hx
  have := shownT_passes banned data safeWords h tries
  simp only [checkT, Bool.and_eq_true, List.all_eq_true] at this
  have hs := this.1 x hx
  simp only [sourcedT, freeT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hs
  exact hs

/-- **F2.** And no banned word is ever shown. -/
theorem shownT_no_banned (banned data safeWords : List Nat)
    (h : safeWords.all (fun w => !banned.contains w) = true) (tries : List TAnswer) :
    ∀ w ∈ (respondT banned data safeWords tries).words, banned.contains w = false := by
  intro w hw
  have := shownT_passes banned data safeWords h tries
  simp only [checkT, Bool.and_eq_true, List.all_eq_true] at this
  simpa using this.2 w hw

/-- **F2.** The audit's examples are now refused: "$2,000.00" and "$31.00" flagged as money fail against engine
data `[$50.00]` and against no data; the year 2,026 written bare still passes. -/
theorem checkT_audit_example :
    checkT [] [5000] ⟨[(200000, .money), (3100, .money)], []⟩ = false ∧
    checkT [] [] ⟨[(3100, .money)], []⟩ = false ∧
    checkT [] [] ⟨[(202600, .bare)], []⟩ = true := by decide

end F2

end Kanon.Tightened
