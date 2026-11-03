import Mathlib.Tactic
import KanonProofs.Lots

/-!
# Choosing the cost method (#36)

Where the law lets the person choose which coins a sale uses (the US: Treas. Reg. 1.1012-1(j)), KANON offers standing
orders: oldest first (FIFO), highest cost first (HIFO) or newest first (LIFO), each from the day it is recorded
(`src/lib/engine/lots.ts`, `methodFor` and `pickLots`).

Proved here:

* **Highest cost first gives the largest cost, so the smallest gain.** Taking coins from lots sorted by cost per coin,
  highest first, the cost of the coins sold is at least that of any other way of taking the same number of coins from
  the same lots (oldest first, newest first, or any mix of parts of lots). With the same sale price, the gain is never
  larger. In exact fractions, for lots of non-negative size and cost.
* **Every order sells real coins.** Whatever order the lots are taken in, coins sold + coins left = coins before, and
  the same for cost: the conservation of #3 holds for HIFO and LIFO too, because they are #3's sale on a reordered
  list, and reordering keeps the totals.
* **A standing order counts from its day on.** A sale uses the newest order recorded on or before its day; before any
  order, the default (oldest first). A new order never changes a sale dated before the order's own day (1.1012-1(j)(4):
  forward only). The app lets an order be dated earlier than the day it is recorded, with a warning; sales between the
  two do follow it. Coins held by an exchange: from 2027 an order counts only if it was also set with the exchange, else
  oldest first (Notice 2025-7). Transactions added by hand are not held by an exchange.

Not covered here, tested in the app: the 40-digit decimals the app works in, ties between lots of equal cost per coin
(oldest first), and which coins a named-lot (specific ID) sale picks.
-/

namespace Kanon.Methods

/-- A lot: how many coins, and what each cost. -/
structure CLot where
  qty : ℚ
  unit : ℚ

/-- The cost of `q` coins taken from the lots in the order given (the app's sale, any order). -/
def taken : List CLot → ℚ → ℚ
  | [], _ => 0
  | l :: ls, q => if q ≤ l.qty then q * l.unit else l.qty * l.unit + taken ls (q - l.qty)

/-- Any way of taking coins from the lots: how many from each (`t`), never below 0 nor above what the lot holds. -/
def Valid : List (CLot × ℚ) → Prop
  | [] => True
  | (l, t) :: rest => 0 ≤ t ∧ t ≤ l.qty ∧ Valid rest

def count : List (CLot × ℚ) → ℚ
  | [] => 0
  | (_, t) :: rest => t + count rest

def costOf : List (CLot × ℚ) → ℚ
  | [] => 0
  | (l, t) :: rest => t * l.unit + costOf rest

/-- Lots sorted by cost per coin, highest first: the order HIFO takes them in. -/
def HighestFirst (ls : List CLot) : Prop := ls.Pairwise (fun a b => b.unit ≤ a.unit)

def Sane (ls : List CLot) : Prop := ∀ l ∈ ls, 0 ≤ l.qty ∧ 0 ≤ l.unit

lemma taken_zero (ls : List CLot) (h : Sane ls) : taken ls 0 = 0 := by
  cases ls with
  | nil => rfl
  | cons l ls => simp [taken, (h l (by simp)).1]

/-- Each further coin taken costs at most the highest cost per coin among the lots. -/
lemma taken_step (ls : List CLot) (u : ℚ) (hs : Sane ls) (hu : 0 ≤ u) (hle : ∀ l ∈ ls, l.unit ≤ u) :
    ∀ s s', 0 ≤ s' → s' ≤ s → taken ls s ≤ taken ls s' + (s - s') * u := by
  induction ls with
  | nil => intro s s' _ h; simp [taken]; nlinarith
  | cons l ls ih =>
    intro s s' h0 h
    have hl := hle l (by simp)
    have hsl := hs l (by simp)
    have ih' := ih (fun x hx => hs x (by simp [hx])) (fun x hx => hle x (by simp [hx]))
    simp only [taken]
    by_cases hA : s ≤ l.qty
    · have hB : s' ≤ l.qty := le_trans h hA
      simp only [hA, hB, if_true]; nlinarith
    · by_cases hB : s' ≤ l.qty
      · simp only [hA, hB, if_true, if_false]
        have := ih' (s - l.qty) 0 le_rfl (by linarith)
        rw [taken_zero ls (fun x hx => hs x (by simp [hx]))] at this
        nlinarith
      · simp only [hA, hB, if_false]
        have := ih' (s - l.qty) (s' - l.qty) (by linarith) (by linarith)
        linarith

/-- **#36 HIFO** Taking coins highest cost first, the coins sold cost at least as much as by any other way of taking
the same number of coins from the same lots. -/
theorem hifo_most_cost (sel : List (CLot × ℚ)) (hv : Valid sel) (hs : Sane (sel.map Prod.fst))
    (hh : HighestFirst (sel.map Prod.fst)) :
    costOf sel ≤ taken (sel.map Prod.fst) (count sel) := by
  induction sel with
  | nil => simp [costOf, taken]
  | cons p rest ih =>
    obtain ⟨l, t⟩ := p
    obtain ⟨ht0, htq, hv'⟩ := hv
    simp only [List.map_cons] at hs hh ⊢
    have hsr : Sane (rest.map Prod.fst) := fun x hx => hs x (by simp [hx])
    have hhr : HighestFirst (rest.map Prod.fst) := (List.pairwise_cons.mp hh).2
    have hbelow : ∀ x ∈ rest.map Prod.fst, x.unit ≤ l.unit := (List.pairwise_cons.mp hh).1
    have hl := hs l (by simp)
    have ih' := ih hv' hsr hhr
    have hc : 0 ≤ count rest := by
      clear ih ih' hbelow hhr hsr hs hh
      induction rest with
      | nil => simp [count]
      | cons p r ih2 => obtain ⟨_, t'⟩ := p; obtain ⟨h1, _, h3⟩ := hv'; simp only [count]; linarith [ih2 h3]
    have step := taken_step (rest.map Prod.fst) l.unit hsr hl.2 hbelow
    simp only [costOf, count, taken]
    by_cases hq : t + count rest ≤ l.qty
    · simp only [hq, if_true]
      have := step (count rest) 0 le_rfl hc
      rw [taken_zero _ hsr] at this
      nlinarith
    · simp only [hq, if_false]
      have := step (count rest) (t + count rest - l.qty) (by linarith) (by linarith)
      nlinarith

/-- **#36 HIFO** With the same sale price, the gain from taking coins highest cost first is never larger than by any
other way of taking the same coins. -/
theorem hifo_least_gain (sel : List (CLot × ℚ)) (hv : Valid sel) (hs : Sane (sel.map Prod.fst))
    (hh : HighestFirst (sel.map Prod.fst)) (proceeds : ℚ) :
    proceeds - taken (sel.map Prod.fst) (count sel) ≤ proceeds - costOf sel := by
  linarith [hifo_most_cost sel hv hs hh]

section Reordered
open Kanon.Lots

lemma totalQty_sum (ls : List Lot) : totalQty ls = (ls.map Lot.qty).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [totalQty, ih]

lemma totalCost_sum (ls : List Lot) : totalCost ls = (ls.map Lot.cost).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [totalCost, ih]

/-- **#36 Any order** Taking the lots in any order (highest cost first, newest first, or any other), #3's sale keeps
coins sold + coins left = coins before, and cost of coins sold + cost left = cost before, against the lots as held. -/
theorem any_order_conserves (ls order : List Lot) (hp : order.Perm ls) (q : ℕ) :
    (sell order q).1 + totalQty (sell order q).2.2 = totalQty ls ∧
      (sell order q).2.1 + totalCost (sell order q).2.2 = totalCost ls := by
  refine ⟨?_, ?_⟩
  · rw [sell_qty, totalQty_sum, totalQty_sum]; exact (hp.map _).sum_eq
  · rw [sell_cost, totalCost_sum, totalCost_sum]; exact (hp.map _).sum_eq

/-- **#36 Any order** In any order, a sale sells exactly what was asked when enough is held. -/
theorem any_order_exact (ls order : List Lot) (hp : order.Perm ls) (q : ℕ) (h : q ≤ totalQty ls) :
    (sell order q).1 = q := by
  apply sell_exact; rw [totalQty_sum] at h ⊢; rwa [(hp.map _).sum_eq]

end Reordered

/-! ### Standing orders -/

inductive Method | fifo | hifo | lifo
  deriving DecidableEq

/-- A standing order: its method, the day it counts from, and whether it was also set with the exchange. -/
structure Order where
  method : Method
  from_ : ℕ
  withExchange : Bool

/-- The last day an exchange's own dated record of the order is enough (31 Dec 2026, as a day number). -/
def recordsUntil : ℕ := 20261231

/-- The method a sale on day `d` uses (orders oldest first; `held` when the coins are held by an exchange, which coins
added by hand are not). Before any order, and for an exchange's coins from 2027 without the order set there, the default
(oldest first). -/
def methodFor (orders : List Order) (d : ℕ) (held : Bool) : Method :=
  match orders.reverse.find? (fun o => decide (o.from_ ≤ d)) with
  | none => .fifo
  | some o => if held ∧ d > recordsUntil ∧ o.withExchange = false then .fifo else o.method

/-- **#36 Standing orders** A new order never changes the method of a sale dated before the order's own day. -/
theorem forward_only (orders : List Order) (o : Order) (d : ℕ) (held : Bool) (h : d < o.from_) :
    methodFor (orders ++ [o]) d held = methodFor orders d held := by
  have : ¬ o.from_ ≤ d := by omega
  simp [methodFor, List.reverse_append, this]

/-- **#36 Standing orders** Before the first order's day, a sale uses the default, oldest first. -/
theorem before_any (orders : List Order) (d : ℕ) (held : Bool) (h : ∀ o ∈ orders, d < o.from_) :
    methodFor orders d held = .fifo := by
  have : orders.reverse.find? (fun o => decide (o.from_ ≤ d)) = none := by
    rw [List.find?_eq_none]; intro o ho; have := h o (List.mem_reverse.mp ho); simp; omega
  simp [methodFor, this]

/-- **#36 Standing orders** Coins not held by an exchange (a wallet of the person's own, or a transaction added by
hand) always use the newest order recorded on or before the day of the sale. -/
theorem own_wallet_uses_order (orders : List Order) (d : ℕ) (o : Order)
    (h : orders.reverse.find? (fun o => decide (o.from_ ≤ d)) = some o) :
    methodFor orders d false = o.method := by
  simp [methodFor, h]

/-- **#36 Standing orders** The order a sale uses is one recorded on or before its day, and no order recorded after it
(later in the list) is also on or before that day. -/
theorem uses_newest (orders : List Order) (d : ℕ) (o : Order)
    (h : orders.reverse.find? (fun o => decide (o.from_ ≤ d)) = some o) :
    o ∈ orders ∧ o.from_ ≤ d ∧ ∃ before after, orders = before ++ o :: after ∧ ∀ x ∈ after, d < x.from_ := by
  obtain ⟨a, b, hab, hno⟩ := List.find?_eq_some_iff_append.mp h |>.2
  have hd : o.from_ ≤ d := by simpa using (List.find?_eq_some_iff_append.mp h).1
  refine ⟨?_, hd, b.reverse, a.reverse, ?_, ?_⟩
  · have : o ∈ orders.reverse := by rw [hab]; simp
    exact List.mem_reverse.mp this
  · have := congrArg List.reverse hab; simpa using this
  · intro x hx; have := hno x (List.mem_reverse.mp hx); simp at this; omega

/-- **#36 Standing orders** Coins held by an exchange, sold from 2027, use the order only if it was also set with the
exchange; otherwise oldest first. -/
theorem exchange_from_2027 (orders : List Order) (d : ℕ) (o : Order) (hd : recordsUntil < d)
    (h : orders.reverse.find? (fun o => decide (o.from_ ≤ d)) = some o) :
    methodFor orders d true = if o.withExchange then o.method else .fifo := by
  cases hw : o.withExchange <;> simp [methodFor, h, hd, hw]

end Kanon.Methods
