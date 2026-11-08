import Mathlib.Tactic

/-!
# The cost of what's held, by the country's own method (#54)

The UK (section 104 pool), Brazil (average acquisition cost) and Japan (total or moving average) cost a coin's sales
from one pool across all wallets, not lot by lot. The app's lots come from a first-in-first-out ledger, so for those
countries the country's engine gives the pool's coins `Q` and cost `P ≥ 0` (`src/lib/report/report.ts`
`poolCosts`), and every held lot of `qᵢ` coins that came into the pool, in any wallet, is given the cost
`qᵢ · P / max(Q, H)`, with `H = ∑ qᵢ` the coins held (`poolUnit`; `src/app/api/money-map/route.ts` `lotsOf`). The
larger of the two is used because the held coins needn't add up to `Q` (a vault's shares are counted by the pool in the
coin put in; coins sold from a wallet that never showed them arriving). Coins never seen arriving stay at 0, outside;
a coin whose cost is only a guess went into the pool at 0, so the average already counts it. Proved below:

* **The held lots cost `P · H / max(Q, H)` together: never more than the pool, exactly the pool when `H ≥ Q`**; every
  coin costs the same; **any group of the lots (one wallet's, say) costs its share**, between nothing and the pool.
* **A sale of `x` of `Q` coins at the average costs `x / Q` of the pool** (the exit planner's and tax-if-sold's pooled
  sale, `src/lib/exit/plan.ts` `exitOptions`, `src/lib/findings/findings.ts` `sellAll`): nothing for none, the whole
  pool for all, never more than the pool, and **selling in parts costs the same in total as selling at once**.

That `poolCosts` computes each country's `P` and `Q` is the engines' work, tested against the tax offices' examples;
it isn't part of this statement.
-/

namespace Kanon.PoolCost

open Finset BigOperators

/-- A held lot of `q` coins costs its share of the pool: `q · (P / N)`, `N` the coins it is shared over. -/
def lotCost (P N q : ℚ) : ℚ := q * (P / N)

/-- **#54** Shared over `max(Q, H)`: the held lots cost `P · H / max(Q, H)` together, never more than the pool and
exactly the pool when `H ≥ Q`, and any group of them costs its share, between nothing and the pool. -/
theorem lots_add_up {n : ℕ} (q : Fin n → ℚ) (P Q : ℚ) (hq : ∀ i, 0 ≤ q i) (hP : 0 ≤ P) (hH : 0 < ∑ i, q i)
    (g : Finset (Fin n)) :
    let H := ∑ i, q i
    let N := max Q H
    (∑ i, lotCost P N (q i)) = P * (H / N) ∧ (∑ i, lotCost P N (q i)) ≤ P ∧ (Q ≤ H → (∑ i, lotCost P N (q i)) = P) ∧
    (∑ i ∈ g, lotCost P N (q i)) = P * ((∑ i ∈ g, q i) / N) ∧
    0 ≤ (∑ i ∈ g, lotCost P N (q i)) ∧ (∑ i ∈ g, lotCost P N (q i)) ≤ P := by
  intro H N
  have hN : 0 < N := lt_of_lt_of_le hH (le_max_right _ _)
  have hHN : H ≤ N := le_max_right _ _
  have hsum : ∀ t : Finset (Fin n), (∑ i ∈ t, lotCost P N (q i)) = P * ((∑ i ∈ t, q i) / N) := by
    intro t; unfold lotCost; rw [← Finset.sum_mul]; ring
  have hle : (∑ i ∈ g, q i) ≤ H := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ g) (fun i _ _ => hq i)
  have h0 : 0 ≤ (∑ i ∈ g, q i) := Finset.sum_nonneg (fun i _ => hq i)
  have hgN : (∑ i ∈ g, q i) / N ≤ 1 := (div_le_one hN).mpr (le_trans hle hHN)
  have hHN1 : H / N ≤ 1 := (div_le_one hN).mpr hHN
  have hall := hsum Finset.univ
  refine ⟨hall, ?_, ?_, hsum g, ?_, ?_⟩
  · rw [hall]; nlinarith [div_nonneg (le_of_lt hH) (le_of_lt hN)]
  · intro hQH
    have : N = H := max_eq_right hQH
    rw [hall, this, div_self (ne_of_gt hH), mul_one]
  · rw [hsum g]; exact mul_nonneg hP (div_nonneg h0 (le_of_lt hN))
  · rw [hsum g]; nlinarith [div_nonneg h0 (le_of_lt hN)]

/-- **#54** Every held coin costs the same: its share of the pool. -/
theorem same_per_coin (P N q : ℚ) (hq : 0 < q) : lotCost P N q / q = P / N := by
  unfold lotCost; field_simp

/-- The cost of selling `x` of the `Q` coins in a pool that cost `P`: its share of the pool. -/
def basis (P Q x : ℚ) : ℚ := P * (x / Q)

/-- **#54** Nothing sold costs nothing, all of it costs the whole pool, and a sale of `0 ≤ x ≤ Q` costs between
nothing and the pool. -/
theorem basis_bounds (P Q x : ℚ) (hP : 0 ≤ P) (hQ : 0 < Q) (hx0 : 0 ≤ x) (hxQ : x ≤ Q) :
    basis P Q 0 = 0 ∧ basis P Q Q = P ∧ 0 ≤ basis P Q x ∧ basis P Q x ≤ P := by
  unfold basis
  refine ⟨by simp, by rw [div_self (ne_of_gt hQ), mul_one], mul_nonneg hP (div_nonneg hx0 (le_of_lt hQ)), ?_⟩
  have : x / Q ≤ 1 := (div_le_one hQ).mpr hxQ
  nlinarith [div_nonneg hx0 (le_of_lt hQ)]

/-- **#54** Selling in parts costs the same in total as selling at once. -/
theorem basis_additive (P Q x y : ℚ) : basis P Q x + basis P Q y = basis P Q (x + y) := by
  unfold basis; ring

end Kanon.PoolCost
