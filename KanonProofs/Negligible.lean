import Mathlib.Tactic

/-!
# UK negligible value claims (#50)

TCGA 1992 s24(2) and HMRC CRYPTO22500: on a negligible value claim the whole section 104 pool of a token is treated as
sold and immediately reacquired for the value stated in the claim (often £0). The app (`src/lib/engine/gb.ts`, step 4
of `matchGb`) applies it after the day's own trades. Proved here, for a pool of `q` tokens costing `c`, a claim at `v`:

* **The claim's disposal is the whole pool: proceeds `v`, cost `c`, gain `v - c`; the tokens are still held, all `q`
  of them, now costing `v`.** A claim on a day none of the token is held does nothing.
* **A claim only moves the loss earlier: it never creates one or makes one vanish.** Sell any `k` of the `q` tokens
  later for `P` (from the pool, at its average cost): the gains so far, less the cost still in the pool, are the same
  with or without the claim. So once every token is sold, the total gain is the same; until then, what the claim
  brought forward is exactly the cost the pool no longer carries.
-/

namespace Kanon.Negligible

/-- A pool: tokens and their total cost. -/
structure Pool where
  qty : ℚ
  cost : ℚ

/-- A negligible value claim at `v`: the pool after it, and the claim's gain (proceeds `v` less the pool's cost). -/
def claim (p : Pool) (v : ℚ) : Pool × ℚ := (⟨p.qty, v⟩, v - p.cost)

/-- A sale of `k` tokens from the pool for `P`: the pool after it, and the gain (cost at the pool's average). -/
def sell (p : Pool) (k P : ℚ) : Pool × ℚ := (⟨p.qty - k, p.cost - p.cost * k / p.qty⟩, P - p.cost * k / p.qty)

/-- The app's step (gb.ts, step 4): a claim on a pool holding tokens is `claim`; on an empty pool it does nothing (no
disposal, `none`). -/
def applyClaim (p : Pool) (v : ℚ) : Pool × Option ℚ :=
  if 0 < p.qty then ((claim p v).1, some (claim p v).2) else (p, none)

/-- **#50** On a pool holding tokens, the claim's disposal is the whole pool at the claim's value (gain `v - c`); the
tokens are kept, all of them, now costing that value. On an empty pool a claim does nothing. -/
theorem claim_whole_pool (p : Pool) (v : ℚ) (hq : 0 < p.qty) :
    (applyClaim p v).1.qty = p.qty ∧ (applyClaim p v).1.cost = v ∧ (applyClaim p v).2 = some (v - p.cost) := by
  simp [applyClaim, hq, claim]

/-- **#50** A claim on a day none of the token is held does nothing. -/
theorem claim_empty (p : Pool) (v : ℚ) (hq : p.qty ≤ 0) : applyClaim p v = (p, none) := by
  simp [applyClaim, not_lt.mpr hq]

/-- **#50** A claim then a sale of `k` tokens, against the sale alone: gains so far less the cost left in the pool are
the same (both are `P - c`). -/
theorem claim_moves_loss (p : Pool) (v k P : ℚ) (hq : p.qty ≠ 0) :
    let c := claim p v
    let s := sell c.1 k P
    c.2 + s.2 - s.1.cost = (sell p k P).2 - (sell p k P).1.cost := by
  simp only [claim, sell]
  field_simp
  ring

/-- **#50** Once every token is sold, the total gain with the claim is the gain without it. -/
theorem claim_then_sell_all (p : Pool) (v P : ℚ) (hq : p.qty ≠ 0) :
    (claim p v).2 + (sell (claim p v).1 p.qty P).2 = (sell p p.qty P).2 := by
  simp only [claim, sell]
  field_simp
  ring

end Kanon.Negligible
