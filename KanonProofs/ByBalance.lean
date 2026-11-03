import Mathlib.Tactic

/-!
# Coin found from the chain's own balance and count (#41)

On Optimism and BNB Chain, coin an app pays a wallet inside a transaction is in no list Alchemy's free plan gives. KANON
finds it from the chain's own records, block by block (`src/lib/chains/by-balance.ts`). Proved here:

* **The halving search can't miss a block.** The wallet's count of sent transactions (its nonce) is asked at the ends of
  a stretch of blocks. If it rose by more than the transactions known in the stretch, some single block in it rose by
  more than is known there (the app then looks for the wallet's own transaction in it; a count raised by an EIP-7702
  authorisation in someone else's transaction has none and is skipped). Split in two, at least one half still shows
  it; a search halving down one side ends on such a block and returns nothing else. And since the count never rises
  by less than the transactions known (`k b ≤ n b - n (b - 1)`), every stretch that holds such a block shows it at its
  ends: the app, which keeps halving every stretch that shows it, reaches every one (`missingOwnBlocks`). For the balance (`findByBalance`), which can part from
  the history either way: a stretch where the chain's change differs from the history's holds a block where it does.
* **What is found makes the history match the chain in that block.** The amount added for a block is the balance after
  it less the balance before it less what was already known there, so known plus found is exactly the chain's change.
* **A shortfall is a fee only where the wallet sent a transaction, and only up to a fee's size** (the app is stricter
  still: only when it is placed on a transaction the wallet sent itself). Coin found going out
  in a block where the wallet sent nothing (taken under an EIP-7702 delegation by someone else's transaction, say), or
  more than the fee cap, is coin that went out, for the person to say; coin found coming in is never a fee.

What a proof can't cover (that the provider's answers are right, that every block asked is answered) is checked against
real wallets: a read that couldn't finish says so.
-/

namespace Kanon.ByBalance

open Finset BigOperators

variable (n k : ℕ → ℤ)

/-- The stretch of blocks after `lo` up to `hi` shows more than is known: the count (or balance) `n` changed by more
than the known changes `k` of its blocks add up to. -/
def Excess (lo hi : ℕ) : Prop := (∑ b ∈ Ioc lo hi, k b) < n hi - n lo

/-- A single block shows more than is known in it. -/
def BlockExcess (b : ℕ) : Prop := k b < n b - n (b - 1)

instance (lo hi : ℕ) : Decidable (Excess n k lo hi) := by unfold Excess; infer_instance

lemma telescope (lo hi : ℕ) (h : lo ≤ hi) : n hi - n lo = ∑ b ∈ Ioc lo hi, (n b - n (b - 1)) := by
  induction hi, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ioc_succ_top hm, ← ih]
    simp

/-- **#41** A stretch that shows more than is known holds a single block that does. -/
theorem excess_has_block (lo hi : ℕ) (hle : lo ≤ hi) (h : Excess n k lo hi) : ∃ b ∈ Ioc lo hi, BlockExcess n k b := by
  by_contra hno
  push_neg at hno
  unfold Excess at h
  rw [telescope n lo hi hle] at h
  have : ∑ b ∈ Ioc lo hi, (n b - n (b - 1)) ≤ ∑ b ∈ Ioc lo hi, k b :=
    Finset.sum_le_sum (fun b hb => by have := hno b hb; unfold BlockExcess at this; linarith)
  linarith

/-- **#41 Balance** A stretch where the chain's balance changed by other than the history's movements add up to holds a
single block where it did (coin can be paid in or taken out, so either way). -/
theorem differs_has_block (lo hi : ℕ) (hle : lo ≤ hi) (h : n hi - n lo ≠ ∑ b ∈ Ioc lo hi, k b) :
    ∃ b ∈ Ioc lo hi, n b - n (b - 1) ≠ k b := by
  by_contra hno
  push_neg at hno
  rw [telescope n lo hi hle, Finset.sum_congr rfl hno] at h
  exact h rfl

/-- **#41** Where no block rises by less than is known in it, a stretch holding a block that rises by more shows it at its
ends: the search, which halves every stretch that shows it, never passes over such a block. -/
theorem block_shows (lo hi b : ℕ) (hb : b ∈ Ioc lo hi) (hk : ∀ x ∈ Ioc lo hi, k x ≤ n x - n (x - 1))
    (hx : BlockExcess n k b) : Excess n k lo hi := by
  have hle : lo ≤ hi := by simp at hb; omega
  unfold Excess
  rw [telescope n lo hi hle]
  exact Finset.sum_lt_sum hk ⟨b, hb, hx⟩

/-- **#41** Split anywhere inside, at least one half of a stretch that shows more than is known still does. -/
theorem split_keeps (lo m hi : ℕ) (h1 : lo ≤ m) (h2 : m ≤ hi) (h : Excess n k lo hi) :
    Excess n k lo m ∨ Excess n k m hi := by
  by_contra hno
  push_neg at hno
  obtain ⟨ha, hb⟩ := hno
  unfold Excess at *
  have : ∑ b ∈ Ioc lo hi, k b = ∑ b ∈ Ioc lo m, k b + ∑ b ∈ Ioc m hi, k b := by
    rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun x hx hy => by simp at hx hy; omega))]
    congr 1; ext x; simp; omega
  linarith

/-- The halving search: one block left, it is the answer if it shows more than is known; otherwise the first half that
does is searched, else the second. -/
def search (lo hi : ℕ) : Option ℕ :=
  if h : hi ≤ lo + 1 then (if lo < hi ∧ Excess n k lo hi then some hi else none)
  else
    let m := (lo + hi) / 2
    if Excess n k lo m then search lo m else search m hi
  termination_by hi - lo
  decreasing_by all_goals omega

/-- **#41** The halving search, started on a stretch that shows more than is known, ends on a single block in it that
shows more than is known in it: it never misses one. -/
theorem search_finds (lo hi : ℕ) (hlt : lo < hi) (h : Excess n k lo hi) :
    ∃ b, search n k lo hi = some b ∧ lo < b ∧ b ≤ hi ∧ BlockExcess n k b := by
  induction hd : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | _ d ih =>
    rw [search]
    by_cases hle : hi ≤ lo + 1
    · have hb : hi = lo + 1 := by omega
      refine ⟨hi, by simp [hle, hlt, h], hlt, le_rfl, ?_⟩
      unfold Excess at h; unfold BlockExcess
      subst hb; simpa using h
    · simp only [hle, dite_false]
      by_cases hm : Excess n k lo ((lo + hi) / 2)
      · obtain ⟨b, hs, h1, h2, h3⟩ := ih _ (by omega) lo ((lo + hi) / 2) (by omega) hm rfl
        exact ⟨b, by simp [hm, hs], h1, by omega, h3⟩
      · have := (split_keeps n k lo ((lo + hi) / 2) hi (by omega) (by omega) h).resolve_left hm
        obtain ⟨b, hs, h1, h2, h3⟩ := ih _ (by omega) ((lo + hi) / 2) hi (by omega) this rfl
        exact ⟨b, by simp [hm, hs], by omega, h2, h3⟩

/-- **#41** Whatever the search returns is a block in the stretch that shows more than is known in it. -/
theorem search_sound (lo hi b : ℕ) (h : search n k lo hi = some b) : lo < b ∧ b ≤ hi ∧ BlockExcess n k b := by
  induction hd : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | _ d ih =>
    rw [search] at h
    by_cases hle : hi ≤ lo + 1
    · simp only [hle, dite_true] at h
      split_ifs at h with hx
      obtain ⟨hlt, hx⟩ := hx
      cases h
      refine ⟨hlt, le_rfl, ?_⟩
      have hb : b = lo + 1 := by omega
      unfold Excess at hx; unfold BlockExcess; subst hb; simpa using hx
    · simp only [hle, dite_false] at h
      split_ifs at h with hm
      · obtain ⟨h1, h2, h3⟩ := ih _ (by omega) lo ((lo + hi) / 2) h rfl; exact ⟨h1, by omega, h3⟩
      · obtain ⟨h1, h2, h3⟩ := ih _ (by omega) ((lo + hi) / 2) hi h rfl; exact ⟨by omega, h2, h3⟩

/-! ### What is found, and when it is a fee -/

/-- The amount found in a block: the chain's change less what was known. -/
def found (before after known : ℚ) : ℚ := after - before - known

/-- **#41** Known plus found is exactly the chain's change in that block. -/
theorem found_matches (before after known : ℚ) : known + found before after known = after - before := by
  unfold found; ring

/-- A found amount is booked as a network fee only when it is coin going out, no more than the fee cap, in a block
where the wallet sent a transaction. -/
def isFee (amount cap : ℚ) (ownBlock : Bool) : Bool := decide (amount < 0) && decide (-amount ≤ cap) && ownBlock

/-- **#41** Never a fee in a block where the wallet sent nothing (an EIP-7702 drain went out, for the person to say). -/
theorem not_fee_without_own (amount cap : ℚ) : isFee amount cap false = false := by simp [isFee]

/-- **#41** Coin found coming in is never a fee, and coin going out beyond the fee cap is never one. -/
theorem fee_bounds (amount cap : ℚ) (own : Bool) (h : isFee amount cap own = true) : amount < 0 ∧ -amount ≤ cap := by
  simp [isFee] at h; exact ⟨h.1.1, h.1.2⟩

end Kanon.ByBalance
