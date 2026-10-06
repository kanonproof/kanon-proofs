/-!
# Price impact (#12)

Selling `q` coins into a constant-product pool holding `B` coins and `Q` of the other side, with a fee of `f`
basis points (k = 10,000 − f is what's kept). The app shows the share of today's value you'd keep:
B·k / (10,000·B + q·k). We prove:
* the share you keep falls as you sell more (price impact rises with size),
* you never keep more than the fee allows,
* the payout the formula gives, rounded down, never takes more out than the pool's x·y = k allows.
-/

namespace Kanon.PriceImpact

/-- Denominator of the share kept: 10,000·B + q·k. -/
def denom (B q k : Nat) : Nat := 10000 * B + q * k

/-- **#12** Selling more never keeps a bigger share: kept(q₂) ≤ kept(q₁) when q₁ ≤ q₂ (cross-multiplied). -/
theorem kept_falls (B k : Nat) {q1 q2 : Nat} (h : q1 ≤ q2) : B * k * denom B q1 k ≤ B * k * denom B q2 k := by
  apply Nat.mul_le_mul_left
  unfold denom
  have := Nat.mul_le_mul_right k h
  omega

/-- **#12** The share kept is never above k / 10,000: the fee is always paid, and any size sale moves the price. -/
theorem kept_le_fee (B q k : Nat) : B * k * 10000 ≤ k * denom B q k := by
  unfold denom
  have e : B * k * 10000 = k * (10000 * B) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [e, Nat.mul_add]
  exact Nat.le_add_right _ _

/-- What the pool pays out, rounded down: Q·q·k / (10,000·B + q·k). -/
def payout (B Q q k : Nat) : Nat := Q * (q * k) / denom B q k

/-- **#12** The pool's x·y never falls: after the sale, (10,000·B + q·k)·(Q − payout) ≥ 10,000·B·Q. -/
theorem k_never_falls (B Q q k : Nat) : 10000 * B * Q ≤ denom B q k * (Q - payout B Q q k) := by
  unfold payout
  have hle : Q * (q * k) / denom B q k * denom B q k ≤ Q * (q * k) := Nat.div_mul_le_self _ _
  generalize Q * (q * k) / denom B q k = p at *
  rw [Nat.mul_sub, Nat.mul_comm (denom B q k) p]
  have e : denom B q k * Q = 10000 * B * Q + Q * (q * k) := by
    unfold denom; rw [Nat.add_mul, Nat.mul_comm (q * k) Q]
  rw [e]
  omega

end Kanon.PriceImpact
