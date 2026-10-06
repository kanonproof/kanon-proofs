/-!
# Payments in USDC (#24)

Every USDC unit paid in is split into burned + costs + pending, with nothing lost to rounding.
Burns take their share rounded down, costs are paid only from what's left, and the remainder is
pending until the next run.
-/

namespace Kanon.Pay

structure Split where
  burned : Nat
  costs : Nat
  pending : Nat

/-- `burnBp`: burn share in basis points; `due`: costs owed this run. -/
def split (paid burnBp due : Nat) : Split :=
  let burned := paid * burnBp / 10000
  let available := paid - burned
  let costs := min due available
  { burned, costs, pending := available - costs }

/-- **#24** Paid in = burned + costs + pending, exactly. -/
theorem conserved (paid bp due : Nat) (hbp : bp ≤ 10000) :
    (split paid bp due).burned + (split paid bp due).costs + (split paid bp due).pending = paid := by
  simp only [split]
  have hb : paid * bp / 10000 ≤ paid := by
    apply Nat.div_le_of_le_mul
    show paid * bp ≤ 10000 * paid
    rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ hbp
  have hm := Nat.min_le_right due (paid - paid * bp / 10000)
  omega

/-- **#24** Costs never exceed what was owed, and never dip into the burn. -/
theorem costs_bounded (paid bp due : Nat) (hbp : bp ≤ 10000) : (split paid bp due).costs ≤ due ∧
    (split paid bp due).burned + (split paid bp due).costs ≤ paid := by
  simp only [split]
  have hb : paid * bp / 10000 ≤ paid := by
    apply Nat.div_le_of_le_mul
    show paid * bp ≤ 10000 * paid
    rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ hbp
  have := Nat.min_le_left due (paid - paid * bp / 10000)
  have := Nat.min_le_right due (paid - paid * bp / 10000)
  omega

end Kanon.Pay
