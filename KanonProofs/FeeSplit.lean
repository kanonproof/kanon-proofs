/-!
# Creator fees: the 50/30/20 split and burns (#18)

Fees arrive in whole smallest units. 50% runs the agent and pays the team, 30% buys and burns
$KANON, 20% goes to the reserve. Dust rule (explicit): the two percentages are rounded down and
every unit of rounding goes to the reserve, so nothing is lost or invented.
-/

namespace Kanon.Fees

def ops (fee : Nat) : Nat := fee * 50 / 100
def burn (fee : Nat) : Nat := fee * 30 / 100
def reserve (fee : Nat) : Nat := fee - ops fee - burn fee

/-- **#18** The split sums exactly to the fee. -/
theorem split_sums (fee : Nat) : ops fee + burn fee + reserve fee = fee := by
  unfold reserve ops burn; omega

/-- **#18** Neither rounded share is ever more than its percentage. -/
theorem ops_le (fee : Nat) : ops fee * 100 ≤ fee * 50 := by unfold ops; exact Nat.div_mul_le_self _ _
theorem burn_le (fee : Nat) : burn fee * 100 ≤ fee * 30 := by unfold burn; exact Nat.div_mul_le_self _ _

/-- **#18** Dust rule: the reserve gets at least its 20%; rounding only ever adds to it, by under 2 units. -/
theorem reserve_ge (fee : Nat) : fee * 20 ≤ reserve fee * 100 := by
  have h1 := ops_le fee; have h2 := burn_le fee; unfold reserve; omega

theorem reserve_dust (fee : Nat) : reserve fee * 100 < fee * 20 + 200 := by
  unfold reserve ops burn; omega

/-- A burn goes through the token's burn function: supply falls by exactly what's burned. -/
def burnSupply (supply burned : Nat) : Nat := supply - burned

/-- **#18** Supply only falls. -/
theorem supply_falls (supply burned : Nat) : burnSupply supply burned ≤ supply := Nat.sub_le _ _

theorem supply_exact (supply burned : Nat) (h : burned ≤ supply) : burnSupply supply burned + burned = supply := by
  unfold burnSupply; omega

/-- **#18** The minimum-out on the buy-back swap bounds the price paid: at most `amountIn / minOut` a token. -/
theorem minOut_bounds_price (amountIn minOut out : Nat) (h : minOut ≤ out) : amountIn * minOut ≤ amountIn * out :=
  Nat.mul_le_mul_left _ h

end Kanon.Fees
