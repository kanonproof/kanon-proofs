/-!
# Rounding (#6)

Amounts are worked out exactly, in a smaller unit (`s` of them make one cent), and only rounded to whole
cents to be shown. A shown amount is rounded half up, so it is never more than half a cent away from the exact
figure. KANON's own tax estimates are rounded up instead, so a shown estimate is never below the exact tax and
less than a cent above it. (Where a tax office prescribes its own rounding, as Brazil does for the DARF, the
engine follows the office.)
-/

namespace Kanon.Rounding

/-- Round `x` (in units of 1/s cent) half up to whole cents. -/
def halfUp (s x : Nat) : Nat := (2 * x + s) / (2 * s)

/-- Round `x` up to whole cents. -/
def up (s x : Nat) : Nat := (x + s - 1) / s

/-- **#6** A shown amount is within half a cent of the exact one: |shown − exact| ≤ ½ cent. -/
theorem halfUp_close (s x : Nat) (hs : 0 < s) :
    2 * x ≤ 2 * (s * halfUp s x) + s ∧ 2 * (s * halfUp s x) ≤ 2 * x + s := by
  unfold halfUp
  have hd := Nat.div_add_mod (2 * x + s) (2 * s)
  have hm := Nat.mod_lt (2 * x + s) (show 0 < 2 * s by omega)
  generalize (2 * x + s) / (2 * s) = q at *
  generalize (2 * x + s) % (2 * s) = r at *
  rw [Nat.mul_assoc] at hd
  generalize s * q = A at *
  omega

/-- **#6** A tax estimate is never below the exact tax, and less than one cent above it. -/
theorem up_never_under (s x : Nat) (hs : 0 < s) : x ≤ s * up s x ∧ s * up s x < x + s := by
  unfold up
  have hd := Nat.div_add_mod (x + s - 1) s
  have hm := Nat.mod_lt (x + s - 1) hs
  generalize (x + s - 1) / s = q at *
  generalize (x + s - 1) % s = r at *
  generalize s * q = A at *
  omega

/-- **#6** Rounding up is never below rounding half up: an estimate never shows less tax than the nearest cent. -/
theorem halfUp_le_up (s x : Nat) (hs : 0 < s) : halfUp s x ≤ up s x := by
  have h1 := halfUp_close s x hs
  have h2 := up_never_under s x hs
  -- s·halfUp ≤ x + s/2 < x + s ≤ s·up + s, so halfUp < up + 1.
  have : s * halfUp s x < s * (up s x + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

end Kanon.Rounding
