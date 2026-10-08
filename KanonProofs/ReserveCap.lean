import KanonProofs.FeeSplit

/-!
# The reserve's ceiling (#33)

The reserve takes its 20% of every fee only until it holds `cap` units (six months of running costs). Whatever it
can't take is burned instead, so once the reserve is full, 70% of every fee is burned.
-/

namespace Kanon.Fees

/-- What the reserve keeps of a fee when it already holds `held` and may hold at most `cap`. -/
def reserveKept (fee held cap : Nat) : Nat := min (reserve fee) (cap - held)

/-- The burn: its own share, plus whatever the reserve could not take. -/
def burnWithOverflow (fee held cap : Nat) : Nat := burn fee + (reserve fee - reserveKept fee held cap)

/-- **#33** With the ceiling, every unit of a fee still goes somewhere: costs + burn + reserve = fee. -/
theorem capped_sums (fee held cap : Nat) :
    ops fee + burnWithOverflow fee held cap + reserveKept fee held cap = fee := by
  simp only [burnWithOverflow, reserveKept, reserve, ops, burn]; omega

/-- **#33** The reserve never goes over its ceiling. -/
theorem reserve_never_over_cap (fee held cap : Nat) (h : held ≤ cap) :
    held + reserveKept fee held cap ≤ cap := by
  simp only [reserveKept, reserve, ops, burn]; omega

/-- **#33** The ceiling only ever adds to the burn. -/
theorem burn_never_less (fee held cap : Nat) : burn fee ≤ burnWithOverflow fee held cap := by
  simp only [burnWithOverflow, reserveKept, reserve, ops, burn]; omega

/-- **#33** A full reserve takes nothing: everything except running costs is burned. -/
theorem full_reserve_burns_the_rest (fee held cap : Nat) (h : cap ≤ held) :
    burnWithOverflow fee held cap = fee - ops fee := by
  simp only [burnWithOverflow, reserveKept, reserve, ops, burn]; omega

/-- **#33** "Half of everything is burned": the burn is half the fee, short by at most one unit of rounding. -/
theorem half_is_burned (fee : Nat) : fee ≤ 2 * burn fee + 1 := by
  simp only [burn]; omega

end Kanon.Fees
