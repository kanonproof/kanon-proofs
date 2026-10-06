/-!
# "Data complete" score (#22)

Score = value we understand ÷ all value moved, as a whole percent rounded down; 100 when nothing
has moved. Fixing a gap moves value from "unexplained" to "understood".
-/

namespace Kanon.Complete

def score (known unknown : Nat) : Nat :=
  if known + unknown = 0 then 100 else known * 100 / (known + unknown)

/-- **#22** The score is always between 0 and 100. -/
theorem score_le_100 (k u : Nat) : score k u ≤ 100 := by
  unfold score
  split
  · exact Nat.le_refl _
  · apply Nat.div_le_of_le_mul
    show k * 100 ≤ (k + u) * 100
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- **#22** Fixing a gap (explaining `x` of the unexplained value) never lowers the score. -/
theorem fix_never_lowers (k u x : Nat) (hx : x ≤ u) : score k u ≤ score (k + x) (u - x) := by
  unfold score
  have e : k + x + (u - x) = k + u := by omega
  rw [e]
  by_cases h : k + u = 0
  · simp [h]
  · simp only [h, if_false]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

/-- **#22** The share resting on estimates is exactly the rest: understood + estimated = 100%
before rounding (shown as two whole numbers, the estimate rounded up). -/
theorem shares_exact (k u : Nat) : k * 100 + u * 100 = (k + u) * 100 := by
  rw [Nat.add_mul]

end Kanon.Complete
