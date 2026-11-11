import Mathlib.Tactic

/-!
# A Form 1099-DA whose reported basis is wrong (#56)

An exchange's Form 1099-DA can report a cost (basis) to the IRS that isn't the right one (coins moved in from
elsewhere, a fee counted another way). The IRS Instructions for Form 8949 (checked 11 Nov 2026) say, when the basis was reported: enter the form's
own proceeds in column (d) and its basis in column (e), code B in column (f), and in column (g) the adjustment; the
gain in column (h) is (d) − (e) + (g). When the basis was reported to the IRS (box G or J), the app
(`src/lib/report/da.ts`, `checkDa`) gives code B with (g) = (e) − the right basis; when a wrong basis was shown but not
reported (box H or K), code B with the right basis in (e) and 0 in (g). Proved below, over exact numbers (the app
rounds each figure to the cent first):

* **Reported basis (G/J): with that adjustment, column (h) is exactly the right gain**, proceeds less the right basis,
  whatever the form reported.
* **It is the only adjustment that does so**, and it is zero exactly when the form's basis is the right one.
* **Unreported basis (H/K): the right basis in (e) and 0 in (g) also give the right gain.**

Not proved here: which box (G, H, J or K) a sale goes in, when code B applies (a basis shown and wrong; none when the
form shows no basis), and proceeds that differ (the app reports those and makes no adjustment for them).
-/

namespace Kanon.DaAdjust

/-- Form 8949 column (h): gain or loss from columns (d), (e) and (g). -/
def colH (d e g : ℚ) : ℚ := d - e + g

/-- The app's column (g) under code B: the form's basis less the right one. -/
def codeB (e right : ℚ) : ℚ := e - right

/-- With the code B adjustment, column (h) is the right gain, whatever basis the form reported. -/
theorem colH_codeB (d e right : ℚ) : colH d e (codeB e right) = d - right := by
  unfold colH codeB; ring

/-- It is the only adjustment that gives the right gain, and it is zero exactly when the form's basis is right. -/
theorem codeB_unique (d e right g : ℚ) :
    (colH d e g = d - right ↔ g = codeB e right) ∧ (codeB e right = 0 ↔ e = right) := by
  unfold colH codeB
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- Unreported basis (box H or K): the right basis in column (e) and 0 in column (g) give the right gain. -/
theorem colH_unreported (d right : ℚ) : colH d right 0 = d - right := by
  unfold colH; ring

end Kanon.DaAdjust
