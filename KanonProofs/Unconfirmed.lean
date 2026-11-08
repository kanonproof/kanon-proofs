import Mathlib.Tactic

/-!
# Coins from an account KANON can't see (#53)

When coins arrive from an account KANON can't see and the person hasn't said what they were, the app books them at
their value on arrival, but only as a guess: the lot is marked unconfirmed (`src/lib/engine/lots.ts`, `unconfirmed`).
Spam priced high on arrival would otherwise show a large loss that never happened. The tax-loss finder and the
"worth less than you paid" finding (`src/lib/findings/harvest.ts` `counted`, `src/lib/findings/findings.ts` `lossOf`)
count each lot's result `g` (value today less cost) through `counted`: an unconfirmed lot's gain counts, its loss
counts as nothing. Proved below, for one lot and for a holding's lots together:

* **An unconfirmed lot never adds a loss, and its gain counts in full**; a confirmed lot counts exactly its result.
* **Counting never shows more loss than the plain sum over the lots**, and the loss shown is never more than the
  confirmed lots' losses added up lot by lot.
* **When no lot is unconfirmed, the counted total equals the plain sum over the lots.**

(For tax figures the app is cautious the other way: tax if sold and every country's report count an unconfirmed
lot as costing nothing until the person answers, like coins never seen arriving. That isn't part of this statement.)
-/

namespace Kanon.Unconfirmed

/-- A lot's result (value today less cost) as counted: an unconfirmed lot's loss counts as nothing. -/
def counted (g : ℚ) (unconfirmed : Bool) : ℚ := if unconfirmed && decide (g < 0) then 0 else g

/-- A holding's lots, each with its result and whether its cost is only a guess. -/
def total (lots : List (ℚ × Bool)) : ℚ := (lots.map fun l => counted l.1 l.2).sum

/-- The plain total, every lot at its booked cost. -/
def plain (lots : List (ℚ × Bool)) : ℚ := (lots.map fun l => l.1).sum

/-- The confirmed lots' losses, added up lot by lot. -/
def confirmedLoss (lots : List (ℚ × Bool)) : ℚ := (lots.map fun l => if l.2 then 0 else max (-l.1) 0).sum

/-- **#53** An unconfirmed lot never adds a loss and its gain counts in full (it counts as `max g 0`); a confirmed lot
counts exactly its result. -/
theorem lot_rule (g : ℚ) : counted g true = max g 0 ∧ 0 ≤ counted g true ∧ counted g false = g := by
  unfold counted
  refine ⟨?_, ?_⟩
  · by_cases h : g < 0
    · simp only [h, decide_true, Bool.and_self, if_true]; exact (max_eq_right (le_of_lt h)).symm
    · simp only [h, decide_false, Bool.and_false, Bool.false_eq_true, if_false]; exact (max_eq_left (not_lt.mp h)).symm
  constructor
  · by_cases h : g < 0
    · simp [h]
    · simp [h]; linarith
  · simp

/-- **#53** Counting never shows more loss than the plain sum: each lot counts at least its result. -/
theorem never_more_loss (lots : List (ℚ × Bool)) : plain lots ≤ total lots := by
  induction lots with
  | nil => simp [plain, total]
  | cons l ls ih =>
    simp only [plain, total, List.map_cons, List.sum_cons] at *
    have : l.1 ≤ counted l.1 l.2 := by
      unfold counted
      by_cases h : l.1 < 0
      · cases l.2 <;> simp [h]; linarith
      · cases l.2 <;> simp [h]
    linarith

/-- One lot: what it takes off the counted total is at most its confirmed loss, which is never negative. -/
lemma lot_step (g : ℚ) (u : Bool) :
    -counted g u ≤ (if u then 0 else max (-g) 0) ∧ 0 ≤ (if u then 0 else max (-g) 0) := by
  cases u
  · simp only [counted, Bool.false_and, Bool.false_eq_true, if_false]
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  · simp only [counted, Bool.true_and, if_true]
    refine ⟨?_, le_refl 0⟩
    by_cases h : g < 0
    · simp [h]
    · simp [h]; linarith

/-- **#53** The loss shown (the counted total below zero) is never more than the confirmed lots' losses. -/
theorem loss_from_confirmed_only (lots : List (ℚ × Bool)) : max (-total lots) 0 ≤ confirmedLoss lots := by
  have key : ∀ ls : List (ℚ × Bool), -total ls ≤ confirmedLoss ls ∧ 0 ≤ confirmedLoss ls := by
    intro ls
    induction ls with
    | nil => simp [total, confirmedLoss]
    | cons l ls ih =>
      simp only [total, confirmedLoss, List.map_cons, List.sum_cons] at *
      obtain ⟨a, b⟩ := lot_step l.1 l.2
      constructor <;> linarith [ih.1, ih.2]
  exact max_le (key lots).1 (key lots).2

/-- **#53** When no lot is unconfirmed, the counted total equals the plain sum over the lots. -/
theorem answered_unchanged (lots : List (ℚ × Bool)) (h : ∀ l ∈ lots, l.2 = false) : total lots = plain lots := by
  induction lots with
  | nil => simp [plain, total]
  | cons l ls ih =>
    simp only [plain, total, List.map_cons, List.sum_cons] at *
    have hl : l.2 = false := h l (by simp)
    rw [ih (fun x hx => h x (by simp [hx]))]
    simp [counted, hl]

end Kanon.Unconfirmed
