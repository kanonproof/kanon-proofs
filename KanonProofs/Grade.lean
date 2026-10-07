/-!
# Exit-card grade (#25)

After a take-profit step is reached (on day `hit`), the grade is a fixed function of the person's recorded sales
of that coin and of how complete the data is: "followed" if there is a sale on or after `hit`; "skipped" only
when the data is 100% complete and there is none; otherwise "not known yet". Days are numbers. The app's
grade is `src/lib/watch/grade.ts`.
-/

namespace Kanon.Grade

inductive Grade | followed | skipped | unknown
deriving DecidableEq, Repr

/-- Sales of the coin, as days. `complete` is the data-complete score, 0–100. -/
def grade (hit : Nat) (sales : List Nat) (complete : Nat) : Grade :=
  if sales.any (fun d => decide (d ≥ hit)) then .followed
  else if complete ≥ 100 then .skipped else .unknown

/-- **#25** Never "skipped" while the data is less than 100% complete. -/
theorem never_skipped_incomplete (hit : Nat) (sales : List Nat) (c : Nat) (h : c < 100) : grade hit sales c ≠ .skipped := by
  unfold grade
  split
  · simp
  · rw [if_neg (by omega)]; simp

/-- **#25** "Followed" exactly when there is a recorded sale on or after the day the step was reached. -/
theorem followed_iff (hit : Nat) (sales : List Nat) (c : Nat) : grade hit sales c = .followed ↔ ∃ d ∈ sales, d ≥ hit := by
  unfold grade
  constructor
  · intro h
    split at h
    · rename_i hs; simpa using hs
    · split at h <;> simp at h
  · intro ⟨d, hd, hge⟩
    have : sales.any (fun d => decide (d ≥ hit)) = true := List.any_eq_true.mpr ⟨d, hd, by simpa using hge⟩
    simp [this]

/-- **#25** "Skipped" only with complete data and no sale since the step was reached. -/
theorem skipped_means (hit : Nat) (sales : List Nat) (c : Nat) (h : grade hit sales c = .skipped) :
    c ≥ 100 ∧ ∀ d ∈ sales, d < hit := by
  unfold grade at h
  split at h
  · simp at h
  · rename_i hs
    split at h
    · rename_i hc
      refine ⟨hc, fun d hd => ?_⟩
      have : ¬ (d ≥ hit) := fun hge => hs (List.any_eq_true.mpr ⟨d, hd, by simpa using hge⟩)
      omega
    · simp at h

end Kanon.Grade
