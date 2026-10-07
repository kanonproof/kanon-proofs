/-!
# Exit-card grade (#25)

After a take-profit step is reached on day `hit`, the grade is a fixed function of the person's recorded sales
of that exact coin (as days), how complete the data is, whether the history was read after the step was
reached, and whether it includes that coin: "followed" if there is a sale on a later day; "not known yet" if
the only sales are the same day (they can't be put in order); "skipped" only with 100% complete data, read
after the step, covering that coin, and no such sale; otherwise "not known yet". The app's grade is
`src/lib/watch/grade.ts`.
-/

namespace Kanon.Grade

inductive Grade | followed | skipped | unknown
deriving DecidableEq, Repr

def grade (hit : Nat) (sales : List Nat) (complete : Nat) (readAfter covers : Bool) : Grade :=
  if sales.any (fun d => decide (d > hit)) then .followed
  else if sales.any (fun d => decide (d = hit)) then .unknown
  else if complete ≥ 100 ∧ readAfter = true ∧ covers = true then .skipped else .unknown

/-- **#25** Never "skipped" while the data is less than 100% complete. -/
theorem never_skipped_incomplete (hit c : Nat) (sales : List Nat) (r v : Bool) (h : c < 100) :
    grade hit sales c r v ≠ .skipped := by
  unfold grade
  split
  · simp
  · split
    · simp
    · rw [if_neg (by omega)]; simp

/-- **#25** "Skipped" only from a complete history, read after the step was reached, that includes the coin,
with no sale of it since that day. -/
theorem skipped_means (hit c : Nat) (sales : List Nat) (r v : Bool) (h : grade hit sales c r v = .skipped) :
    c ≥ 100 ∧ r = true ∧ v = true ∧ ∀ d ∈ sales, d < hit := by
  unfold grade at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · simp at h
    · rename_i h2
      split at h
      · rename_i h3
        refine ⟨h3.1, h3.2.1, h3.2.2, fun d hd => ?_⟩
        have a : ¬ d > hit := fun g => h1 (List.any_eq_true.mpr ⟨d, hd, by simpa using g⟩)
        have b : ¬ d = hit := fun g => h2 (List.any_eq_true.mpr ⟨d, hd, by simpa using g⟩)
        omega
      · simp at h

/-- **#25** "Followed" exactly when there is a recorded sale of that coin on a later day than the step was reached. -/
theorem followed_iff (hit c : Nat) (sales : List Nat) (r v : Bool) :
    grade hit sales c r v = .followed ↔ ∃ d ∈ sales, d > hit := by
  unfold grade
  constructor
  · intro h
    split at h
    · rename_i hs; simpa using hs
    · split at h
      · simp at h
      · split at h <;> simp at h
  · intro ⟨d, hd, hgt⟩
    have : sales.any (fun d => decide (d > hit)) = true := List.any_eq_true.mpr ⟨d, hd, by simpa using hgt⟩
    simp [this]

end Kanon.Grade
