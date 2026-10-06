/-!
# Hold check for access tiers (#23)

Access by holding $KANON uses the time-weighted average balance over 7 days: one sample an hour,
168 samples, summed across the user's wallets with each wallet counted once.
-/

namespace Kanon.Hold

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

/-- The 7-day time-weighted average: total of the hourly samples ÷ number of samples. -/
def twa (samples : List Nat) : Nat := if samples.length = 0 then 0 else sum samples / samples.length

/-- Pointwise "holds at least as much at every sample". -/
def AtLeast : List Nat → List Nat → Prop
  | [], [] => True
  | a :: as, b :: bs => a ≥ b ∧ AtLeast as bs
  | _, _ => False

theorem atLeast_len : ∀ (a b : List Nat), AtLeast a b → a.length = b.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by simp [AtLeast] at h; simp [atLeast_len as bs h.2]
  | [], _ :: _, h => by simp [AtLeast] at h
  | _ :: _, [], h => by simp [AtLeast] at h

theorem atLeast_sum : ∀ (a b : List Nat), AtLeast a b → sum b ≤ sum a
  | [], [], _ => Nat.le_refl _
  | x :: as, y :: bs, h => by simp [AtLeast] at h; have := atLeast_sum as bs h.2; simp [sum]; omega
  | [], _ :: _, h => by simp [AtLeast] at h
  | _ :: _, [], h => by simp [AtLeast] at h

/-- **#23** More tokens never means less access: holding at least as much at every hour never lowers the average. -/
theorem more_never_less (a b : List Nat) (h : AtLeast a b) : twa b ≤ twa a := by
  unfold twa
  rw [atLeast_len a b h]
  split
  · exact Nat.le_refl _
  · exact Nat.div_le_div_right (atLeast_sum a b h)

/-- **#23** The average is never above the highest balance held. -/
theorem twa_le_max (samples : List Nat) (m : Nat) (h : ∀ x ∈ samples, x ≤ m) : twa samples ≤ m := by
  unfold twa
  split
  · exact Nat.zero_le _
  · next hl =>
    apply Nat.div_le_of_le_mul
    have : ∀ xs : List Nat, (∀ x ∈ xs, x ≤ m) → sum xs ≤ xs.length * m := by
      intro xs; induction xs with
      | nil => simp [sum]
      | cons x xs ih => intro hx; simp [sum] at *; have := ih hx.2; rw [Nat.add_mul, Nat.one_mul]; omega
    exact this samples h

/-- The user's wallets, each kept once. -/
def dedup : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup (x : Nat) (ws : List Nat) : x ∈ dedup ws ↔ x ∈ ws := by
  induction ws with
  | nil => simp [dedup]
  | cons w ws ih =>
    simp only [dedup]
    split
    · next h => rw [ih]; constructor
                · intro hx; exact List.mem_cons_of_mem _ hx
                · intro hx; rcases List.mem_cons.mp hx with rfl | hx
                  · exact ih.mp h
                  · exact hx
    · simp [ih]

/-- **#23** No wallet counted twice, and none dropped: every wallet appears exactly once. -/
theorem dedup_once (ws : List Nat) : (dedup ws).Nodup := by
  induction ws with
  | nil => simp [dedup]
  | cons w ws ih =>
    simp only [dedup]
    split
    · exact ih
    · next h => exact List.nodup_cons.mpr ⟨h, ih⟩

/-- Grace period: access continues for `grace` hours after the average drops below the line. -/
def access (avg line hoursBelow grace : Nat) : Bool := avg ≥ line || hoursBelow < grace

/-- **#23** Holding enough always gives access, whatever the grace counter says. -/
theorem enough_gives_access (avg line h g : Nat) (hl : line ≤ avg) : access avg line h g = true := by
  simp [access, hl]

end Kanon.Hold
