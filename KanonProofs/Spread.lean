/-!
# Brazil's monthly planner (#32)

Brazil exempts the profit of any month whose crypto sales stay at R$35,000 or less. The planner spreads an
amount: this month only up to what's left of the limit after what's already been sold, then the limit each month
until the amount is sold. Amounts are in cents, as whole numbers. The app uses this rule in `src/lib/exit/spread.ts`.

Shown here: the months add up to exactly the amount; every month stays within the limit, this month counting what
was already sold; no month sells nothing; and no plan within the limit finishes sooner: any plan that sells some part
this month (within what's left of the limit) and then up to the limit a month needs at least as many months
after this one.
-/

namespace Kanon.Spread

/-- After this month: up to `cap` a month until `rest` is sold. `fuel` bounds the months (the amount itself is enough). -/
def chunks (cap : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, rest => if rest = 0 then [] else min cap rest :: chunks cap fuel (rest - min cap rest)

/-- This month's part: what's left of the limit after `sold`, and never more than the amount. -/
def first (cap sold amount : Nat) : Nat := min (cap - sold) amount

/-- The whole plan, this month first (left out if there's no room this month). -/
def plan (cap sold amount : Nat) : List Nat :=
  (if first cap sold amount > 0 then [first cap sold amount] else []) ++ chunks cap amount (amount - first cap sold amount)

theorem chunks_sum (cap : Nat) (hc : 0 < cap) : ∀ fuel rest, rest ≤ fuel → (chunks cap fuel rest).sum = rest := by
  intro fuel
  induction fuel with
  | zero => intro rest h; simp [chunks]; omega
  | succ n ih =>
    intro rest h
    by_cases h0 : rest = 0
    · simp [chunks, h0]
    · simp only [chunks, h0, if_false, List.sum_cons]
      rw [ih (rest - min cap rest) (by omega)]
      omega

theorem chunks_within (cap : Nat) (hc : 0 < cap) : ∀ fuel rest, ∀ x ∈ chunks cap fuel rest, 0 < x ∧ x ≤ cap := by
  intro fuel
  induction fuel with
  | zero => intro rest x hx; simp [chunks] at hx
  | succ n ih =>
    intro rest x hx
    by_cases h0 : rest = 0
    · simp [chunks, h0] at hx
    · simp only [chunks, h0, if_false, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact ih _ x hx

theorem chunks_length (cap : Nat) (hc : 0 < cap) : ∀ fuel rest, rest ≤ fuel →
    (chunks cap fuel rest).length = (rest + cap - 1) / cap := by
  intro fuel
  induction fuel with
  | zero =>
    intro rest h
    have : rest = 0 := by omega
    subst this; simp [chunks]; exact (Nat.div_eq_of_lt (by omega)).symm
  | succ n ih =>
    intro rest h
    by_cases h0 : rest = 0
    · subst h0; simp [chunks]; exact (Nat.div_eq_of_lt (by omega)).symm
    · simp only [chunks, h0, if_false, List.length_cons]
      rw [ih (rest - min cap rest) (by omega)]
      by_cases hr : rest ≤ cap
      · have hm : min cap rest = rest := by omega
        rw [hm, Nat.sub_self, Nat.zero_add, Nat.div_eq_of_lt (by omega : cap - 1 < cap)]
        exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
      · have hm : min cap rest = cap := by omega
        rw [hm, ← Nat.add_div_right _ hc]
        congr 1
        omega

/-- Any list of parts each within the limit can't sell more than its length times the limit. -/
theorem sum_le_length_mul (cap : Nat) : ∀ L : List Nat, (∀ x ∈ L, x ≤ cap) → L.sum ≤ L.length * cap := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    intro h
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have := h a (List.mem_cons_self ..)
    omega

/-- **#32** The months add up to exactly the amount. -/
theorem plan_sum (cap sold amount : Nat) (hc : 0 < cap) : (plan cap sold amount).sum = amount := by
  unfold plan
  rw [List.sum_append_nat, chunks_sum cap hc amount _ (by unfold first; omega)]
  split <;> simp <;> unfold first at * <;> omega

/-- **#32** This month, what's already sold plus the plan's part stays within the limit. -/
theorem first_within (cap sold amount : Nat) (h : first cap sold amount > 0) : sold + first cap sold amount ≤ cap := by
  unfold first at *; omega

/-- **#32** Every month of the plan sells something and stays within the limit. -/
theorem plan_within (cap sold amount : Nat) (hc : 0 < cap) : ∀ x ∈ plan cap sold amount, 0 < x ∧ x ≤ cap := by
  intro x hx
  unfold plan at hx
  rcases List.mem_append.mp hx with h | h
  · split at h
    · simp at h; subst h; unfold first at *; omega
    · simp at h
  · exact chunks_within cap hc _ _ x h

/-- **#32** After this month, the plan takes the fewest months: no plan within the limit sells the rest in fewer. -/
theorem fewest_months (cap sold amount : Nat) (hc : 0 < cap) (L : List Nat)
    (within : ∀ x ∈ L, x ≤ cap) (sells : L.sum = amount - first cap sold amount) :
    (chunks cap amount (amount - first cap sold amount)).length ≤ L.length := by
  rw [chunks_length cap hc _ _ (by unfold first; omega)]
  have hs := sum_le_length_mul cap L within
  rw [sells] at hs
  have : (amount - first cap sold amount + cap - 1) / cap < L.length + 1 := by
    rw [Nat.div_lt_iff_lt_mul hc, Nat.succ_mul]
    omega
  omega

/-- **#32** No plan within the limit finishes sooner: whatever `now` it sells this month (within what's left of the
limit) and however it splits the rest into months of at most the limit, it needs at least as many later months. -/
theorem finishes_soonest (cap sold amount now : Nat) (hc : 0 < cap) (later : List Nat)
    (room : now ≤ cap - sold) (within : ∀ x ∈ later, x ≤ cap) (sells : now + later.sum = amount) :
    (chunks cap amount (amount - first cap sold amount)).length ≤ later.length := by
  rw [chunks_length cap hc _ _ (by unfold first; omega)]
  have hs := sum_le_length_mul cap later within
  have : (amount - first cap sold amount + cap - 1) / cap < later.length + 1 := by
    rw [Nat.div_lt_iff_lt_mul hc, Nat.succ_mul]
    unfold first
    omega
  omega

end Kanon.Spread
