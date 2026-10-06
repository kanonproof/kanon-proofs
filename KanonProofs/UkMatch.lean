/-!
# UK matching rules (#5, UK part)

HMRC matches each sale of a token in a fixed order: buys on the same day, then buys in the next
30 days (earliest first), then the section 104 pool. Whatever is still unmatched has no known cost.
We prove the parts of every sale add up exactly to what was sold, that no purchase is ever used
more than once, and that the pool never gives out more cost than it holds.
-/

namespace Kanon.UkMatch

def total : List Nat → Nat
  | [] => 0
  | a :: as => a + total as

/-- Take up to `want` from available amounts, earliest first: (taken from each, left of each, still wanted). -/
def take : Nat → List Nat → List Nat × List Nat × Nat
  | w, [] => ([], [], w)
  | w, a :: as =>
    let r := take (w - min w a) as
    (min w a :: r.1, (a - min w a) :: r.2.1, r.2.2)

theorem take_sum (w : Nat) (as : List Nat) : total (take w as).1 + (take w as).2.2 = w := by
  induction as generalizing w with
  | nil => simp [take, total]
  | cons a as ih =>
    simp only [take, total]
    have := ih (w - min w a)
    have := Nat.min_le_left w a
    omega

/-- Taken plus left is exactly what each purchase had: none is used twice or beyond its size. -/
theorem take_each (w : Nat) (as : List Nat) :
    List.zipWith (· + ·) (take w as).1 (take w as).2.1 = as := by
  induction as generalizing w with
  | nil => simp [take]
  | cons a as ih =>
    simp only [take, List.zipWith_cons_cons, ih, List.cons.injEq, and_true]
    have := Nat.min_le_right w a
    omega

theorem take_left (w : Nat) (as : List Nat) : total (take w as).1 + total (take w as).2.1 = total as := by
  induction as generalizing w with
  | nil => simp [take, total]
  | cons a as ih =>
    simp only [take, total]
    have := ih (w - min w a)
    have := Nat.min_le_right w a
    omega

/-- One sale on a day: `sell` sold and `buy` bought that day, `window` the buys left in the next 30 days,
`pool` the section 104 pool's size. -/
structure Sale where
  sameDay : Nat
  thirtyDay : List Nat
  fromPool : Nat
  unknown : Nat

def matchSale (sell buy : Nat) (window : List Nat) (pool : Nat) : Sale :=
  let m := min sell buy
  let t := take (sell - m) window
  let p := min t.2.2 pool
  ⟨m, t.1, p, t.2.2 - p⟩

/-- **#5** Same day, 30 days, pool and unknown add up exactly to what was sold. -/
theorem parts_sum (sell buy : Nat) (window : List Nat) (pool : Nat) :
    let s := matchSale sell buy window pool
    s.sameDay + total s.thirtyDay + s.fromPool + s.unknown = sell := by
  simp only [matchSale]
  have := take_sum (sell - min sell buy) window
  have := Nat.min_le_left sell buy
  have := Nat.min_le_left (take (sell - min sell buy) window).2.2 pool
  omega

/-- **#5** The same-day match never uses more than was bought that day, and the pool never gives out more than it holds. -/
theorem within_limits (sell buy : Nat) (window : List Nat) (pool : Nat) :
    (matchSale sell buy window pool).sameDay ≤ buy ∧ (matchSale sell buy window pool).fromPool ≤ pool := by
  simp only [matchSale]
  exact ⟨Nat.min_le_right _ _, Nat.min_le_right _ _⟩

/-- **#5** Every buy in the 30-day window: used by this sale plus what's left for later equals what was bought. -/
theorem window_once (sell buy : Nat) (window : List Nat) :
    List.zipWith (· + ·) (take (sell - min sell buy) window).1 (take (sell - min sell buy) window).2.1 = window :=
  take_each _ _

/-- Cost taken from the pool for `q` of its `n` tokens: its share, rounded down. -/
def poolCost (cost n q : Nat) : Nat := cost * q / n

/-- **#5** The pool's cost taken out never exceeds what it holds, so the pool's cost can never go negative. -/
theorem pool_cost_le (cost n q : Nat) (h : q ≤ n) : poolCost cost n q ≤ cost := by
  unfold poolCost
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · exact Nat.div_le_of_le_mul (by have := Nat.mul_le_mul_left cost h; rw [Nat.mul_comm n cost]; exact this)

end Kanon.UkMatch
