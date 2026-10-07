/-!
# No look-ahead (#15)

What KANON works out at day `t` uses only prices up to `t`. Prices are a function from day to price (in cents).
Two price histories that agree on every day up to `t` give the same answer at `t`, so a later price can never
change it. Covered: the "missed sale" finding (the best price since purchase) and the Watcher's check of a
take-profit step. The app: `peakSince` in `src/lib/money-map/prices.ts` (days from the purchase up to today) and
the Watcher's check (today's price against the target).
-/

namespace Kanon.LookAhead

/-- Best price from day `start` to day `t`, inclusive. -/
def peak (p : Nat → Nat) (start t : Nat) : Nat :=
  (List.range' start (t + 1 - start)).foldl (fun m d => max m (p d)) 0

/-- The Watcher's check at day `t`: has the price reached the target? -/
def reached (p : Nat → Nat) (target t : Nat) : Bool := decide (p t ≥ target)

theorem foldl_congr (p q : Nat → Nat) : ∀ (l : List Nat) (acc : Nat), (∀ d ∈ l, p d = q d) →
    l.foldl (fun m d => max m (p d)) acc = l.foldl (fun m d => max m (q d)) acc
  | [], _, _ => rfl
  | d :: ds, acc, h => by
    simp only [List.foldl]
    rw [h d (by simp)]
    exact foldl_congr p q ds _ (fun x hx => h x (by simp [hx]))

/-- **#15** The best price since purchase, worked out at day `t`, ignores every price after `t`. -/
theorem peak_no_lookahead (p q : Nat → Nat) (start t : Nat) (h : ∀ d ≤ t, p d = q d) : peak p start t = peak q start t := by
  unfold peak
  apply foldl_congr
  intro d hd
  rw [List.mem_range'_1] at hd
  exact h d (by omega)

/-- **#15** The Watcher's check at day `t` ignores every price after `t`. -/
theorem reached_no_lookahead (p q : Nat → Nat) (target t : Nat) (h : ∀ d ≤ t, p d = q d) : reached p target t = reached q target t := by
  unfold reached; rw [h t (Nat.le_refl t)]

theorem foldl_attained (p : Nat → Nat) (start t : Nat) : ∀ (l : List Nat) (acc : Nat), (∀ d ∈ l, start ≤ d ∧ d ≤ t) →
    (acc = 0 ∨ ∃ d, start ≤ d ∧ d ≤ t ∧ acc = p d) →
    (l.foldl (fun m d => max m (p d)) acc = 0 ∨ ∃ d, start ≤ d ∧ d ≤ t ∧ l.foldl (fun m d => max m (p d)) acc = p d)
  | [], _, _, h => h
  | x :: xs, acc, hm, h => by
    simp only [List.foldl]
    apply foldl_attained p start t xs _ (fun d hd => hm d (List.mem_cons_of_mem _ hd))
    have hx := hm x (List.mem_cons_self ..)
    by_cases hle : acc ≤ p x
    · exact Or.inr ⟨x, hx.1, hx.2, by omega⟩
    · rw [Nat.max_eq_left (by omega)]; exact h

/-- **#15** The best price is one of the prices in the window (never made up), or 0 for an empty window. -/
theorem peak_attained (p : Nat → Nat) (start t : Nat) : peak p start t = 0 ∨ ∃ d, start ≤ d ∧ d ≤ t ∧ peak p start t = p d := by
  unfold peak
  exact foldl_attained p start t _ 0 (fun d hd => by rw [List.mem_range'_1] at hd; omega) (Or.inl rfl)

end Kanon.LookAhead
