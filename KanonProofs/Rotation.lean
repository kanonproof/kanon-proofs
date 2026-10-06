/-!
# A swap is a sale, and the new coins cost what came in (#31)

Swapping one token for another (a rotation, say a memecoin into a Stock Token) counts as selling the old
token wherever the country taxes swaps. KANON values the sale at what came in (`T`, in cents), splits it
across the coins on each side by their value, and the last coin takes what's left. So the parts on the side
that left add up to `T` exactly (the sale price), and the parts on the side that arrived add up to `T`
exactly (the new coins' cost): no cent is lost or invented between the old cost basis and the new one.
The app does the same in `toEvents` (`src/lib/money-map/map.ts`).
-/

namespace Kanon.Rotation

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

/-- Split `left` cents across coins weighted `w` (out of `W`): each gets its share of `T`, the last gets what's left. -/
def parts (T W : Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | [_], left => [left]
  | w :: v :: ws, left => let p := min left (T * w / W); p :: parts T W (v :: ws) (left - p)

theorem sum_parts (T W : Nat) : ∀ (ws : List Nat) (left : Nat), ws ≠ [] → sum (parts T W ws left) = left
  | [], _, h => absurd rfl h
  | [_], left, _ => by simp [parts, sum]
  | w :: v :: ws, left, _ => by
    simp only [parts, sum]
    rw [sum_parts T W (v :: ws) _ (by simp)]
    have := Nat.min_le_left left (T * w / W)
    omega

theorem parts_le (T W : Nat) : ∀ (ws : List Nat) (left : Nat), ∀ p ∈ parts T W ws left, p ≤ left
  | [], _ => by simp [parts]
  | [_], left => by simp [parts]
  | w :: v :: ws, left => by
    intro p hp
    simp only [parts, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (parts_le T W (v :: ws) _ p hp) (Nat.sub_le _ _)

/-- A swap: the coins that left (with their values) and the coins that arrived, and `T`, what came in. -/
structure Swap where
  out : List Nat
  inn : List Nat
  T : Nat

def proceeds (s : Swap) : List Nat := parts s.T (sum s.out) s.out s.T
def newCost (s : Swap) : List Nat := parts s.T (sum s.inn) s.inn s.T

/-- **#31** The old coins are sold for exactly what came in. -/
theorem sold_for_what_came_in (s : Swap) (h : s.out ≠ []) : sum (proceeds s) = s.T := sum_parts _ _ _ _ h

/-- **#31** The new coins' cost is exactly what came in, so the new cost basis equals the value received. -/
theorem new_cost_is_value_received (s : Swap) (h : s.inn ≠ []) : sum (newCost s) = s.T := sum_parts _ _ _ _ h

/-- **#31** Nothing is lost or invented between the sale and the new cost. -/
theorem sale_equals_new_cost (s : Swap) (ho : s.out ≠ []) (hi : s.inn ≠ []) : sum (proceeds s) = sum (newCost s) := by
  rw [sold_for_what_came_in s ho, new_cost_is_value_received s hi]

/-- **#31** No single coin's part is more than the whole price. -/
theorem part_at_most_price (s : Swap) : ∀ p ∈ proceeds s, p ≤ s.T := parts_le _ _ _ _

end Kanon.Rotation
