/-!
# Cash-out route ranking (#30)

The cash-out routes shown in My money are ranked by what they cost on the user's own amount (published fees, in
cents). Shown here: the ranking never puts a cheaper route below a dearer one, and never drops or adds a route.
The app ranks this way in
`cheapest()` (`src/lib/cashout/data.ts`); speed isn't part of the ranking, so it can't push a dearer route up.
-/

namespace Kanon.Ranking

/-- A route and what it costs on the user's amount, in cents. -/
structure Route where
  name : String
  fee : Nat

def le (a b : Route) : Bool := decide (a.fee ≤ b.fee)

/-- The ranking: cheapest first. -/
def rank (routes : List Route) : List Route := routes.mergeSort le

/-- **#30** Every route ahead of another in the ranking costs no more than it. -/
theorem cheaper_first (routes : List Route) : (rank routes).Pairwise (fun a b => a.fee ≤ b.fee) := by
  have h := List.sorted_mergeSort (le := le)
    (by intro a b c hab hbc; simp [le] at *; omega)
    (by intro a b; simp [le]; omega) routes
  exact h.imp (fun {a b} hab => by simpa [le] using hab)

/-- **#30** A route that costs less is never ranked below one that costs more. -/
theorem never_below_dearer (routes : List Route) (i j : Nat) (hi : i < (rank routes).length) (hj : j < (rank routes).length)
    (order : i < j) : ((rank routes)[i]).fee ≤ ((rank routes)[j]).fee :=
  List.pairwise_iff_getElem.mp (cheaper_first routes) i j hi hj order

/-- **#30** The ranking is the same routes, each once: nothing dropped, nothing added. -/
theorem same_routes (routes : List Route) : (rank routes).Perm routes := List.mergeSort_perm routes le

end Kanon.Ranking
