import KanonProofs.Lots
/-!
# Cash-out plans (#10, #11)

A plan is a list of (lot number, coins to sell). We prove the planner's plans are always valid —
only lots that exist, no lot twice, never more than a lot holds — and that they raise the cash
asked for when the coins are there. #11: the planner picks the cheapest of its candidate plans,
and the country's default method is always where it starts, so the chosen plan's tax is never
higher than the default's.
-/

namespace Kanon.CashOut
open Kanon.Lots

abbrev Plan := List (Nat × Nat)

/-- Valid: every step names an existing lot, sells at most what it holds, and no lot appears twice. -/
def Valid (lots : List Lot) (p : Plan) : Prop :=
  (p.map Prod.fst).Nodup ∧ ∀ s ∈ p, ∃ l, lots[s.1]? = some l ∧ s.2 ≤ l.qty

/-- Oldest-first plan for `q` coins, starting at lot number `i`. -/
def fifoPlan : List Lot → Nat → Nat → Plan
  | [], _, _ => []
  | l :: ls, i, q =>
    if q = 0 then []
    else if q ≤ l.qty then [(i, q)]
    else (i, l.qty) :: fifoPlan ls (i + 1) (q - l.qty)

theorem fifoPlan_idx (ls : List Lot) (i q : Nat) : ∀ s ∈ fifoPlan ls i q, i ≤ s.1 ∧ s.1 < i + ls.length := by
  induction ls generalizing i q with
  | nil => simp [fifoPlan]
  | cons l ls ih =>
    intro s hs
    simp only [fifoPlan] at hs
    split at hs
    · simp at hs
    · split at hs
      · simp at hs; subst hs; simp
      · simp at hs
        rcases hs with rfl | hs
        · simp
        · have := ih (i + 1) (q - l.qty) s hs; simp; omega

theorem fifoPlan_nodup (ls : List Lot) (i q : Nat) : ((fifoPlan ls i q).map Prod.fst).Nodup := by
  induction ls generalizing i q with
  | nil => simp [fifoPlan]
  | cons l ls ih =>
    simp only [fifoPlan]
    split
    · simp
    · split
      · simp
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, ih _ _⟩
        simp at hm
        obtain ⟨b, hb⟩ := hm
        have := fifoPlan_idx ls (i + 1) (q - l.qty) (i, b) hb
        omega

theorem fifoPlan_within (ls : List Lot) (i q : Nat) :
    ∀ s ∈ fifoPlan ls i q, ∃ l, ls[s.1 - i]? = some l ∧ s.2 ≤ l.qty := by
  induction ls generalizing i q with
  | nil => simp [fifoPlan]
  | cons l ls ih =>
    intro s hs
    simp only [fifoPlan] at hs
    split at hs
    · simp at hs
    · split at hs
      · next h1 h2 => simp at hs; subst hs; exact ⟨l, by simp, h2⟩
      · next h1 h2 =>
        simp at hs
        rcases hs with rfl | hs
        · exact ⟨l, by simp, Nat.le_refl _⟩
        · obtain ⟨l', hl', hq⟩ := ih (i + 1) (q - l.qty) s hs
          have hi := (fifoPlan_idx ls (i + 1) (q - l.qty) s hs).1
          refine ⟨l', ?_, hq⟩
          have : s.1 - i = (s.1 - (i + 1)) + 1 := by omega
          rw [this]; simpa using hl'

/-- **#10** Every plan sells only lots that exist, never sells a lot twice, never more than it holds. -/
theorem fifoPlan_valid (ls : List Lot) (q : Nat) : Valid ls (fifoPlan ls 0 q) := by
  refine ⟨fifoPlan_nodup ls 0 q, fun s hs => ?_⟩
  simpa using fifoPlan_within ls 0 q s hs

def planQty (p : Plan) : Nat := (p.map Prod.snd).sum

/-- **#10** When the coins are there, the plan sells exactly the coins needed. -/
theorem fifoPlan_hits (ls : List Lot) (i q : Nat) (h : q ≤ totalQty ls) : planQty (fifoPlan ls i q) = q := by
  induction ls generalizing i q with
  | nil => simp [totalQty] at h; simp [fifoPlan, planQty, h]
  | cons l ls ih =>
    simp only [fifoPlan]
    split
    · next h0 => simp [planQty, h0]
    · split
      · simp [planQty]
      · next h0 h1 =>
        have := ih (i + 1) (q - l.qty) (by simp [totalQty] at h; omega)
        simp [planQty] at *; omega

/-- **#10** Cash target: selling at `price` per coin raises at least `target` when the coins are worth it. -/
theorem fifoPlan_cash (ls : List Lot) (price target : Nat) (hp : 0 < price)
    (h : (target + price - 1) / price ≤ totalQty ls) :
    target ≤ price * planQty (fifoPlan ls 0 ((target + price - 1) / price)) := by
  rw [fifoPlan_hits ls 0 _ h]
  have := Nat.div_add_mod (target + price - 1) price
  have := Nat.mod_lt (target + price - 1) hp
  have : price * ((target + price - 1) / price) = target + price - 1 - (target + price - 1) % price := by omega
  omega

/-- **#11** The planner picks the cheapest candidate. -/
def cheapest (tax : Plan → Nat) : Plan → List Plan → Plan
  | best, [] => best
  | best, c :: cs => cheapest tax (if tax c < tax best then c else best) cs

theorem cheapest_le_start (tax : Plan → Nat) (best : Plan) (cs : List Plan) : tax (cheapest tax best cs) ≤ tax best := by
  induction cs generalizing best with
  | nil => simp [cheapest]
  | cons c cs ih =>
    simp only [cheapest]
    have := ih (if tax c < tax best then c else best)
    by_cases hc : tax c < tax best
    · simp [hc] at this ⊢; omega
    · simp [hc] at this ⊢; omega

/-- **#11** Starting from the country's default plan, the chosen plan's tax is never higher than the default's. -/
theorem chosen_le_default (tax : Plan → Nat) (default : Plan) (others : List Plan) :
    tax (cheapest tax default others) ≤ tax default := cheapest_le_start tax default others

end Kanon.CashOut
