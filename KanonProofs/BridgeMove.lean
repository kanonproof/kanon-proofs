import KanonProofs.Lots

/-!
# A coin that crosses a chain's own bridge under another name (#34)

A token can have one name on a chain and another on Ethereum (bridged USDC on zkSync is "USDC.e"; on Ethereum it is
USDC). When it crosses that chain's official bridge it is the same property arriving in the user's own wallet, so the
ledger moves its lots to the new wallet and the new name and touches nothing else: no sale, no new purchase.

Model of the `toAsset` field of the ledger's transfer event (`src/lib/engine/lots.ts`).
-/

namespace Kanon.Lots

/-- A lot as the ledger files it: where it is held, and under which coin's name. -/
structure Named where
  held : Held
  asset : Nat
  deriving Repr, DecidableEq

/-- A move through an official bridge: every lot goes to the destination wallet and takes the destination name. -/
def moveAs (to asset : Nat) (hs : List Named) : List Named :=
  hs.map fun h => { held := { h.held with wallet := to }, asset := asset }

/-- **#34** Crossing a bridge under another name is never a sale: every lot keeps its date, quantity and cost. -/
theorem moveAs_keeps_lots (to asset : Nat) (hs : List Named) :
    (moveAs to asset hs).map (fun h => h.held.lot) = hs.map (fun h => h.held.lot) := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [moveAs] at *

/-- **#34** Nothing is created or lost on the way: the same coins, for the same cost. -/
theorem moveAs_conserves (to asset : Nat) (hs : List Named) :
    totalQty ((moveAs to asset hs).map (fun h => h.held.lot)) = totalQty (hs.map (fun h => h.held.lot)) ∧
    totalCost ((moveAs to asset hs).map (fun h => h.held.lot)) = totalCost (hs.map (fun h => h.held.lot)) := by
  rw [moveAs_keeps_lots]; exact ⟨rfl, rfl⟩

/-- **#34** After the move every lot is in the destination wallet, under the destination name. -/
theorem moveAs_dest (to asset : Nat) (hs : List Named) : ∀ h ∈ moveAs to asset hs, h.held.wallet = to ∧ h.asset = asset := by
  intro h hm; simp [moveAs] at hm; obtain ⟨x, _, rfl⟩ := hm; exact ⟨rfl, rfl⟩

/-- **#34** Moved under the same name, it is exactly the own-wallet move of #4. -/
theorem moveAs_is_move (to asset : Nat) (hs : List Named) :
    (moveAs to asset hs).map (fun h => h.held) = move to (hs.map (fun h => h.held)) := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [moveAs, move] at *

end Kanon.Lots
