import Mathlib.Tactic

/-!
# The person's answers ("Needs you") (#40)

KANON asks about each transfer it couldn't explain (`src/lib/money-map/map.ts`, `buildMap` and `toEvents`). Coins in:
"I paid for it" (what and when), "Came back from an account of mine", "Income or reward". Coins out: "Still mine: an
account I haven't added" or "Sold or spent". Proved here:

* **An answer is used only where it fits.** An answer about coins in is never applied to coins out, nor the other way.
  "Paid for it" is used only with a day on or before the coins arrived; "Sold" only for a coin with a price (what it
  sold for must be known).
* **Coins that left with no answer are not a sale.** They leave the wallet but are not reported (only sales, `s`, are);
  "Sold or spent" makes them a sale.
* **"Paid for it" keeps the day it was bought.** The lot is dated to the day the person gives, which is never after the
  coins arrived; it costs what they paid.
* **Coins sent to an account of the person's come back with their date and cost, and never more than went there.**
  Over any run of coins sent away ("still mine") and coins coming back, what comes back from that account is never
  more than was sent there and is still there; anything more arrives like any coin from outside. The coins still away
  are never below 0, and they are exactly those sent less those come back.
-/

namespace Kanon.Answers

inductive Answer
  | paid (day : ℕ)
  | income
  | back
  | mine
  | sold

/-- Whether an answer is used for a transfer: coins in (`incoming`), arriving on `arrival`, with or without a price. -/
def used (incoming : Bool) (arrival : ℕ) (priced : Bool) : Answer → Bool
  | .paid d => incoming && decide (d ≤ arrival)
  | .income => incoming
  | .back => incoming
  | .mine => !incoming
  | .sold => !incoming && priced

/-- **#40** An answer about coins in is never used for coins out, and one about coins out never for coins in. -/
theorem fits_direction (arrival : ℕ) (priced : Bool) :
    (∀ d, used false arrival priced (.paid d) = false) ∧ used false arrival priced .income = false ∧
      used false arrival priced .back = false ∧ used true arrival priced .mine = false ∧
      used true arrival priced .sold = false := by
  simp [used]

/-- **#40** "Paid for it" is used only with a day on or before the coins arrived. -/
theorem paid_not_after (d arrival : ℕ) (priced : Bool) (h : used true arrival priced (.paid d) = true) : d ≤ arrival := by
  simpa [used] using h

/-- **#40** "Sold or spent" is used only for a coin with a price. -/
theorem sold_needs_price (arrival : ℕ) (incoming : Bool) (h : used incoming arrival false .sold = true) : False := by
  simp [used] at h

/-- What the ledger does with coins out: `sale` (`s`, reported) or `left` (`x`, out of the wallet, not reported), or
`away` (moved to the person's account elsewhere, keeping date and cost). -/
inductive Out | sale | left | away
  deriving DecidableEq

def outEvent (a : Option Answer) : Out :=
  match a with
  | some .mine => .away
  | some .sold => .sale
  | _ => .left

/-- **#40** Coins out with no answer are never reported as a sale; only "Sold or spent" makes them one. -/
theorem unanswered_not_sale : outEvent none = .left := rfl

theorem sale_only_if_sold (a : Option Answer) (h : outEvent a = .sale) : a = some .sold := by
  match a, h with
  | some .sold, _ => rfl

/-- The lot's day for holding periods (`runLedger`: the day bought if before the day the coins arrived). -/
def lotDay (arrival : ℕ) (bought : Option ℕ) : ℕ :=
  match bought with
  | some d => if d < arrival then d else arrival
  | none => arrival

/-- **#40** A lot is never dated after the coins arrived, and with "paid for it" (used) it is dated to the day given. -/
theorem lot_day (arrival d : ℕ) (priced : Bool) (h : used true arrival priced (.paid d) = true) :
    lotDay arrival (some d) = d ∧ lotDay arrival (some d) ≤ arrival := by
  have := paid_not_after d arrival priced h
  simp only [lotDay]; split_ifs with hlt
  · exact ⟨rfl, this⟩
  · have : d = arrival := by omega
    exact ⟨this.symm, le_rfl⟩

/-- What coins that came in cost: what the person said they paid, else their value that day. -/
def lotCost (paid : Option ℚ) (value : ℚ) : ℚ := paid.getD value

/-- **#40** With "paid for it", the lot costs what the person paid; with no answer, its value the day it arrived. -/
theorem lot_cost (c v : ℚ) : lotCost (some c) v = c ∧ lotCost none v = v := ⟨rfl, rfl⟩

theorem lot_day_le (arrival : ℕ) (b : Option ℕ) : lotDay arrival b ≤ arrival := by
  unfold lotDay; split <;> [split_ifs <;> omega; exact le_rfl]

/-! ### Coins sent away and coming back -/

/-- Coins of one kind sent to the person's account elsewhere (`mine a`) or coming back from it (`back a`). -/
inductive Move | mine (a : ℚ) | back (a : ℚ)

/-- One move: what is away, what came back from there (with its date and cost), what arrived as new. A move back
returns `min a away` from there and the rest arrives as from outside. -/
def step (s : ℚ × ℚ × ℚ) : Move → ℚ × ℚ × ℚ
  | .mine a => (s.1 + a, s.2.1, s.2.2)
  | .back a => (s.1 - min a s.1, s.2.1 + min a s.1, s.2.2 + (a - min a s.1))

def sent : List Move → ℚ
  | [] => 0
  | .mine a :: ms => a + sent ms
  | .back _ :: ms => sent ms

def cameBack : List Move → ℚ
  | [] => 0
  | .mine _ :: ms => cameBack ms
  | .back a :: ms => a + cameBack ms

def Pos : List Move → Prop
  | [] => True
  | .mine a :: ms => 0 ≤ a ∧ Pos ms
  | .back a :: ms => 0 ≤ a ∧ Pos ms

/-- The fold, generalised over its start. -/
lemma fold_facts (ms : List Move) (hp : Pos ms) (s : ℚ × ℚ × ℚ) (h0 : 0 ≤ s.1) :
    let r := ms.foldl step s
    0 ≤ r.1 ∧ r.1 + r.2.1 = s.1 + s.2.1 + sent ms ∧ r.2.1 + r.2.2 = s.2.1 + s.2.2 + cameBack ms := by
  induction ms generalizing s with
  | nil => simp [sent, cameBack, h0]
  | cons m ms ih =>
    cases m with
    | mine a =>
      obtain ⟨ha, hp'⟩ := hp
      have := ih hp' (step s (.mine a)) (by simp [step]; linarith)
      simp only [List.foldl_cons, sent, cameBack, step] at this ⊢
      refine ⟨this.1, by linarith [this.2.1], by linarith [this.2.2]⟩
    | back a =>
      obtain ⟨ha, hp'⟩ := hp
      have hm : 0 ≤ s.1 - min a s.1 := by have := min_le_right a s.1; linarith
      have := ih hp' (step s (.back a)) (by simp [step])
      simp only [List.foldl_cons, sent, cameBack, step] at this ⊢
      refine ⟨this.1, by linarith [this.2.1], by linarith [this.2.2]⟩

/-- **#40** Over any run of coins sent away and coming back: what is still away is never below 0; what is away plus
what came back from there is exactly what was sent there (so what comes back never exceeds what was sent); and what
came back from there plus what arrived as new is exactly all that came back. -/
theorem away_and_back (ms : List Move) (hp : Pos ms) :
    let r := ms.foldl step (0, 0, 0)
    0 ≤ r.1 ∧ r.1 + r.2.1 = sent ms ∧ r.2.1 ≤ sent ms ∧ r.2.1 + r.2.2 = cameBack ms := by
  have := fold_facts ms hp (0, 0, 0) le_rfl
  simp only [add_zero, zero_add] at this
  exact ⟨this.1, this.2.1, by linarith [this.1, this.2.1], this.2.2⟩

end Kanon.Answers
