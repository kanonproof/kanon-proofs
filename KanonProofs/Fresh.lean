/-!
# Freshness (#28)

Every hand-checked number (a rate, a fee, a tax rule) carries the day it was checked and a limit in days
for its kind (rates 14, fees 30, inflation 62, rules 120). Shown past its limit, it carries a "stale" label;
a number with no readable date is always stale; and the agent is only ever given numbers that aren't stale.
Days are counted from a fixed start, as whole numbers. The app uses this rule in `src/lib/fresh.ts`.
-/

namespace Kanon.Fresh

/-- A number as checked: its value, the day it was checked (none if the date can't be read), its limit in days. -/
structure Checked where
  value : Int
  asOf : Option Nat
  limit : Nat

def stale (today : Nat) (n : Checked) : Bool :=
  match n.asOf with
  | none => true
  | some d => decide (today - d > n.limit)

/-- What a card shows: the number and whether it carries the "stale" label. -/
structure Shown where
  value : Int
  staleLabel : Bool

def display (today : Nat) (n : Checked) : Shown := ⟨n.value, stale today n⟩

/-- What the agent is given: only numbers that aren't stale. -/
def forAgent (today : Nat) (ns : List Checked) : List Checked := ns.filter (fun n => !stale today n)

/-- **#28** A number older than its limit is never shown without the "stale" label. -/
theorem old_is_labelled (today : Nat) (n : Checked) (d : Nat) (h : n.asOf = some d) (old : today - d > n.limit) :
    (display today n).staleLabel = true := by
  simp [display, stale, h, old]

/-- **#28** A number whose date can't be read is always labelled stale. -/
theorem undated_is_labelled (today : Nat) (n : Checked) (h : n.asOf = none) : (display today n).staleLabel = true := by
  simp [display, stale, h]

/-- **#28** The label never changes the number itself. -/
theorem label_keeps_value (today : Nat) (n : Checked) : (display today n).value = n.value := rfl

/-- **#28** Everything the agent is given has a date and is within its limit. -/
theorem agent_never_gets_stale (today : Nat) (ns : List Checked) :
    ∀ n ∈ forAgent today ns, ∃ d, n.asOf = some d ∧ today - d ≤ n.limit := by
  intro n hn
  simp only [forAgent, List.mem_filter] at hn
  obtain ⟨_, hs⟩ := hn
  cases h : n.asOf with
  | none => simp [stale, h] at hs
  | some d =>
    refine ⟨d, rfl, ?_⟩
    simp [stale, h] at hs
    omega

/-- **#28** A number fresh today stays labelled stale once it's past its limit: checking later never hides age. -/
theorem stale_stays_stale (t₁ t₂ : Nat) (n : Checked) (later : t₁ ≤ t₂) (h : stale t₁ n = true) : stale t₂ n = true := by
  cases e : n.asOf with
  | none => simp [stale, e]
  | some d =>
    simp [stale, e] at h ⊢
    omega

end Kanon.Fresh
