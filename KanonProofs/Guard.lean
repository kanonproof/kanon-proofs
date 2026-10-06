/-!
# The agent's checker (#17)

The agent only explains; KANON's engines do every number. Before an answer is shown it goes through a
checker: every number in it must be a small count or year, or close to a number the engines produced,
and it must use none of the banned words (advice, promises, jargon). The agent gets at most a few tries;
if none passes, a fixed "I can't answer that from your numbers yet" is shown instead.

We prove that whatever is shown always passes the checker. Money is in cents, so "close" is exact:
within 50 cents, or within half a percent of the engine's number.
-/

namespace Kanon.Guard

structure Answer where
  numbers : List Nat
  words : List Nat   -- word ids; the banned list is a list of ids

/-- Small counts (0–31) and years carry no claim. Counts are whole numbers, scaled to cents. -/
def free (n : Nat) : Bool := n ≤ 3100 || (199000 ≤ n && n ≤ 210000)

def dist (a b : Nat) : Nat := (a - b) + (b - a)

/-- Within 50 cents, or half a percent of the engine's number. -/
def close (n a : Nat) : Bool := dist n a ≤ max 50 (a / 200)

def sourced (data : List Nat) (n : Nat) : Bool := free n || data.any (close n)

def check (banned data : List Nat) (a : Answer) : Bool :=
  a.numbers.all (sourced data) && a.words.all (fun w => !banned.contains w)

/-- The fixed reply when nothing passes: no numbers, and its words are never on the banned list. -/
def fallback (safeWords : List Nat) : Answer := ⟨[], safeWords⟩

/-- Show the first try that passes, else the fallback. -/
def respond (banned data safeWords : List Nat) : List Answer → Answer
  | [] => fallback safeWords
  | a :: rest => if check banned data a then a else respond banned data safeWords rest

/-- **#17** The fallback passes whenever its words aren't banned. -/
theorem fallback_ok (banned data safeWords : List Nat) (h : safeWords.all (fun w => !banned.contains w) = true) :
    check banned data (fallback safeWords) = true := by
  simp [check, fallback] at *; exact h

/-- **#17** Whatever the agent shows passes the checker, for any number of tries. -/
theorem shown_passes (banned data safeWords : List Nat) (h : safeWords.all (fun w => !banned.contains w) = true) :
    ∀ tries : List Answer, check banned data (respond banned data safeWords tries) = true := by
  intro tries
  induction tries with
  | nil => exact fallback_ok banned data safeWords h
  | cons a rest ih =>
    unfold respond
    by_cases hc : check banned data a = true
    · simp [hc]
    · simp [hc]; exact ih

/-- **#17** So every number shown is a small count or year, or close to a number from the engines. -/
theorem shown_numbers_sourced (banned data safeWords : List Nat) (h : safeWords.all (fun w => !banned.contains w) = true)
    (tries : List Answer) : ∀ n ∈ (respond banned data safeWords tries).numbers,
      free n = true ∨ ∃ d ∈ data, close n d = true := by
  intro n hn
  have := shown_passes banned data safeWords h tries
  simp only [check, Bool.and_eq_true, List.all_eq_true] at this
  have hs := this.1 n hn
  simp only [sourced, Bool.or_eq_true, List.any_eq_true] at hs
  exact hs

/-- **#17** And no banned word is ever shown. -/
theorem shown_no_banned (banned data safeWords : List Nat) (h : safeWords.all (fun w => !banned.contains w) = true)
    (tries : List Answer) : ∀ w ∈ (respond banned data safeWords tries).words, banned.contains w = false := by
  intro w hw
  have := shown_passes banned data safeWords h tries
  simp only [check, Bool.and_eq_true, List.all_eq_true] at this
  simpa using this.2 w hw

end Kanon.Guard
