import Mathlib.Tactic

/-!
# Alert timing: when a take-profit step's alert is sent (#16)

A step is a coin, a currency and a target price (`AlertRule`, `src/lib/watch/alerts.ts`). With alerts on, KANON keeps
the steps on its server, and about every 5 minutes a round (`runAlerts`, started by `POST /api/alerts/run`) prices
each coin once and sends a push notification for each step reached. The rule, as the app's code has it:

* **Reached** means: the step is not marked yet (`hits[id]` unset) and the round has a price in the step's own
  currency at or above the target (`due`, alerts.ts:111-113; a price in another currency is never compared,
  `api/alerts/run/route.ts`:34-35). It is a level, read when the round runs, not a crossing between rounds.
* **Sent once:** the step is marked (`hits[id] = now`) and then sent (alerts.ts:185-188). If the push service takes
  it, the step stays marked and is never sent again. A marked step is never unmarked except when its send failed;
  nothing else ever re-arms it (a step is never edited: removing it and setting it again makes a new step with a new
  id, `src/app/money/Watch.tsx`:76-79).
* **A failed send** unmarks the step, so the next round that sees the price at or above the target sends it again
  (alerts.ts:191); the rest of that address's steps wait for the next round (alerts.ts:193).
* **The address is deleted** (every step with it) when the browser has dropped it, at the 20th failed send in a row,
  after 30 days without the page syncing, or when alerts are turned off (alerts.ts:157, 189, 192; `api/alerts`
  DELETE). A step removed on the page is gone too.
* **Seen on the page:** a step the open page saw reached is sent to the server as reached and never pushed
  (`api/alerts/route.ts`:44-47).
* **A missed round** (the schedule ran late or not at all, the round ran out of time before this address, the store
  failed, there was no price) changes nothing: the step waits, and the next round that sees the price at or above the
  target sends it. Prices between rounds are never looked at, so a price that rises above the target and falls back
  between two rounds sends nothing (the app says alerts "can be missed", `src/app/terms/page.tsx`:35).
* **Cut off after marking** (the round stopped between marking and the send's answer, or couldn't write the unmark):
  the step stays marked and is never sent again, whether or not the notification went out. So a step is sent **at most
  once**, not exactly once.

The model follows one step through the rounds, in order, one round at a time. What each round did for the step is a
`Round`; everything the round did for other steps of the same address that matters to this one (a failed send before
it, the address deleted) is one of those cases. Proved below:

* **Never before the price is seen at or above the target:** a round sends the step only if the step was waiting
  and that round saw a price at or above the target.
* **The first such round sends it:** for a waiting step, the first round that sees a price at or above the target
  sends it, and no earlier round does; missed rounds and earlier failed sends don't change that.
* **Never twice:** after a send the push service took (or one that was cut off), the step is never sent again. A
  second send only ever follows a failed one, and at most one send ever reaches the push service.
* **Never re-armed:** a step once reached or removed never waits again; only a failed send leaves it waiting.
* **A missed round changes nothing.**
* **What the code does when two sends race:** the mark (alerts.ts:186) doesn't look whether the step is already
  marked, so a round that read the step before another round or the open page marked it still marks it and sends.
  The one-round-at-a-time model above relies on rounds not overlapping; see `mark_does_not_recheck`.

Not proved here: which coins get a price and in what currency (`src/lib/watch/prices.ts`), the round's time budget
and order, the 30-day and 20-failure counters themselves (in the model they are the `dropped` and `gone` cases), and
the Monday report.
-/

namespace Kanon.Alerts

/-- What came of sending a step's notification (`deps.send`, alerts.ts:188-193). -/
inductive Send
  /-- The push service took it: the step stays marked. -/
  | ok
  /-- The send failed: the step is unmarked, and the address's other steps wait for the next round. -/
  | failed
  /-- The address was deleted: the browser dropped it (404/410), or this was its 20th failed send in a row. -/
  | gone
  /-- The round stopped after marking the step (time ran out, or the unmark couldn't be written): it stays marked,
  whether or not the notification went out. -/
  | cut
  deriving DecidableEq

/-- What one round did with the step. -/
inductive Round
  /-- The round didn't look at the step: no round ran, it ran out of time before this address, the store failed, no
  price in the step's currency, or an earlier step of the same address failed to send this round. -/
  | skipped
  /-- The round had this price for the step's coin in its currency; if the step was due, sending it came to `send`. -/
  | seen (price : ℚ) (send : Send)
  /-- The open page saw the step reached and told the server (`api/alerts/route.ts`:44-47): marked, never pushed. -/
  | pageSaw
  /-- The step or its address was deleted: removed on the page, alerts turned off, 30 days without a sync, or the
  address deleted while sending another of its steps. -/
  | dropped

/-- A step: waiting (`hits[id]` unset), reached (marked), or removed from the server. -/
inductive State
  | armed
  | reached
  | removed
  deriving DecidableEq

/-- Whether the round marks and sends the step (`due`, alerts.ts:111-113): it is waiting and the round's price is at or
above the target. -/
def firesIn (target : ℚ) : State → Round → Prop
  | .armed, .seen p _ => target ≤ p
  | _, _ => False

/-- The step after its send (alerts.ts:186-193). -/
def afterSend : Send → State
  | .ok => .reached
  | .cut => .reached
  | .failed => .armed
  | .gone => .removed

/-- The step after one round. -/
def step (target : ℚ) : State → Round → State
  | .armed, .seen p o => if target ≤ p then afterSend o else .armed
  | .armed, .pageSaw => .reached
  | _, .dropped => .removed
  | s, _ => s

/-- The step before round `n`, from `s0` before round 0, the rounds in order. -/
def state (target : ℚ) (s0 : State) (rs : ℕ → Round) : ℕ → State
  | 0 => s0
  | n + 1 => step target (state target s0 rs n) (rs n)

/-- Round `n` marks and sends the step. -/
def fires (target : ℚ) (s0 : State) (rs : ℕ → Round) (n : ℕ) : Prop :=
  firesIn target (state target s0 rs n) (rs n)

/-- Round `n` sent the step and the push service took it, or the round was cut off after marking it (it may have gone
out). -/
def notified (target : ℚ) (s0 : State) (rs : ℕ → Round) (n : ℕ) : Prop :=
  fires target s0 rs n ∧ ∃ p o, rs n = .seen p o ∧ (o = .ok ∨ o = .cut)

lemma fires_iff (target : ℚ) (s0 : State) (rs : ℕ → Round) (n : ℕ) :
    fires target s0 rs n ↔ state target s0 rs n = .armed ∧ ∃ p o, rs n = .seen p o ∧ target ≤ p := by
  unfold fires
  cases h : state target s0 rs n <;> cases hr : rs n <;> simp [firesIn]

lemma not_armed_step (target : ℚ) (s : State) (r : Round) (h : s ≠ .armed) : step target s r ≠ .armed := by
  cases s <;> cases r <;> simp_all [step]

/-- **#16** Never re-armed: a step once reached or removed never waits again. -/
theorem never_rearmed (target : ℚ) (s0 : State) (rs : ℕ → Round) (n k : ℕ)
    (h : state target s0 rs n ≠ .armed) : state target s0 rs (n + k) ≠ .armed := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [← Nat.add_assoc]
    exact not_armed_step target _ _ ih

/-- **#16** Never before the price is seen at or above the target: a round sends the step only if the step was
waiting and that round saw a price at or above the target. -/
theorem fires_only_at_or_above (target : ℚ) (s0 : State) (rs : ℕ → Round) (n : ℕ)
    (h : fires target s0 rs n) :
    state target s0 rs n = .armed ∧ ∃ p o, rs n = .seen p o ∧ target ≤ p :=
  (fires_iff target s0 rs n).1 h

lemma stays_armed (target : ℚ) (rs : ℕ → Round) (n : ℕ)
    (hbefore : ∀ k < n, rs k = .skipped ∨ ∃ q o, rs k = .seen q o ∧ (q < target ∨ o = .failed)) :
    state target .armed rs n = .armed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
    show step target (state target .armed rs n) (rs n) = .armed
    rw [ih]
    rcases hbefore n (Nat.lt_succ_self n) with h | ⟨q, o, h, hq⟩
    · rw [h]; rfl
    · rw [h]
      rcases hq with hq | ho
      · simp [step, not_le.mpr hq]
      · subst ho; by_cases hp : target ≤ q <;> simp [step, hp, afterSend]

/-- **#16** The first round that sees the price at or above the target sends it: for a waiting step, if every round
before `n` missed it or saw a price below the target, and round `n` sees a price at or above the target, round `n`
sends the step and no earlier round did. -/
theorem first_round_at_or_above (target : ℚ) (rs : ℕ → Round) (n : ℕ) (p : ℚ) (o : Send)
    (hbefore : ∀ k < n, rs k = .skipped ∨ ∃ q o', rs k = .seen q o' ∧ q < target)
    (hn : rs n = .seen p o) (hp : target ≤ p) :
    fires target .armed rs n ∧ ∀ k < n, ¬ fires target .armed rs k := by
  have hb : ∀ k < n, rs k = .skipped ∨ ∃ q o', rs k = .seen q o' ∧ (q < target ∨ o' = .failed) := by
    intro k hk
    rcases hbefore k hk with h | ⟨q, o', h, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, o', h, Or.inl hq⟩
  refine ⟨(fires_iff _ _ _ _).2 ⟨stays_armed target rs n hb, p, o, hn, hp⟩, ?_⟩
  intro k hk hf
  obtain ⟨_, q, o', hq, hle⟩ := fires_only_at_or_above _ _ _ _ hf
  rcases hbefore k hk with h | ⟨q', o'', h, hlt⟩
  · rw [h] at hq; cases hq
  · rw [h] at hq; cases hq; linarith

/-- **#16** Missed rounds and failed sends don't stop it: for a waiting step, if every round before `n` missed it, saw
a price below the target, or failed to send it, and round `n` sees a price at or above the target, round `n` sends
it. -/
theorem sent_after_misses_and_failures (target : ℚ) (rs : ℕ → Round) (n : ℕ) (p : ℚ) (o : Send)
    (hbefore : ∀ k < n, rs k = .skipped ∨ ∃ q o', rs k = .seen q o' ∧ (q < target ∨ o' = .failed))
    (hn : rs n = .seen p o) (hp : target ≤ p) :
    fires target .armed rs n :=
  (fires_iff _ _ _ _).2 ⟨stays_armed target rs n hbefore, p, o, hn, hp⟩

/-- **#16** A missed round changes nothing. -/
theorem missed_round_changes_nothing (target : ℚ) (s0 : State) (rs : ℕ → Round) (n : ℕ)
    (h : rs n = .skipped) : state target s0 rs (n + 1) = state target s0 rs n := by
  show step target (state target s0 rs n) (rs n) = state target s0 rs n
  rw [h]; cases state target s0 rs n <;> rfl

/-- **#16** A failed send leaves the step waiting (it is tried again by the next round that sees the price at or above
the target). -/
theorem failed_send_rearms (target : ℚ) (s0 : State) (rs : ℕ → Round) (n : ℕ) (p : ℚ)
    (hf : fires target s0 rs n) (hn : rs n = .seen p .failed) : state target s0 rs (n + 1) = .armed := by
  obtain ⟨ha, -⟩ := fires_only_at_or_above _ _ _ _ hf
  obtain ⟨-, q, o, hq, hle⟩ := fires_only_at_or_above _ _ _ _ hf
  rw [hn] at hq; cases hq
  show step target (state target s0 rs n) (rs n) = .armed
  rw [ha, hn]; simp [step, hle, afterSend]

/-- **#16** Sent again only after a failed send: if rounds `n < m` both send the step, the send in round `n` failed. -/
theorem again_only_after_failure (target : ℚ) (s0 : State) (rs : ℕ → Round) (n m : ℕ) (hnm : n < m)
    (hn : fires target s0 rs n) (hm : fires target s0 rs m) : ∃ p, rs n = .seen p .failed := by
  obtain ⟨ha, p, o, hr, hle⟩ := fires_only_at_or_above _ _ _ _ hn
  refine ⟨p, ?_⟩
  rw [hr]
  cases o with
  | failed => rfl
  | _ =>
    exfalso
    have h1 : state target s0 rs (n + 1) ≠ .armed := by
      show step target (state target s0 rs n) (rs n) ≠ .armed
      rw [ha, hr]; simp [step, hle, afterSend]
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    exact never_rearmed target s0 rs (n + 1) k h1 (fires_only_at_or_above _ _ _ _ hm).1

/-- **#16** Never twice: after a send the push service took, or one cut off after marking, no later round sends the
step. -/
theorem never_after_notified (target : ℚ) (s0 : State) (rs : ℕ → Round) (n m : ℕ) (hnm : n < m)
    (hn : notified target s0 rs n) : ¬ fires target s0 rs m := by
  intro hm
  obtain ⟨hf, p, o, hr, ho⟩ := hn
  obtain ⟨q, hq⟩ := again_only_after_failure target s0 rs n m hnm hf hm
  rw [hr] at hq; cases hq
  rcases ho with h | h <;> cases h

/-- **#16** At most one send of a step ever reaches the push service (counting a send cut off after marking as one
that may have). -/
theorem notified_at_most_once (target : ℚ) (s0 : State) (rs : ℕ → Round) (n m : ℕ)
    (hn : notified target s0 rs n) (hm : notified target s0 rs m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd hm.1 (never_after_notified target s0 rs n m h hn)
  · exact h
  · exact absurd hn.1 (never_after_notified target s0 rs m n h hm)

/-- The round's mark (alerts.ts:186): on the file as read again, the step's hit is set to `now` if the step is still
listed; otherwise the hit is left as it was. -/
def markEdit (listed : Bool) (hitBefore : Option ℕ) (now : ℕ) : Option ℕ :=
  if listed then some now else hitBefore

/-- The round sends when the step is marked in the file the mark wrote (alerts.ts:187-188). -/
def sendsAfterMark (listed : Bool) (hitBefore : Option ℕ) (now : ℕ) : Bool :=
  (markEdit listed hitBefore now).isSome

/-- **#16, what the code does when two sends race:** the mark doesn't look at an earlier mark. A round that found the
step due in the file it read first, and finds it still listed when it marks, sends it even if another round or the
open page marked it in between (`hitBefore = some t`). Rounds that overlap can send a step twice. -/
theorem mark_does_not_recheck (t now : ℕ) : sendsAfterMark true (some t) now = true := by
  simp [sendsAfterMark, markEdit]

end Kanon.Alerts
