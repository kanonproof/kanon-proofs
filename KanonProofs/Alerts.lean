import Mathlib.Tactic

/-!
# Alert timing: when a take-profit step's alert is sent (#16)

Take-profit alerts with KANON closed (KANON `src/lib/watch/alerts.ts`, branch claude/alert-once-2, e3c3d30):
about every 5 minutes a round reads each saved address, prices the coins and, for each step reached, marks it in the
address file (alerts.ts:328-334), claims the step's record (`claimSent`, 183-196: one write only one round can win),
tries to send, then writes "sent" to the record (346-350); a failed or thrown send unmarks the step and deletes the
record (355-358). A mark or "sending" record left by a round that ended early is taken over after `TAKEOVER_MS`
(10 minutes, line 134).

1. `atLeast_iff`: the price comparison is exact for plain decimals (`target ≤ price` as rationals).
2. Rounds at the same time, every interleaving (`sent_at_most_once`, `no_try_after_sent`,
   `resent_after_lost_write`): with every round's work inside 60 seconds of its start (a hypothesis), a second try
   only ever follows a send whose "sent" write never happened, and more than 10 minutes after the first round
   started; after a "sent" write nobody tries again. The exception is real (the code says so, lines 314-316).
3. Rounds one after another, every store write able to fail (`tries_only_at_or_above`, `sent_eventually`,
   `no_try_after_sent_record`, `no_resend_after_rearm`, `resent_after_crash`).

Not covered: a price written with an exponent (compared with `Number`), the record being deleted (the step removed,
alerts turned off, the sweep after 355 days: then a step can be sent again), one clock for every round, round codes
that never repeat (random UUIDs), the Monday report.
-/

namespace Kanon.Alerts

/-! ## 1. Prices compared as exact decimals (`atLeast`, alerts.ts:119-128) -/

/-- The value of a string of digits, most significant first. -/
def num (l : List ℕ) : ℕ := l.foldl (fun a d => 10 * a + d) 0

lemma foldl_num (a : ℕ) (l : List ℕ) :
    l.foldl (fun a d => 10 * a + d) a = a * 10 ^ l.length + l.foldl (fun a d => 10 * a + d) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons d l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (10 * a + d), ih (10 * 0 + d)]
    ring

lemma num_cons (d : ℕ) (l : List ℕ) : num (d :: l) = d * 10 ^ l.length + num l := by
  simp only [num, List.foldl_cons]
  rw [foldl_num (10 * 0 + d)]
  ring

lemma num_lt (l : List ℕ) (h : ∀ d ∈ l, d < 10) : num l < 10 ^ l.length := by
  induction l with
  | nil => simp [num]
  | cons d l ih =>
    have hd : d < 10 := h d (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    rw [num_cons, List.length_cons, pow_succ]
    calc d * 10 ^ l.length + num l < d * 10 ^ l.length + 10 ^ l.length := by omega
      _ = (d + 1) * 10 ^ l.length := by ring
      _ ≤ 10 * 10 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ l.length * 10 := by ring

lemma num_replicate_zero (k : ℕ) : num (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, num_cons, ih]; simp

lemma num_append_zeros (l : List ℕ) (k : ℕ) : num (l ++ List.replicate k 0) = num l * 10 ^ k := by
  have h := foldl_num (num l) (List.replicate k 0)
  have h0 := num_replicate_zero k
  simp only [num, List.foldl_append, List.length_replicate] at h h0 ⊢
  rw [h, h0]
  simp

/-- A leading digit larger than the other's decides, whatever follows (both tails shorter than `P` in value). -/
lemma lead_lt {x y a b P : ℕ} (h : x < y) (ha : a < P) : x * P + a < y * P + b := by
  calc x * P + a < x * P + P := by omega
    _ = (x + 1) * P := by ring
    _ ≤ y * P := Nat.mul_le_mul_right _ h
    _ ≤ y * P + b := by omega

/-- JavaScript's `<` on two strings of digits (each digit's character code is in digit order): the first place they
differ decides, and a string that is the start of the other is smaller. -/
def jsLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => decide (a < b) || (decide (a = b) && jsLt l m)

lemma jsLt_iff : ∀ (a b : List ℕ), a.length = b.length → (∀ d ∈ a, d < 10) → (∀ d ∈ b, d < 10) →
    (jsLt a b = true ↔ num a < num b)
  | [], [], _, _, _ => by simp [jsLt, num]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | x :: a, y :: b, hl, ha, hb => by
    have hl' : a.length = b.length := by simpa using hl
    have ih := jsLt_iff a b hl' (fun d h => ha d (by simp [h])) (fun d h => hb d (by simp [h]))
    have na := num_lt a (fun d h => ha d (by simp [h]))
    have nb := num_lt b (fun d h => hb d (by simp [h]))
    rw [num_cons, num_cons, ← hl']
    rw [← hl'] at nb
    simp only [jsLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, ih]
    constructor
    · rintro (h | ⟨rfl, h⟩)
      · exact lead_lt h na
      · omega
    · intro h
      rcases lt_trichotomy x y with h1 | rfl | h1
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, by omega⟩
      · exact absurd h (not_lt.2 (le_of_lt (lead_lt h1 nb)))

lemma num_inj : ∀ (a b : List ℕ), a.length = b.length → (∀ d ∈ a, d < 10) → (∀ d ∈ b, d < 10) →
    num a = num b → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | x :: a, y :: b, hl, ha, hb, h => by
    have hl' : a.length = b.length := by simpa using hl
    have na := num_lt a (fun d h => ha d (by simp [h]))
    have nb := num_lt b (fun d h => hb d (by simp [h]))
    rw [num_cons, num_cons, ← hl'] at h
    rw [← hl'] at nb
    rcases lt_trichotomy x y with h1 | rfl | h1
    · exact absurd h (ne_of_lt (lead_lt h1 na))
    · have : num a = num b := by omega
      rw [num_inj a b hl' (fun d h => ha d (by simp [h])) (fun d h => hb d (by simp [h])) this]
    · exact absurd h (ne_of_gt (lead_lt h1 nb))

/-- `x.replace(/^0+(?=\d)/, "")`: the leading zeros go, but never the last digit. -/
def strip : List ℕ → List ℕ
  | [] => []
  | [d] => [d]
  | 0 :: d :: l => strip (d :: l)
  | (n + 1) :: d :: l => (n + 1) :: d :: l

lemma num_strip : ∀ l : List ℕ, num (strip l) = num l
  | [] => rfl
  | [_] => rfl
  | 0 :: d :: l => by rw [strip, num_strip (d :: l), num_cons 0 (d :: l)]; simp
  | (_ + 1) :: _ :: _ => rfl

lemma mem_strip : ∀ l : List ℕ, ∀ x ∈ strip l, x ∈ l
  | [] => by simp [strip]
  | [_] => by simp [strip]
  | 0 :: d :: l => fun x hx => by rw [strip] at hx; exact List.mem_cons_of_mem _ (mem_strip (d :: l) x hx)
  | (_ + 1) :: _ :: _ => fun x hx => by simpa [strip] using hx

lemma strip_ne_nil : ∀ l : List ℕ, l ≠ [] → strip l ≠ []
  | [] => fun h => h
  | [_] => by simp [strip]
  | 0 :: d :: l => fun _ => by rw [strip]; exact strip_ne_nil (d :: l) (by simp)
  | (_ + 1) :: _ :: _ => by simp [strip]

lemma strip_lead : ∀ l : List ℕ, 2 ≤ (strip l).length → ∃ n t, strip l = (n + 1) :: t
  | [] => by simp [strip]
  | [_] => by simp [strip]
  | 0 :: d :: l => by rw [strip]; exact strip_lead (d :: l)
  | (n + 1) :: d :: l => fun _ => ⟨n, d :: l, rfl⟩

/-- Of two stripped whole parts, the longer is the larger number. -/
lemma lt_of_strip_length (a b : List ℕ) (hb : ∀ d ∈ b, d < 10) (hb0 : b ≠ [])
    (h : (strip b).length < (strip a).length) : num b < num a := by
  have h1 : 1 ≤ (strip b).length := by
    have := strip_ne_nil b hb0
    cases hs : strip b with
    | nil => exact absurd hs this
    | cons _ _ => simp
  obtain ⟨n, t, ht⟩ := strip_lead a (by omega)
  have hbl := num_lt (strip b) (fun d hd => hb d (mem_strip b d hd))
  rw [← num_strip a, ← num_strip b, ht, num_cons]
  rw [ht] at h
  simp only [List.length_cons] at h
  calc num (strip b) < 10 ^ (strip b).length := hbl
    _ ≤ 10 ^ t.length := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ (n + 1) * 10 ^ t.length := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ (n + 1) * 10 ^ t.length + num t := by omega

/-- A plain decimal (`/^\d+(\.\d+)?$/`, alerts.ts:120): its whole digits, and its fraction digits (none when it has no
point), most significant first. -/
structure Dec where
  whole : List ℕ
  frac : List ℕ

/-- Written as a plain decimal: at least one whole digit, every digit 0-9. -/
def Dec.Plain (x : Dec) : Prop := x.whole ≠ [] ∧ (∀ d ∈ x.whole, d < 10) ∧ (∀ d ∈ x.frac, d < 10)

/-- The number a plain decimal stands for, exactly. -/
def Dec.val (x : Dec) : ℚ := (num x.whole : ℚ) + (num x.frac : ℚ) / 10 ^ x.frac.length

/-- `padEnd(n, "0")`. -/
def pad (l : List ℕ) (n : ℕ) : List ℕ := l ++ List.replicate (n - l.length) 0

/-- `atLeast(price, target)` for two plain decimals (alerts.ts:121-128): leading zeros of the whole parts go; the
longer whole part wins; whole parts of the same length are compared as strings; equal whole parts, then the fraction
parts padded with zeros to the same length, compared as strings. -/
def atLeast (p t : Dec) : Bool :=
  if (strip p.whole).length ≠ (strip t.whole).length then decide ((strip t.whole).length < (strip p.whole).length)
  else if strip p.whole ≠ strip t.whole then jsLt (strip t.whole) (strip p.whole)
  else !jsLt (pad p.frac (max p.frac.length t.frac.length)) (pad t.frac (max p.frac.length t.frac.length))

lemma frac_bounds (f : List ℕ) (h : ∀ d ∈ f, d < 10) :
    0 ≤ (num f : ℚ) / 10 ^ f.length ∧ (num f : ℚ) / 10 ^ f.length < 1 := by
  have h1 := num_lt f h
  have hp : (0 : ℚ) < 10 ^ f.length := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hp]
  exact_mod_cast h1

lemma frac_pad (f : List ℕ) (n : ℕ) (hn : f.length ≤ n) :
    (num f : ℚ) / 10 ^ f.length = (num (pad f n) : ℚ) / 10 ^ n := by
  rw [pad, num_append_zeros]
  have hn' : n = f.length + (n - f.length) := by omega
  conv_rhs => rw [hn', pow_add]
  push_cast
  have : (0 : ℚ) < 10 ^ (n - f.length) := by positivity
  field_simp
  rw [Nat.add_sub_cancel_left]

lemma pad_length (f : List ℕ) (n : ℕ) (hn : f.length ≤ n) : (pad f n).length = n := by
  simp [pad]; omega

lemma pad_digits (f : List ℕ) (n : ℕ) (h : ∀ d ∈ f, d < 10) : ∀ d ∈ pad f n, d < 10 := by
  intro d hd
  simp only [pad, List.mem_append, List.mem_replicate] at hd
  rcases hd with hd | ⟨_, rfl⟩
  · exact h d hd
  · norm_num

/-- If one whole part is smaller, so is the number, whatever the fractions. -/
lemma val_lt_of_whole (x y : Dec) (hx : x.Plain) (hy : y.Plain) (h : num x.whole < num y.whole) :
    x.val < y.val := by
  have fx := frac_bounds x.frac hx.2.2
  have fy := frac_bounds y.frac hy.2.2
  have h' : (num x.whole : ℚ) + 1 ≤ num y.whole := by exact_mod_cast h
  unfold Dec.val
  linarith [fx.2, fy.1]

/-- **`atLeast` is exact for plain decimals:** it answers yes exactly when the price is at or above the target, as
numbers (no rounding, however many digits). -/
theorem atLeast_iff (p t : Dec) (hp : p.Plain) (ht : t.Plain) : atLeast p t = true ↔ t.val ≤ p.val := by
  have dp : ∀ d ∈ strip p.whole, d < 10 := fun d hd => hp.2.1 d (mem_strip _ d hd)
  have dt : ∀ d ∈ strip t.whole, d < 10 := fun d hd => ht.2.1 d (mem_strip _ d hd)
  unfold atLeast
  by_cases hl : (strip p.whole).length ≠ (strip t.whole).length
  · rw [if_pos hl, decide_eq_true_iff]
    rcases lt_or_gt_of_ne hl with h | h
    · have := lt_of_strip_length t.whole p.whole hp.2.1 hp.1 h
      constructor
      · intro h'; omega
      · intro h'; exact absurd h' (not_le.2 (val_lt_of_whole p t hp ht this))
    · have := lt_of_strip_length p.whole t.whole ht.2.1 ht.1 h
      exact ⟨fun _ => le_of_lt (val_lt_of_whole t p ht hp this), fun _ => h⟩
  rw [if_neg hl]
  push_neg at hl
  by_cases he : strip p.whole ≠ strip t.whole
  · rw [if_pos he, jsLt_iff _ _ hl.symm dt dp, num_strip, num_strip]
    have hne : num p.whole ≠ num t.whole := by
      intro h; apply he
      exact num_inj _ _ hl dp dt (by rw [num_strip, num_strip, h])
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨fun h' => absurd h' (not_lt.2 (le_of_lt h)),
        fun h' => absurd h' (not_le.2 (val_lt_of_whole p t hp ht h))⟩
    · exact ⟨fun _ => le_of_lt (val_lt_of_whole t p ht hp h), fun _ => h⟩
  rw [if_neg he]
  push_neg at he
  have hw : num p.whole = num t.whole := by rw [← num_strip, he, num_strip]
  set n := max p.frac.length t.frac.length
  have hpn : p.frac.length ≤ n := le_max_left _ _
  have htn : t.frac.length ≤ n := le_max_right _ _
  have hj := jsLt_iff (pad p.frac n) (pad t.frac n) (by rw [pad_length _ _ hpn, pad_length _ _ htn])
    (pad_digits _ _ hp.2.2) (pad_digits _ _ ht.2.2)
  unfold Dec.val
  rw [hw, frac_pad p.frac n hpn, frac_pad t.frac n htn, add_le_add_iff_left]
  have hpos : (0 : ℚ) < 10 ^ n := by positivity
  rw [div_le_div_iff_of_pos_right hpos, Nat.cast_le]
  cases h : jsLt (pad p.frac n) (pad t.frac n)
  · simp only [Bool.not_false, true_iff]
    rw [h] at hj
    simp at hj
    exact hj
  · simp only [Bool.not_true]
    rw [h] at hj
    simp only [true_iff] at hj
    simp only [Bool.false_eq_true, false_iff, not_le]
    exact hj

/-! ## 2. Rounds running at the same time: the record of the send (`claimSent`, alerts.ts:162-196) -/

/-- `TAKEOVER_MS` (alerts.ts:134): 10 minutes, in milliseconds. -/
def takeoverMs : ℕ := 600000

/-- How long a round can run: `maxDuration = 60` seconds (`api/alerts/run/route.ts`:13), in milliseconds. It appears
only in hypotheses: the code doesn't check it, the platform stops the round. -/
def roundMs : ℕ := 60000

/-- The step's record in `alerts-sent/` (`sentPath`, `Ledger`, alerts.ts:162-173). Tokens are the rounds' random codes
(`randomUUID`, alerts.ts:321), one per round and step; in the model each round is its own number. -/
inductive Rec
  /-- No record. -/
  | absent
  /-- `{at: since, token: tok, state: "sending"}`. -/
  | sending (since tok : ℕ)
  /-- `{token: tok, state: "sent"}`; `sent none` is an old record with only `{at}`, or one that can't be read. -/
  | sent (tok : Option ℕ)
  deriving DecidableEq

/-- The record's token. -/
def Rec.tok : Rec → Option ℕ
  | .absent => none
  | .sending _ k => some k
  | .sent k => k

/-- `claimSent`'s answer. -/
inductive Claim
  | mine
  | busy
  | sent
  deriving DecidableEq

/-- `claimSent(store, path, token, now)` (alerts.ts:183-196): the answer and the record afterwards. The create-only
write and the compare-and-swap after it are each one step of the store (`Store.create`, `Store.update`,
store.ts:15, 31), and together they come to this one atomic step: no record: ours; a record with our token: ours;
a "sending" record older than `TAKEOVER_MS` (`stale`, alerts.ts:135, `!(at >= now - TAKEOVER_MS)`): taken over;
any other "sending" record: busy; anything else: sent. -/
def claim (r : Rec) (tok now : ℕ) : Claim × Rec :=
  match r with
  | .absent => (.mine, .sending now tok)
  | .sending since k =>
    if k = tok then (.mine, r)
    else if since + takeoverMs < now then (.mine, .sending now tok) else (.busy, r)
  | .sent k => if k = some tok then (.mine, r) else (.sent, r)

/-- What the push service answered (`deps.send`, alerts.ts:345; a send that threw counts as `failed`). -/
inductive Send
  | ok
  | failed
  | gone
  deriving DecidableEq

/-- Where one round is with the step (alerts.ts:341-358). -/
inductive Pc
  /-- Has not claimed the record yet (it may never: not due, its mark not won, out of time, crashed). -/
  | idle
  /-- Claimed and got "busy" or "sent": done with the step. -/
  | out
  /-- Got "mine": may try to send. -/
  | mayTry
  /-- Tried to send and the push service said ok. -/
  | okd
  /-- Then wrote "sent" to the record. -/
  | wrote
  /-- Tried to send and it failed or the address was gone: will delete the record. -/
  | failed
  /-- Deleted the record. -/
  | deleted
  deriving DecidableEq

/-- The record and every round, at a moment in time (ms). -/
structure St where
  record : Rec
  pc : ℕ → Pc
  now : ℕ

/-- One thing that happens to the step's record. -/
inductive Act
  /-- Round `a` claims the record (`claimSent`, alerts.ts:341). -/
  | claim (a : ℕ)
  /-- Round `a` tries to send the notification, and the push service answers `r` (alerts.ts:345). -/
  | send (a : ℕ) (r : Send)
  /-- Round `a` writes "sent" over the record if it still has `a`'s token (alerts.ts:348). -/
  | sentWrite (a : ℕ)
  /-- Round `a` deletes the record after a send that failed or found the address gone (alerts.ts:354, 356). -/
  | del (a : ℕ)
  /-- The record is deleted from outside a round: the step removed on the page, alerts turned off
  (`api/alerts/route.ts`:59-66, 77-84), or the yearly sweep (`sweepSent`, `SENT_DAYS`). -/
  | wipe
  deriving DecidableEq

/-- An event: when it happened (ms, on one clock) and what. -/
structure Ev where
  time : ℕ
  act : Act
  deriving DecidableEq

/-- The round an event belongs to, if any. -/
def Act.round : Act → Option ℕ
  | .claim a => some a
  | .send a _ => some a
  | .sentWrite a => some a
  | .del a => some a
  | .wipe => none

/-- One event. `start a` is round `a`'s `now` (alerts.ts:265), the time it puts in what it writes. Each round does
its steps in the code's order: an event out of that order can't happen (`none`). A round that stops (a crash, a
store write that failed, out of time) simply has no more events. -/
def step (start : ℕ → ℕ) (s : St) (e : Ev) : Option St :=
  match e.act with
  | .claim a =>
    if s.pc a = .idle then
      some ⟨(claim s.record a (start a)).2,
        Function.update s.pc a (if (claim s.record a (start a)).1 = .mine then .mayTry else .out), e.time⟩
    else none
  | .send a r =>
    if s.pc a = .mayTry then some ⟨s.record, Function.update s.pc a (if r = .ok then .okd else .failed), e.time⟩
    else none
  | .sentWrite a =>
    if s.pc a = .okd then
      some ⟨if s.record.tok = some a then .sent (some a) else s.record, Function.update s.pc a .wrote, e.time⟩
    else none
  | .del a => if s.pc a = .failed then some ⟨.absent, Function.update s.pc a .deleted, e.time⟩ else none
  | .wipe => some ⟨.absent, s.pc, e.time⟩

/-- A list of events, in the order they happen; `none` if one can't happen. -/
def exec (start : ℕ → ℕ) : St → List Ev → Option St
  | s, [] => some s
  | s, e :: tr => (step start s e).bind (fun s' => exec start s' tr)

/-- A new step: no record, no round has looked at it. -/
def init : St := ⟨.absent, fun _ => .idle, 0⟩

/-- Hypothesis: the events are listed in time order. -/
def Ordered (tr : List Ev) : Prop := tr.Pairwise (fun e f => e.time ≤ f.time)

/-- Hypothesis: every event of round `a` happens while it runs: from its start to 60 seconds later. -/
def Timely (start : ℕ → ℕ) (tr : List Ev) : Prop :=
  ∀ e ∈ tr, ∀ a, e.act.round = some a → start a ≤ e.time ∧ e.time ≤ start a + roundMs

/-- Hypothesis: the record is not deleted from outside a round (the step stays saved, alerts stay on, less than
`SENT_DAYS`). -/
def NoWipe (tr : List Ev) : Prop := ∀ e ∈ tr, e.act ≠ .wipe

/-- A round in the middle of its work. -/
def Busy (p : Pc) : Prop := p = .mayTry ∨ p = .okd ∨ p = .failed

/-- What holds at every moment of a run without wipes in which rounds keep to their 60 seconds. -/
structure Inv (start : ℕ → ℕ) (s : St) : Prop where
  idle_tok : ∀ a, s.pc a = .idle → s.record.tok ≠ some a
  busy : ∀ a, Busy (s.pc a) → s.record = .sending (start a) a ∨ start a + roundMs < s.now
  wrote : ∀ a, s.pc a = .wrote → s.record = .sent (some a)
  okd : ∀ a, s.pc a = .okd → s.record = .sending (start a) a ∨ start a + takeoverMs < s.now
  after_ok : ∀ a b, a ≠ b → (s.pc a = .okd ∨ s.pc a = .wrote) → s.pc b = .mayTry → s.now ≤ start b + roundMs →
    s.pc a = .okd ∧ start a + takeoverMs < s.now

lemma inv_init (start : ℕ → ℕ) : Inv start init where
  idle_tok := by intro a _; simp [init, Rec.tok]
  busy := by intro a h; simp [init, Busy] at h
  wrote := by intro a h; simp [init] at h
  okd := by intro a h; simp [init] at h
  after_ok := by intro a b _ h; simp [init] at h

lemma roundMs_lt : roundMs < takeoverMs := by decide

/-- A round still within its 60 seconds that is in the middle of its work holds the record. -/
lemma holds (start : ℕ → ℕ) (s : St) (hi : Inv start s) (a t : ℕ) (hb : Busy (s.pc a)) (hn : s.now ≤ t)
    (ht : t ≤ start a + roundMs) : s.record = .sending (start a) a := by
  rcases hi.busy a hb with h | h
  · exact h
  · omega

/-- What a claim by a round that hasn't written the record does: it gets "mine" and the record becomes its own
"sending" record (only over no record, or a "sending" one older than `TAKEOVER_MS`), or it doesn't, and the record
stays as it was. -/
lemma claim_spec (r : Rec) (tok now : ℕ) (hr : r.tok ≠ some tok) :
    ((claim r tok now).1 = .mine ∧ (claim r tok now).2 = .sending now tok ∧
      (∀ since k, r = .sending since k → since + takeoverMs < now) ∧ (∀ k, r ≠ .sent k)) ∨
    ((claim r tok now).1 ≠ .mine ∧ (claim r tok now).2 = r) := by
  cases r with
  | absent =>
    left
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro _ _ h; cases h
    · intro _ h; cases h
  | sending since k =>
    have hk : k ≠ tok := by simpa [Rec.tok] using hr
    simp only [claim, if_neg hk]
    split_ifs with h
    · left
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro _ _ h'; cases h'; exact h
      · intro _ h'; cases h'
    · right; exact ⟨by simp, rfl⟩
  | sent k =>
    have hk : k ≠ some tok := by simpa [Rec.tok] using hr
    simp only [claim, if_neg hk]
    right; constructor <;> simp

lemma upd_ne {f : ℕ → Pc} {c a : ℕ} {v : Pc} (h : a ≠ c) : Function.update f c v a = f a :=
  Function.update_of_ne h v f

lemma step_inv (start : ℕ → ℕ) (s s' : St) (e : Ev) (hi : Inv start s) (hn : s.now ≤ e.time)
    (ht : ∀ a, e.act.round = some a → start a ≤ e.time ∧ e.time ≤ start a + roundMs) (hw : e.act ≠ .wipe)
    (hs : step start s e = some s') : Inv start s' := by
  rcases e with ⟨t, act⟩
  simp only at hn ht hw
  cases act with
  | wipe => exact absurd rfl hw
  | claim c =>
    have htc := ht c rfl
    simp only [step] at hs
    by_cases hpc : s.pc c = .idle
    swap
    · rw [if_neg hpc] at hs; cases hs
    rw [if_pos hpc] at hs
    cases hs
    have hct := hi.idle_tok c hpc
    rcases claim_spec s.record c (start c) hct with ⟨hm, hr, hstale, hnsent⟩ | ⟨hm, hr⟩
    · -- "mine": the record is now this round's; every other round still working is past its 60 seconds
      rw [hm, hr]
      simp only [if_true]
      have other : ∀ b, b ≠ c → Busy (s.pc b) → start b + roundMs < t := by
        intro b hbc hb
        rcases hi.busy b hb with h | h
        · have := hstale _ _ h; have := roundMs_lt; omega
        · omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp at ha
        · simp [Rec.tok]; exact fun h => hac h.symm
      · intro a ha
        by_cases hac : a = c
        · subst hac; exact Or.inl rfl
        · rw [upd_ne hac] at ha; exact Or.inr (other a hac ha)
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp at ha
        · rw [upd_ne hac] at ha; exact absurd (hi.wrote a ha) (hnsent _)
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp at ha
        · rw [upd_ne hac] at ha
          right
          rcases hi.okd a ha with h | h
          · have := hstale _ _ h; omega
          · omega
      · intro a b hab ha hb hbt
        by_cases hac : a = c
        · subst hac; simp at ha
        rw [upd_ne hac] at ha ⊢
        by_cases hbc : b = c
        · subst hbc
          rcases ha with ha | ha
          · refine ⟨ha, ?_⟩
            rcases hi.okd a ha with h | h
            · have := hstale _ _ h; omega
            · omega
          · exact absurd (hi.wrote a ha) (hnsent _)
        · rw [upd_ne hbc] at hb
          have := hi.after_ok a b hab ha hb (by omega)
          exact ⟨this.1, by omega⟩
    · -- not "mine": the record is as it was, and the round is done with the step
      rw [if_neg hm, hr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp at ha
        · rw [upd_ne hac] at ha; exact hi.idle_tok a ha
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp [Busy] at ha
        · rw [upd_ne hac] at ha
          rcases hi.busy a ha with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp at ha
        · rw [upd_ne hac] at ha; exact hi.wrote a ha
      · intro a ha
        by_cases hac : a = c
        · subst hac; simp at ha
        · rw [upd_ne hac] at ha
          rcases hi.okd a ha with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
      · intro a b hab ha hb hbt
        by_cases hbc : b = c
        · subst hbc; simp at hb
        rw [upd_ne hbc] at hb
        by_cases hac : a = c
        · subst hac; simp at ha
        rw [upd_ne hac] at ha ⊢
        have := hi.after_ok a b hab ha hb (by omega)
        exact ⟨this.1, by omega⟩
  | send c r =>
    have htc := ht c rfl
    simp only [step] at hs
    by_cases hpc : s.pc c = .mayTry
    swap
    · rw [if_neg hpc] at hs; cases hs
    rw [if_pos hpc] at hs
    cases hs
    have hrc := holds start s hi c t (Or.inl hpc) hn htc.2
    have other : ∀ b, b ≠ c → Busy (s.pc b) → start b + roundMs < t := by
      intro b hbc hb
      rcases hi.busy b hb with h | h
      · rw [hrc] at h; simp at h; exact absurd h.2.symm hbc
      · omega
    have hv : (if r = .ok then Pc.okd else Pc.failed) = .okd ∨ (if r = .ok then Pc.okd else Pc.failed) = .failed := by
      split_ifs <;> simp
    generalize (if r = .ok then Pc.okd else Pc.failed) = v at hv ⊢
    have hvb : Busy v := by rcases hv with rfl | rfl <;> simp [Busy]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp at ha; rcases hv with rfl | rfl <;> simp at ha
      · rw [upd_ne hac] at ha; exact hi.idle_tok a ha
    · intro a ha
      by_cases hac : a = c
      · subst hac; exact Or.inl hrc
      · rw [upd_ne hac] at ha; exact Or.inr (other a hac ha)
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp at ha; rcases hv with rfl | rfl <;> simp at ha
      · rw [upd_ne hac] at ha; exact hi.wrote a ha
    · intro a ha
      by_cases hac : a = c
      · subst hac; exact Or.inl hrc
      · rw [upd_ne hac] at ha
        rcases hi.okd a ha with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
    · intro a b hab ha hb hbt
      by_cases hbc : b = c
      · subst hbc; simp at hb; rcases hv with rfl | rfl <;> simp at hb
      rw [upd_ne hbc] at hb
      by_cases hac : a = c
      · subst hac
        have := other b (Ne.symm hab) (Or.inl hb)
        omega
      rw [upd_ne hac] at ha ⊢
      have := hi.after_ok a b hab ha hb (by omega)
      exact ⟨this.1, by omega⟩
  | sentWrite c =>
    have htc := ht c rfl
    simp only [step] at hs
    by_cases hpc : s.pc c = .okd
    swap
    · rw [if_neg hpc] at hs; cases hs
    rw [if_pos hpc] at hs
    cases hs
    have hrc := holds start s hi c t (Or.inr (Or.inl hpc)) hn htc.2
    have other : ∀ b, b ≠ c → Busy (s.pc b) → start b + roundMs < t := by
      intro b hbc hb
      rcases hi.busy b hb with h | h
      · rw [hrc] at h; simp at h; exact absurd h.2.symm hbc
      · omega
    have hnew : (if s.record.tok = some c then Rec.sent (some c) else s.record) = .sent (some c) := by
      rw [hrc]; simp [Rec.tok]
    rw [hnew]
    have := roundMs_lt
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp at ha
      · simp [Rec.tok]; exact fun h => hac h.symm
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp [Busy] at ha
      · rw [upd_ne hac] at ha; exact Or.inr (other a hac ha)
    · intro a ha
      by_cases hac : a = c
      · rw [hac]
      · rw [upd_ne hac] at ha
        have := hi.wrote a ha
        rw [hrc] at this; simp at this
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp at ha
      · rw [upd_ne hac] at ha
        rcases hi.okd a ha with h | h
        · rw [hrc] at h; simp at h; exact absurd h.2.symm hac
        · exact Or.inr (by omega)
    · intro a b hab ha hb hbt
      by_cases hbc : b = c
      · subst hbc; simp at hb
      · rw [upd_ne hbc] at hb
        have := other b hbc (Or.inl hb)
        omega
  | del c =>
    have htc := ht c rfl
    simp only [step] at hs
    by_cases hpc : s.pc c = .failed
    swap
    · rw [if_neg hpc] at hs; cases hs
    rw [if_pos hpc] at hs
    cases hs
    have hrc := holds start s hi c t (Or.inr (Or.inr hpc)) hn htc.2
    have other : ∀ b, b ≠ c → Busy (s.pc b) → start b + roundMs < t := by
      intro b hbc hb
      rcases hi.busy b hb with h | h
      · rw [hrc] at h; simp at h; exact absurd h.2.symm hbc
      · omega
    have := roundMs_lt
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro a _; simp [Rec.tok]
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp [Busy] at ha
      · rw [upd_ne hac] at ha; exact Or.inr (other a hac ha)
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp at ha
      · rw [upd_ne hac] at ha
        have := hi.wrote a ha
        rw [hrc] at this; simp at this
    · intro a ha
      by_cases hac : a = c
      · subst hac; simp at ha
      · rw [upd_ne hac] at ha
        rcases hi.okd a ha with h | h
        · rw [hrc] at h; simp at h; exact absurd h.2.symm hac
        · exact Or.inr (by omega)
    · intro a b hab ha hb hbt
      by_cases hbc : b = c
      · subst hbc; simp at hb
      · rw [upd_ne hbc] at hb
        have := other b hbc (Or.inl hb)
        omega

lemma step_now (start : ℕ → ℕ) (s s' : St) (e : Ev) (h : step start s e = some s') : s'.now = e.time := by
  rcases e with ⟨t, act⟩
  cases act <;> simp only [step] at h <;> (try split_ifs at h) <;> cases h <;> rfl

lemma step_pc_ne (start : ℕ → ℕ) (s s' : St) (e : Ev) (a : ℕ) (h : step start s e = some s')
    (ha : e.act.round ≠ some a) : s'.pc a = s.pc a := by
  rcases e with ⟨t, act⟩
  cases act <;> simp only [step, Act.round] at h ha <;> (try split_ifs at h) <;> cases h <;>
    first | rfl | exact Function.update_of_ne (by rintro rfl; exact ha rfl) _ _

lemma step_actor (start : ℕ → ℕ) (s s' : St) (e : Ev) (c : ℕ) (h : step start s e = some s')
    (hc : e.act.round = some c) :
    (s.pc c = .okd → e.act = .sentWrite c ∧ s'.pc c = .wrote) ∧ s.pc c ≠ .wrote := by
  rcases e with ⟨t, act⟩
  cases act <;> simp [Act.round] at hc <;> subst hc <;> simp only [step] at h <;>
    split_ifs at h with g <;> cases h <;> simp [g]

lemma step_pc_wrote (start : ℕ → ℕ) (s s' : St) (e : Ev) (a : ℕ) (h : step start s e = some s')
    (ha : s.pc a = .wrote) : s'.pc a = .wrote := by
  by_cases hr : e.act.round = some a
  · exact absurd ha (step_actor start s s' e a h hr).2
  · rw [step_pc_ne start s s' e a h hr]; exact ha

lemma step_pc_okd (start : ℕ → ℕ) (s s' : St) (e : Ev) (a : ℕ) (h : step start s e = some s')
    (ha : s.pc a = .okd) : (s'.pc a = .okd ∧ e.act ≠ .sentWrite a) ∨ s'.pc a = .wrote := by
  by_cases hr : e.act.round = some a
  · exact Or.inr ((step_actor start s s' e a h hr).1 ha).2
  · left; refine ⟨by rw [step_pc_ne start s s' e a h hr]; exact ha, ?_⟩
    intro he; rw [he] at hr; exact hr rfl

lemma exec_append (start : ℕ → ℕ) (s : St) (p q : List Ev) :
    exec start s (p ++ q) = (exec start s p).bind (fun m => exec start m q) := by
  induction p generalizing s with
  | nil => simp [exec]
  | cons e p ih =>
    simp only [List.cons_append, exec]
    cases step start s e with
    | none => rfl
    | some s1 => simp only [Option.bind_some]; exact ih s1

lemma exec_split (start : ℕ → ℕ) (s u : St) (p q : List Ev) (h : exec start s (p ++ q) = some u) :
    ∃ m, exec start s p = some m ∧ exec start m q = some u := by
  rw [exec_append] at h
  cases hp : exec start s p with
  | none => rw [hp] at h; cases h
  | some m => rw [hp] at h; exact ⟨m, rfl, h⟩

lemma exec_cons (start : ℕ → ℕ) (s u : St) (e : Ev) (q : List Ev) (h : exec start s (e :: q) = some u) :
    ∃ m, step start s e = some m ∧ exec start m q = some u := by
  simp only [exec] at h
  cases hp : step start s e with
  | none => rw [hp] at h; cases h
  | some m => rw [hp] at h; exact ⟨m, rfl, h⟩

lemma exec_wrote (start : ℕ → ℕ) (a : ℕ) :
    ∀ (tr : List Ev) (s u : St), exec start s tr = some u → s.pc a = .wrote → u.pc a = .wrote
  | [], s, u, h, ha => by simp [exec] at h; subst h; exact ha
  | e :: tr, s, u, h, ha => by
    obtain ⟨m, h1, h2⟩ := exec_cons start s u e tr h
    exact exec_wrote start a tr m u h2 (step_pc_wrote start s m e a h1 ha)

lemma exec_okd (start : ℕ → ℕ) (a : ℕ) :
    ∀ (tr : List Ev) (s u : St), exec start s tr = some u → s.pc a = .okd →
      (u.pc a = .okd ∧ ∀ e ∈ tr, e.act ≠ .sentWrite a) ∨ u.pc a = .wrote
  | [], s, u, h, ha => by simp [exec] at h; subst h; exact Or.inl ⟨ha, by simp⟩
  | e :: tr, s, u, h, ha => by
    obtain ⟨m, h1, h2⟩ := exec_cons start s u e tr h
    rcases step_pc_okd start s m e a h1 ha with ⟨hm, he⟩ | hm
    · rcases exec_okd start a tr m u h2 hm with ⟨hu, hall⟩ | hu
      · left; refine ⟨hu, ?_⟩
        intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact he
        · exact hall f hf
      · exact Or.inr hu
    · exact Or.inr (exec_wrote start a tr m u h2 hm)

lemma exec_now (start : ℕ → ℕ) (T : ℕ) :
    ∀ (tr : List Ev) (s u : St), exec start s tr = some u → s.now ≤ T → (∀ e ∈ tr, e.time ≤ T) → u.now ≤ T
  | [], s, u, h, hs, _ => by simp [exec] at h; subst h; exact hs
  | e :: tr, s, u, h, _, he => by
    obtain ⟨m, h1, h2⟩ := exec_cons start s u e tr h
    have := step_now start s m e h1
    exact exec_now start T tr m u h2 (by rw [this]; exact he e (by simp)) (fun f hf => he f (by simp [hf]))

lemma inv_exec (start : ℕ → ℕ) :
    ∀ (tr : List Ev) (s u : St), Inv start s → (∀ e ∈ tr, s.now ≤ e.time) → Ordered tr → Timely start tr →
      NoWipe tr → exec start s tr = some u → Inv start u
  | [], s, u, hi, _, _, _, _, h => by simp [exec] at h; subst h; exact hi
  | e :: tr, s, u, hi, hle, hord, htime, hw, h => by
    obtain ⟨m, h1, h2⟩ := exec_cons start s u e tr h
    have hm := step_inv start s m e hi (hle e (by simp)) (htime e (by simp)) (hw e (by simp)) h1
    have hnow := step_now start s m e h1
    have hord' := List.pairwise_cons.1 hord
    exact inv_exec start tr m u hm (fun f hf => by rw [hnow]; exact hord'.1 f hf) hord'.2
      (fun f hf => htime f (by simp [hf])) (fun f hf => hw f (by simp [hf])) h2

/-- **Concurrent rounds: a step is sent at most once, except when the first send's "sent" write was lost.**
Rounds may run at the same time and in any interleaving, may stop at any point (a crash, a store write that failed,
out of time), and the push service may answer anything. Hypotheses: the record isn't deleted from outside a round
(`NoWipe`), events are in time order (`Ordered`), and every event of a round happens within 60 seconds of its start
(`Timely`, with `TAKEOVER_MS` = 10 minutes). Then if round `a`'s send was taken by the push service (ok) and a
different round `b` tries to send the step later, round `a` never wrote "sent" in between, and `b` tries more than
10 minutes after `a` started. -/
theorem sent_at_most_once (start : ℕ → ℕ) (p m q : List Ev) (a b ti tj : ℕ) (r : Send) (fin : St)
    (hrun : exec start init (p ++ ⟨ti, .send a .ok⟩ :: (m ++ ⟨tj, .send b r⟩ :: q)) = some fin)
    (hord : Ordered (p ++ ⟨ti, .send a .ok⟩ :: (m ++ ⟨tj, .send b r⟩ :: q)))
    (htime : Timely start (p ++ ⟨ti, .send a .ok⟩ :: (m ++ ⟨tj, .send b r⟩ :: q)))
    (hwipe : NoWipe (p ++ ⟨ti, .send a .ok⟩ :: (m ++ ⟨tj, .send b r⟩ :: q)))
    (hab : a ≠ b) :
    (∀ e ∈ m, e.act ≠ .sentWrite a) ∧ start a + takeoverMs < tj := by
  set pre := p ++ ⟨ti, .send a .ok⟩ :: m with hpre
  have hl : p ++ ⟨ti, .send a .ok⟩ :: (m ++ ⟨tj, .send b r⟩ :: q) = pre ++ ⟨tj, .send b r⟩ :: q := by
    simp [hpre]
  rw [hl] at hrun hord htime hwipe
  obtain ⟨s3, hpre3, hrest⟩ := exec_split start init fin pre _ hrun
  obtain ⟨s4, hstep, _⟩ := exec_cons start s3 fin _ q hrest
  have hordp := (List.pairwise_append.1 hord)
  have hi3 : Inv start s3 :=
    inv_exec start pre init s3 (inv_init start) (fun _ _ => Nat.zero_le _) hordp.1
      (fun f hf => htime f (by simp [hf])) (fun f hf => hwipe f (by simp [hf])) hpre3
  have hnow3 : s3.now ≤ tj :=
    exec_now start tj pre init s3 hpre3 (Nat.zero_le _) (fun f hf => hordp.2.2 f hf ⟨tj, .send b r⟩ (by simp))
  have hb : s3.pc b = .mayTry := by
    simp only [step] at hstep; split_ifs at hstep with h <;> exact h
  have htb := htime ⟨tj, .send b r⟩ (by simp) b rfl
  simp only at htb
  obtain ⟨s1, hp1, hrest1⟩ := exec_split start init s3 p _ hpre3
  obtain ⟨s2, hstep2, hm2⟩ := exec_cons start s1 s3 _ m hrest1
  have ha2 : s2.pc a = .okd := by
    simp only [step] at hstep2; split_ifs at hstep2; cases hstep2; simp
  have ha3 := exec_okd start a m s2 s3 hm2 ha2
  have key := hi3.after_ok a b hab (by rcases ha3 with ⟨h, _⟩ | h <;> simp [h]) hb (by omega)
  refine ⟨?_, by omega⟩
  rcases ha3 with ⟨_, hall⟩ | h
  · exact hall
  · rw [key.1] at h; cases h

/-- The record says sent, and every round still in the middle of its work is past its 60 seconds. -/
def Blocked (start : ℕ → ℕ) (s : St) : Prop :=
  (∃ k, s.record = .sent k) ∧ ∀ b, Busy (s.pc b) → start b + roundMs < s.now

lemma step_blocked (start : ℕ → ℕ) (s s' : St) (e : Ev) (hi : Inv start s) (hb : Blocked start s)
    (hn : s.now ≤ e.time) (ht : ∀ a, e.act.round = some a → start a ≤ e.time ∧ e.time ≤ start a + roundMs)
    (hw : e.act ≠ .wipe) (hs : step start s e = some s') : Blocked start s' ∧ ∀ b r, e.act ≠ .send b r := by
  rcases e with ⟨t, act⟩
  obtain ⟨⟨k, hk⟩, hdead⟩ := hb
  simp only at hn ht hw
  cases act with
  | wipe => exact absurd rfl hw
  | claim c =>
    simp only [step] at hs
    by_cases hpc : s.pc c = .idle
    swap
    · rw [if_neg hpc] at hs; cases hs
    rw [if_pos hpc] at hs
    cases hs
    have hct := hi.idle_tok c hpc
    rw [hk] at hct ⊢
    simp only [Rec.tok] at hct
    simp only [claim, if_neg hct]
    refine ⟨⟨⟨k, rfl⟩, ?_⟩, by simp⟩
    intro b hb
    by_cases hbc : b = c
    · subst hbc; simp [Busy] at hb
    · dsimp only at hb ⊢; rw [upd_ne hbc] at hb; have := hdead b hb; omega
  | send c r =>
    simp only [step] at hs
    split_ifs at hs with hpc <;> (have := hdead c (Or.inl hpc); have := ht c rfl; omega)
  | sentWrite c =>
    simp only [step] at hs
    split_ifs at hs with hpc <;> (have := hdead c (Or.inr (Or.inl hpc)); have := ht c rfl; omega)
  | del c =>
    simp only [step] at hs
    split_ifs at hs with hpc
    have := hdead c (Or.inr (Or.inr hpc)); have := ht c rfl; omega

lemma blocked_exec (start : ℕ → ℕ) :
    ∀ (tr : List Ev) (s u : St), Inv start s → Blocked start s → (∀ e ∈ tr, s.now ≤ e.time) → Ordered tr →
      Timely start tr → NoWipe tr → exec start s tr = some u → ∀ e ∈ tr, ∀ b r, e.act ≠ .send b r
  | [], _, _, _, _, _, _, _, _, _ => by simp
  | e :: tr, s, u, hi, hb, hle, hord, htime, hw, h => by
    obtain ⟨m, h1, h2⟩ := exec_cons start s u e tr h
    have hle1 := hle e (by simp)
    have ht1 := htime e (by simp)
    have hw1 := hw e (by simp)
    obtain ⟨hbm, hne⟩ := step_blocked start s m e hi hb hle1 ht1 hw1 h1
    have hm := step_inv start s m e hi hle1 ht1 hw1 h1
    have hnow := step_now start s m e h1
    have hord' := List.pairwise_cons.1 hord
    have rest := blocked_exec start tr m u hm hbm (fun f hf => by rw [hnow]; exact hord'.1 f hf) hord'.2
      (fun f hf => htime f (by simp [hf])) (fun f hf => hw f (by simp [hf])) h2
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hne
    · exact rest f hf

/-- **A "sent" record means no further send.** Same hypotheses as `sent_at_most_once`. After a round writes "sent" to
the step's record, no round (one already running or any later one, whatever happens to the address files) tries to
send the step again. -/
theorem no_try_after_sent (start : ℕ → ℕ) (p q : List Ev) (a t : ℕ) (fin : St)
    (hrun : exec start init (p ++ ⟨t, .sentWrite a⟩ :: q) = some fin)
    (hord : Ordered (p ++ ⟨t, .sentWrite a⟩ :: q))
    (htime : Timely start (p ++ ⟨t, .sentWrite a⟩ :: q))
    (hwipe : NoWipe (p ++ ⟨t, .sentWrite a⟩ :: q)) :
    ∀ e ∈ q, ∀ b r, e.act ≠ .send b r := by
  obtain ⟨s1, hp1, hrest⟩ := exec_split start init fin p _ hrun
  obtain ⟨s2, hstep, hq⟩ := exec_cons start s1 fin _ q hrest
  have hordp := List.pairwise_append.1 hord
  have hi1 : Inv start s1 :=
    inv_exec start p init s1 (inv_init start) (fun _ _ => Nat.zero_le _) hordp.1
      (fun f hf => htime f (by simp [hf])) (fun f hf => hwipe f (by simp [hf])) hp1
  have hnow1 : s1.now ≤ t :=
    exec_now start t p init s1 hp1 (Nat.zero_le _) (fun f hf => hordp.2.2 f hf ⟨t, .sentWrite a⟩ (by simp))
  have hta := htime ⟨t, .sentWrite a⟩ (by simp) a rfl
  have hwa := hwipe ⟨t, .sentWrite a⟩ (by simp)
  have hi2 := step_inv start s1 s2 _ hi1 hnow1 (fun c hc => htime _ (by simp) c hc) hwa hstep
  have hnow2 := step_now start s1 s2 _ hstep
  simp only [step] at hstep
  by_cases hpc : s1.pc a = .okd
  swap
  · rw [if_neg hpc] at hstep; cases hstep
  rw [if_pos hpc] at hstep
  have hrc := holds start s1 hi1 a t (Or.inr (Or.inl hpc)) hnow1 hta.2
  have hb2 : Blocked start s2 := by
    cases hstep
    refine ⟨⟨some a, by dsimp only; rw [hrc]; simp [Rec.tok]⟩, ?_⟩
    intro b hb
    by_cases hba : b = a
    · subst hba; simp [Busy] at hb
    · dsimp only at hb ⊢
      rw [upd_ne hba] at hb
      rcases hi1.busy b hb with h | h
      · rw [hrc] at h; simp at h; exact absurd h.2.symm hba
      · omega
  have hordq := List.pairwise_cons.1 hordp.2.1
  exact blocked_exec start q s2 fin hi2 hb2 (fun f hf => by rw [hnow2]; exact hordq.1 f hf) hordq.2
    (fun f hf => htime f (by simp [hf])) (fun f hf => hwipe f (by simp [hf])) hq

/-- **The exception is real** (the one the code names, alerts.ts:314-316): round 0 sends and the push service takes it,
but its "sent" write is lost (the round crashed, or the write failed); 11 minutes later round 1 takes the record over
and sends again, and the push service takes that too. Every hypothesis of `sent_at_most_once` holds. -/
theorem resent_after_lost_write :
    ∃ (start : ℕ → ℕ) (tr : List Ev) (fin : St), exec start init tr = some fin ∧ Ordered tr ∧ Timely start tr ∧
      NoWipe tr ∧ (∀ e ∈ tr, e.act ≠ .sentWrite 0) ∧
      ⟨1000, .send 0 .ok⟩ ∈ tr ∧ ⟨661000, .send 1 .ok⟩ ∈ tr := by
  let start : ℕ → ℕ := fun a => if a = 0 then 0 else 660000
  let tr : List Ev := [⟨0, .claim 0⟩, ⟨1000, .send 0 .ok⟩, ⟨660000, .claim 1⟩, ⟨661000, .send 1 .ok⟩]
  have hx : (exec start init tr).isSome = true := by decide
  obtain ⟨fin, hfin⟩ := Option.isSome_iff_exists.1 hx
  refine ⟨start, tr, fin, hfin, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ordered; decide
  · intro e he a ha
    simp only [tr, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [Act.round] at ha <;> subst ha <;> simp [start, roundMs]
  · intro e he; simp only [tr, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp
  · intro e he; simp only [tr, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp
  · simp [tr]
  · simp [tr]

/-! ## 3. One step's rounds, one after another (`runAlerts`, alerts.ts:265-362)

Rounds run one at a time (section 2 covers rounds at the same time). Each store write a round makes either lands and
the round goes on (`ok`), never lands and throws (`lost`), or lands and still throws (`landedErr`): the store's retries
can end any of these ways. A round that throws stops for this address (alerts.ts:361). Between rounds the page may
save the address file (route.ts POST), or the file or the record may go. Round `k`'s random code is `k` itself. -/

/-- How one store write ended. -/
inductive Write
  | ok
  | lost
  | landedErr
  deriving DecidableEq

def Write.landed : Write → Bool
  | .ok => true
  | .lost => false
  | .landedErr => true

def Write.thrown : Write → Bool
  | .ok => false
  | _ => true

/-- `new` if the write landed, else `old`. -/
def wr {α : Type} (w : Write) (old new : α) : α := if w.landed then new else old

/-- The step's part of the address file: `hits[id]`, `sending[id]` (when, round code) and `fails`. -/
structure Mark where
  hit : Option ℕ
  mark : Option (ℕ × ℕ)
  fails : ℕ

/-- `toSend` (alerts.ts:141-145): not reached, or marked by a round whose mark is older than `TAKEOVER_MS`. -/
def Mark.toSend (f : Mark) (now : ℕ) : Bool :=
  match f.hit, f.mark with
  | none, _ => true
  | some _, none => false
  | some h, some (t0, _) => decide (h = t0) && decide (t0 + takeoverMs < now)

/-- The round's mark (alerts.ts:333). -/
def Mark.markBy (f : Mark) (now tok : ℕ) : Mark := ⟨some now, some (now, tok), f.fails⟩

/-- `unmark` (alerts.ts:325): only the round's own mark goes, and `hits` with it if it is the mark's. -/
def Mark.unmark (f : Mark) (tok : ℕ) : Mark :=
  match f.mark with
  | some (t0, k) => if k = tok then ⟨if f.hit = some t0 then none else f.hit, none, f.fails⟩ else f
  | none => f

/-- `forget` (alerts.ts:324): the round's own mark goes, `hits` stays. -/
def Mark.forget (f : Mark) (tok : ℕ) : Mark :=
  match f.mark with
  | some (_, k) => if k = tok then ⟨f.hit, none, f.fails⟩ else f
  | none => f

/-- One step's state: its part of the address file (`none`: no file) and its record. -/
structure RS where
  file : Option Mark
  record : Rec

/-- What happens to one round: whether it gets to the step at all (the file read, a price, time left), what the push
service answers, and how each of its store writes ends. -/
structure Luck where
  reached : Bool
  send : Send
  mark : Write
  claim : Write
  unmark : Write
  sentW : Write
  fileW : Write
  delRec : Write
  delFile : Write

/-- Every store write of the round lands without an error. -/
def Luck.land (l : Luck) : Prop :=
  l.mark = .ok ∧ l.claim = .ok ∧ l.unmark = .ok ∧ l.sentW = .ok ∧ l.fileW = .ok ∧ l.delRec = .ok ∧ l.delFile = .ok

/-- `MAX_FAILS` (alerts.ts:247). -/
def maxFails : ℕ := 20

/-- One round, for one step: the state after it, and what the push service answered if it tried to send
(`none`: it didn't try). `now` is the round's time, `tok` its code, `atOrAbove` whether its price is at or above the
step. Follows alerts.ts:321-359 line by line. -/
def roundR (now tok : ℕ) (atOrAbove : Bool) (l : Luck) (s : RS) : RS × Option Send :=
  match s.file with
  | none => (s, none)
  | some f =>
    if l.reached && f.toSend now && atOrAbove then
      if l.mark.thrown then
        (⟨some (if l.mark.landed then wr l.unmark (f.markBy now tok) ((f.markBy now tok).unmark tok)
          else wr l.unmark f (f.unmark tok)), s.record⟩, none)
      else if l.claim.thrown then
        (⟨some (wr l.unmark (f.markBy now tok) ((f.markBy now tok).unmark tok)),
          wr l.claim s.record (claim s.record tok now).2⟩, none)
      else match (claim s.record tok now).1 with
        | .sent => (⟨some (wr l.unmark (f.markBy now tok) ((f.markBy now tok).forget tok)), s.record⟩, none)
        | .busy => (⟨some (wr l.unmark (f.markBy now tok) ((f.markBy now tok).unmark tok)), s.record⟩, none)
        | .mine =>
          match l.send with
          | .ok =>
            (⟨some (wr l.fileW (f.markBy now tok) { (f.markBy now tok).forget tok with fails := 0 }),
              wr l.sentW (claim s.record tok now).2
                (if (claim s.record tok now).2.tok = some tok then .sent (some tok) else (claim s.record tok now).2)⟩,
              some .ok)
          | .gone =>
            if l.delRec.thrown then
              (⟨some (f.markBy now tok), wr l.delRec (claim s.record tok now).2 .absent⟩, some .gone)
            else (⟨wr l.delFile (some (f.markBy now tok)) none, .absent⟩, some .gone)
          | .failed =>
            if l.fileW.thrown then
              (⟨some (wr l.fileW (f.markBy now tok)
                { (f.markBy now tok).unmark tok with fails := f.fails + 1 }), (claim s.record tok now).2⟩, some .failed)
            else if l.delRec.thrown then
              (⟨some { (f.markBy now tok).unmark tok with fails := f.fails + 1 },
                wr l.delRec (claim s.record tok now).2 .absent⟩, some .failed)
            else
              (⟨if maxFails ≤ f.fails + 1 then wr l.delFile (some { (f.markBy now tok).unmark tok with fails := f.fails + 1 }) none
                else some { (f.markBy now tok).unmark tok with fails := f.fails + 1 }, .absent⟩, some .failed)
    else (s, none)

/-- What happens between two rounds. `quiet`: nothing. `saw t`: the open page saw the step reached and showed its own notice, then saved
(route.ts:52-57). `save`: the page saved the steps (a new file if there was none: deleted after 30 days unsynced, or
after 20 failed sends, or a new push address). `drop`: the address file was deleted. `wipeRec`: the step's record was
deleted (the step removed or alerts turned off, route.ts:60-66 and 82; or the sweep after 355 days). -/
inductive Page
  | quiet
  | saw (t : ℕ)
  | save
  | drop
  | wipeRec

def Page.apply : Page → RS → RS
  | .quiet, s => s
  | .saw t, s =>
    ⟨some (match s.file with
      | some f => ⟨some (f.hit.getD t), none, 0⟩
      | none => ⟨some t, none, 0⟩), s.record⟩
  | .save, s =>
    ⟨some (match s.file with
      | some f => ⟨f.hit, f.mark, 0⟩
      | none => ⟨none, none, 0⟩), s.record⟩
  | .drop, s => ⟨none, s.record⟩
  | .wipeRec, s => ⟨s.file, .absent⟩

/-- Whether a price was found and is at or above the step (`due`, alerts.ts:148-150; a price written as a plain decimal
is compared exactly). -/
def atOrAbove (p : Option Dec) (target : Dec) : Bool :=
  match p with
  | some q => atLeast q target
  | none => false

/-- A run: round `k` starts at `T k`, finds price `price k` and has luck `luck k`; after it, `page k` happens. -/
structure Run where
  T : ℕ → ℕ
  price : ℕ → Option Dec
  target : Dec
  luck : ℕ → Luck
  page : ℕ → Page
  s0 : RS

def Run.res (R : Run) (k : ℕ) (s : RS) : RS × Option Send :=
  roundR (R.T k) k (atOrAbove (R.price k) R.target) (R.luck k) s

/-- The state before round `k`. -/
def Run.before (R : Run) : ℕ → RS
  | 0 => R.s0
  | k + 1 => (R.page k).apply (R.res k (R.before k)).1

/-- Whether round `k` tried to send the step, and what the push service answered. -/
def Run.outcome (R : Run) (k : ℕ) : Option Send := (R.res k (R.before k)).2

lemma roundR_tries (now tok : ℕ) (b : Bool) (l : Luck) (s : RS) (r : Send)
    (h : (roundR now tok b l s).2 = some r) : b = true := by
  by_contra g
  simp only [Bool.not_eq_true] at g
  subst g
  unfold roundR at h
  split at h <;> simp at h

/-- **Only at or above the step.** If round `k` tries to send the step, it found a price `p` and `atLeast p target`
held; when both are written as plain decimals, that is exactly `target ≤ p`. -/
theorem tries_only_at_or_above (R : Run) (k : ℕ) (h : R.outcome k ≠ none) :
    ∃ p, R.price k = some p ∧ atLeast p R.target = true ∧ (p.Plain → R.target.Plain → R.target.val ≤ p.val) := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
  have hb := roundR_tries _ _ _ _ _ r hr
  unfold atOrAbove at hb
  split at hb
  · rename_i q hq
    exact ⟨q, hq, hb, fun hp ht => (atLeast_iff q R.target hp ht).1 hb⟩
  · cases hb

/-- Nothing in the step's part of the file stops round `n` (at `Tn`): not reached, or marked by a round that started
more than `TAKEOVER_MS` before `Tn`. -/
def FileOK (Tn : ℕ) (f : Mark) : Prop := ∀ h, f.hit = some h → ∃ k, f.mark = some (h, k) ∧ h + takeoverMs < Tn

/-- Nothing in the record stops round `n`: none, or "sending" from a round that started more than `TAKEOVER_MS`
before `Tn`. -/
def RecOK (Tn : ℕ) (r : Rec) : Prop := r = .absent ∨ ∃ since k, r = .sending since k ∧ since + takeoverMs < Tn

def Ready (Tn : ℕ) (s : RS) : Prop := (∀ f, s.file = some f → FileOK Tn f) ∧ RecOK Tn s.record

lemma fileOK_markBy (Tn now tok : ℕ) (f : Mark) (h : now + takeoverMs < Tn) : FileOK Tn (f.markBy now tok) := by
  intro x hx
  simp only [Mark.markBy, Option.some.injEq] at hx
  subst hx
  exact ⟨tok, rfl, h⟩

lemma fileOK_markBy_unmark (Tn now tok : ℕ) (f : Mark) : FileOK Tn ((f.markBy now tok).unmark tok) := by
  intro x hx
  simp [Mark.markBy, Mark.unmark] at hx

lemma fileOK_unmark (Tn tok : ℕ) (f : Mark) (hf : FileOK Tn f) : FileOK Tn (f.unmark tok) := by
  unfold Mark.unmark
  split
  · rename_i t0 k hm
    split_ifs with hk hh
    · intro x hx; cases hx
    · intro x hx
      dsimp only at hx
      obtain ⟨k', hk', _⟩ := hf x hx
      rw [hm] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact absurd (by rw [hk'.1]; exact hx) hh
    · exact hf
  · exact hf

lemma claim_ready (Tn : ℕ) (r : Rec) (tok now : ℕ) (hr : RecOK Tn r) :
    (claim r tok now).1 ≠ .sent ∧ ((claim r tok now).2 = r ∨ (claim r tok now).2 = .sending now tok) := by
  rcases hr with rfl | ⟨since, k, rfl, _⟩
  · simp [claim]
  · simp only [claim]
    split_ifs <;> simp

lemma ready_round (Tn now tok : ℕ) (b : Bool) (l : Luck) (s : RS) (hs : Ready Tn s)
    (hok : (roundR now tok b l s).2 ≠ some .ok) (hl : l.land ∨ now + takeoverMs < Tn) :
    Ready Tn (roundR now tok b l s).1 := by
  obtain ⟨hf, hr⟩ := hs
  obtain ⟨hc1, hc2⟩ := claim_ready Tn s.record tok now hr
  have hc2' : now + takeoverMs < Tn → RecOK Tn (claim s.record tok now).2 := by
    intro hn
    rcases hc2 with h | h
    · rw [h]; exact hr
    · rw [h]; exact Or.inr ⟨now, tok, rfl, hn⟩
  unfold roundR at hok ⊢
  rcases hfile : s.file with _ | f
  · exact ⟨hf, hr⟩
  have hff := hf f hfile
  simp only [hfile] at hok ⊢
  by_cases g : (l.reached && f.toSend now && b) = true
  swap
  · rw [if_neg g]; exact ⟨fun f' h' => hf f' (hfile ▸ h'), hr⟩
  rw [if_pos g] at hok ⊢
  by_cases hland : l.land
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hland
    simp only [h1, h2, h3, h4, h5, h6, h7, Write.thrown, Write.landed, wr, if_true, if_false,
      Bool.false_eq_true] at hok ⊢
    rcases hcl : (claim s.record tok now).1 with _ | _ | _
    · simp only [hcl] at hok ⊢
      rcases hsd : l.send with _ | _ | _
      · simp only [hsd] at hok; exact absurd rfl hok
      · simp only
        split_ifs
        · exact ⟨by simp, Or.inl rfl⟩
        · refine ⟨?_, Or.inl rfl⟩
          intro f' h'
          simp only [Option.some.injEq] at h'
          subst h'
          exact fileOK_markBy_unmark Tn now tok f
      · exact ⟨by simp, Or.inl rfl⟩
    · refine ⟨?_, hr⟩
      intro f' h'
      simp only [Option.some.injEq] at h'
      subst h'
      exact fileOK_markBy_unmark Tn now tok f
    · exact absurd hcl hc1
  · have hn := hl.resolve_left hland
    have hm := fileOK_markBy Tn now tok f hn
    have hmu := fileOK_markBy_unmark Tn now tok f
    have hfu := fileOK_unmark Tn tok f hff
    have hca := hc2' hn
    by_cases hmt : l.mark.thrown = true
    · rw [if_pos hmt]
      refine ⟨?_, hr⟩
      intro f' h'; simp only [Option.some.injEq] at h'; subst h'
      split_ifs <;> (unfold wr; split_ifs <;> assumption)
    rw [if_neg hmt] at hok ⊢
    by_cases hct : l.claim.thrown = true
    · rw [if_pos hct]
      refine ⟨?_, ?_⟩
      · intro f' h'; simp only [Option.some.injEq] at h'; subst h'
        unfold wr; split_ifs <;> assumption
      · unfold wr; split_ifs <;> assumption
    rw [if_neg hct] at hok ⊢
    rcases hcl : (claim s.record tok now).1 with _ | _ | _
    · simp only [hcl] at hok ⊢
      rcases hsd : l.send with _ | _ | _
      · simp only [hsd] at hok; exact absurd rfl hok
      · simp only
        by_cases hft : l.fileW.thrown = true
        · rw [if_pos hft]
          refine ⟨?_, hca⟩
          intro f' h'; simp only [Option.some.injEq] at h'; subst h'
          unfold wr; split_ifs
          · exact hmu
          · exact hm
        rw [if_neg hft]
        by_cases hdt : l.delRec.thrown = true
        · rw [if_pos hdt]
          refine ⟨?_, ?_⟩
          · intro f' h'; simp only [Option.some.injEq] at h'; subst h'; exact hmu
          · unfold wr; split_ifs
            · exact Or.inl rfl
            · exact hca
        rw [if_neg hdt]
        refine ⟨?_, Or.inl rfl⟩
        intro f' h'
        split_ifs at h'
        · unfold wr at h'
          split_ifs at h'
          simp only [Option.some.injEq] at h'; subst h'; exact hmu
        · simp only [Option.some.injEq] at h'; subst h'; exact hmu
      · simp only
        by_cases hdt : l.delRec.thrown = true
        · rw [if_pos hdt]
          refine ⟨?_, ?_⟩
          · intro f' h'; simp only [Option.some.injEq] at h'; subst h'; exact hm
          · unfold wr; split_ifs
            · exact Or.inl rfl
            · exact hca
        rw [if_neg hdt]
        refine ⟨?_, Or.inl rfl⟩
        intro f' h'
        unfold wr at h'
        split_ifs at h'
        simp only [Option.some.injEq] at h'; subst h'; exact hm
    · refine ⟨?_, hr⟩
      intro f' h'; simp only [Option.some.injEq] at h'; subst h'
      unfold wr; split_ifs <;> assumption
    · exact absurd hcl hc1

lemma ready_page (Tn : ℕ) (p : Page) (s : RS) (hp : ∀ t, p ≠ .saw t) (hs : Ready Tn s) : Ready Tn (p.apply s) := by
  obtain ⟨hf, hr⟩ := hs
  cases p with
  | quiet => exact ⟨hf, hr⟩
  | saw t => exact absurd rfl (hp t)
  | save =>
    refine ⟨?_, hr⟩
    intro f' h'
    simp only [Page.apply, Option.some.injEq] at h'
    subst h'
    rcases hfile : s.file with _ | f
    · intro x hx; cases hx
    · exact hf f hfile
  | drop => exact ⟨fun _ h => (by cases h), hr⟩
  | wipeRec => exact ⟨hf, Or.inl rfl⟩

lemma fileOK_toSend (Tn : ℕ) (f : Mark) (hf : FileOK Tn f) : f.toSend Tn = true := by
  unfold Mark.toSend
  rcases hh : f.hit with _ | h
  · rfl
  · obtain ⟨k, hm, hlt⟩ := hf h hh
    rw [hm]
    simp [hlt]

lemma claim_mine_ready (Tn tok : ℕ) (r : Rec) (hr : RecOK Tn r) : (claim r tok Tn).1 = .mine := by
  rcases hr with rfl | ⟨since, k, rfl, hlt⟩
  · rfl
  · simp only [claim]
    split_ifs <;> rfl

lemma ready_fire (Tn tok : ℕ) (l : Luck) (s : RS) (hs : Ready Tn s) (hfile : s.file ≠ none)
    (hreach : l.reached = true) (hm : l.mark = .ok) (hc : l.claim = .ok) (hsend : l.send = .ok) :
    (roundR Tn tok true l s).2 = some .ok := by
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hfile
  have hts := fileOK_toSend Tn f (hs.1 f hf)
  have hcm := claim_mine_ready Tn tok s.record hs.2
  unfold roundR
  simp only [hf, hreach, hts, hm, hc, Write.thrown, Bool.and_self, if_true, if_false, Bool.false_eq_true]
  rw [hcm]
  simp only [hsend]

/-- **A step reached is sent, despite writes that failed.** Round `n` tries to send the step and the push service
takes it (`is sent`), unless an earlier round already got an "ok" from the push service, or the open page saw the
step reached and showed its own notice. Hypotheses: the step starts not reached, with no record; every earlier round in
which some store write failed (a lost write, a write that landed and still threw, a failed delete, a thrown send's
clean-up) started more than `TAKEOVER_MS` (10 minutes) before round `n`; the address file is there when round `n`
starts (it wasn't deleted, or the page saved it again); and in round `n` the step is reached (the file read, the time
left), its price `p` is at or above the step (`atLeast`), its mark and claim writes land, and the push service answers
ok. Every other round may go any way: failed or thrown sends, lost or landed-with-error writes, failed deletes, the page
saving between rounds, the file deleted. -/
theorem sent_eventually (R : Run) (n : ℕ) (p : Dec)
    (h0 : ∀ f, R.s0.file = some f → f.hit = none) (hrec0 : R.s0.record = .absent)
    (hlate : ∀ k < n, ¬ (R.luck k).land → R.T k + takeoverMs < R.T n)
    (hfile : (R.before n).file ≠ none)
    (hreach : (R.luck n).reached = true) (hp : R.price n = some p) (hat : atLeast p R.target = true)
    (hm : (R.luck n).mark = .ok) (hc : (R.luck n).claim = .ok) (hsend : (R.luck n).send = .ok) :
    R.outcome n = some .ok ∨ ∃ k < n, R.outcome k = some .ok ∨ ∃ t, R.page k = .saw t := by
  have inv : ∀ k ≤ n, (∃ j < k, R.outcome j = some .ok ∨ ∃ t, R.page j = .saw t) ∨ Ready (R.T n) (R.before k) := by
    intro k
    induction k with
    | zero =>
      intro _
      right
      refine ⟨fun f hf x hx => ?_, Or.inl hrec0⟩
      rw [h0 f hf] at hx; cases hx
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨j, hj, hj'⟩ | hr
      · exact Or.inl ⟨j, by omega, hj'⟩
      by_cases hok : R.outcome k = some .ok
      · exact Or.inl ⟨k, by omega, Or.inl hok⟩
      by_cases hsaw : ∃ t, R.page k = .saw t
      · exact Or.inl ⟨k, by omega, Or.inr hsaw⟩
      right
      have hl : (R.luck k).land ∨ R.T k + takeoverMs < R.T n := by
        by_cases h : (R.luck k).land
        · exact Or.inl h
        · exact Or.inr (hlate k (by omega) h)
      have := ready_round (R.T n) (R.T k) k _ (R.luck k) (R.before k) hr hok hl
      exact ready_page (R.T n) (R.page k) _ (fun t ht => hsaw ⟨t, ht⟩) this
  rcases inv n le_rfl with ⟨j, hj, hj'⟩ | hr
  · exact Or.inr ⟨j, hj, hj'⟩
  · left
    have hb : atOrAbove (R.price n) R.target = true := by rw [hp]; exact hat
    unfold Run.outcome Run.res
    rw [hb]
    exact ready_fire (R.T n) n (R.luck n) (R.before n) hr hfile hreach hm hc hsend

lemma page_record (p : Page) (s : RS) (hp : p ≠ .wipeRec) : (p.apply s).record = s.record := by
  cases p <;> first | exact absurd rfl hp | rfl

lemma round_sent (now tok : ℕ) (b : Bool) (l : Luck) (s : RS) (k : Option ℕ) (hr : s.record = .sent k)
    (hk : k ≠ some tok) : (roundR now tok b l s).1.record = .sent k ∧ (roundR now tok b l s).2 = none := by
  have hc : claim s.record tok now = (.sent, s.record) := by rw [hr]; simp [claim, hk]
  unfold roundR
  rw [hc]
  split
  · exact ⟨hr, rfl⟩
  · split_ifs <;> simp [hr, wr]

/-- **A "sent" record means no further send.** If, before round `j`, the step's record says sent (by an earlier
round, or a record with no round code, which counts as sent), no round from `j` on tries to send the step, whatever the
prices, the store, the push service or the page do (the file deleted, saved again, the step seen), as long as the
record itself isn't deleted (the step removed, alerts turned off, the sweep after 355 days). -/
theorem no_try_after_sent_record (R : Run) (j : ℕ) (k : Option ℕ) (hrec : (R.before j).record = .sent k)
    (hk : ∀ i, j ≤ i → k ≠ some i) (hwipe : ∀ i, j ≤ i → R.page i ≠ .wipeRec) :
    ∀ i, j ≤ i → R.outcome i = none := by
  have hall : ∀ i, j ≤ i → (R.before i).record = .sent k := by
    intro i hi
    induction i with
    | zero => have : j = 0 := by omega
              subst this; exact hrec
    | succ i ih =>
      rcases Nat.lt_or_ge i j with h | h
      · have : j = i + 1 := by omega
        subst this; exact hrec
      · show ((R.page i).apply _).record = _
        rw [page_record _ _ (hwipe i h)]
        exact (round_sent _ _ _ _ _ k (ih h) (hk i h)).1
  intro i hi
  exact (round_sent _ _ _ _ _ k (hall i hi) (hk i hi)).2

lemma claim_mine_tok (r : Rec) (tok now : ℕ) (h : (claim r tok now).1 = .mine) : (claim r tok now).2.tok = some tok := by
  cases r with
  | absent => rfl
  | sending since k =>
    simp only [claim] at h ⊢
    split_ifs at h ⊢ with h1 h2 <;> simp_all [Rec.tok]
  | sent k =>
    simp only [claim] at h ⊢
    split_ifs at h ⊢ with h1
    simp_all [Rec.tok]

lemma round_ok_record (now tok : ℕ) (b : Bool) (l : Luck) (s : RS) (h : (roundR now tok b l s).2 = some .ok)
    (hw : l.sentW.landed = true) : (roundR now tok b l s).1.record = .sent (some tok) := by
  unfold roundR at h ⊢
  rcases hfile : s.file with _ | f
  · simp only [hfile] at h; simp at h
  simp only [hfile] at h ⊢
  by_cases g : (l.reached && f.toSend now && b) = true
  swap
  · rw [if_neg g] at h; simp at h
  rw [if_pos g] at h ⊢
  by_cases hmt : l.mark.thrown = true
  · rw [if_pos hmt] at h; simp at h
  rw [if_neg hmt] at h ⊢
  by_cases hct : l.claim.thrown = true
  · rw [if_pos hct] at h; simp at h
  rw [if_neg hct] at h ⊢
  rcases hcl : (claim s.record tok now).1 with _ | _ | _
  · simp only [hcl] at h ⊢
    rcases hsd : l.send with _ | _ | _
    · simp [wr, hw, claim_mine_tok _ _ _ hcl]
    · simp only [hsd] at h; split_ifs at h <;> simp at h
    · simp only [hsd] at h; split_ifs at h <;> simp at h
  · simp only [hcl] at h; simp at h
  · simp only [hcl] at h; simp at h

/-- **Re-arming doesn't send again.** If round `k`'s send was taken by the push service and its "sent" write landed, no
later round tries to send the step, whatever happens to the address file after (deleted after 30 days unsynced, after
failed sends, a new push address, and the page saving the same step again) and whatever the store and push service do,
as long as the step's record isn't deleted (the step removed, alerts turned off, the sweep after 355 days). -/
theorem no_resend_after_rearm (R : Run) (k : ℕ) (hok : R.outcome k = some .ok)
    (hw : (R.luck k).sentW.landed = true) (hwipe : ∀ i, k ≤ i → R.page i ≠ .wipeRec) :
    ∀ i, k < i → R.outcome i = none := by
  have hrec : (R.before (k + 1)).record = .sent (some k) := by
    show ((R.page k).apply _).record = _
    rw [page_record _ _ (hwipe k le_rfl)]
    exact round_ok_record _ _ _ _ _ hok hw
  intro i hi
  exact no_try_after_sent_record R (k + 1) (some k) hrec (fun i hi h => by simp at h; omega)
    (fun i hi => hwipe i (by omega)) i hi

/-- **The exception, round by round** (alerts.ts:314-316): round 0 sends and the push service takes it, then the
round crashes before its "sent" write and its file write land; round 1, 11 minutes later, takes the step over and sends
it again, and the push service takes that too. -/
theorem resent_after_crash :
    ∃ R : Run, R.outcome 0 = some .ok ∧ R.outcome 1 = some .ok ∧ R.T 1 = R.T 0 + 660000 := by
  let ok : Luck := ⟨true, .ok, .ok, .ok, .ok, .ok, .ok, .ok, .ok⟩
  let crash : Luck := { ok with sentW := .lost, fileW := .lost }
  refine ⟨⟨fun k => k * 660000, fun _ => some ⟨[2], []⟩, ⟨[1], []⟩, fun k => if k = 0 then crash else ok,
    fun _ => .quiet, ⟨some ⟨none, none, 0⟩, .absent⟩⟩, ?_, ?_, ?_⟩ <;> decide

end Kanon.Alerts
