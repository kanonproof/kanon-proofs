import Mathlib.Tactic

/-!
# Spain: crypto gains of a resident person in the Renta (Modelo 100), arts. 33, 46, 48, 49, 66 and 76 LIRPF

The app (kanon-app branch `claude/spain-32` at 9a497c3, with the ledger fix of 268c7fa): the ledger
`src/lib/engine/lots.ts` (`runLedger` with `"FIFO"` and scope `"universal"`, `rank`, `byFifo`, `Book.add`, `pickLots`), the Spanish engine `src/lib/engine/es.ts` (`esWash`,
`esSavings`, `esScale`, `esSavingsTax`, `esTaxOnSale`) and the box lines in `src/lib/report/es.ts`. Sources: LIRPF
arts. 33.5.e (a loss is not counted when the same goods are bought again "dentro del año siguiente a la fecha de
dicha transmisión", and counts when they are sold; the two-month and before-or-after rules of 33.5.f and 33.5.g are
for valores, not crypto), 46, 48, 49 (offsets and four years' carry-forward, 25% cross limit from 2018, 10/15/20%
in 2015-2017), 66 and 76 (savings scale, state plus regional);
AEAT Manual Renta 2024, ch. 11-12 (boxes 1800-1814, the ch. 12 Caso práctico); the AEAT savings-scale figures.

Modelled line for line, in exact fractions:

* ES-1: one pool per coin across all wallets, oldest lot first; a sale takes `min(left, lot.qty)` at
  `cost × take ÷ qty`; coins missing at a sale come in at cost 0; a move between own wallets is not a sale.
* ES-2: each entry's part for the year = proceeds − cost + loss put off, and 1814 − 1813 is the year's saldo less
  futures.
* ES-3: `esWash`, art. 33.5.e: each loss is matched to coins of the same coin bought again within the year after
  the sale (from the sale's day, after it where both places in the day are known, to the same day a year later;
  29 February + one year = 28 February); the part put off is `loss × got ÷ qty` and is counted when those coins are
  sold: put off = counted in its own year + counted later + still waiting, and the cent counts add up to the cents
  of what was put off past its year.
* ES-4: the released-loss lines: 1804 = 1806 − v ≥ 0, 1807 = 1808 = v, and 1808 ≤ 1807 on any entry; one key's
  entries depend only on that key's lines.
* ES-5: `esSavings`, art. 49: phase 1 (the year's negative saldo of one kind against the other, within the year's
  limit), phase 2 (earlier losses, own kind first then the other within the room left, oldest first), gone after
  four years, and a loss left waiting only when nothing more could be taken (art. 49.2, "cuantía máxima");
  conservation for one year and over many.
* ES-6: the scale: tax ≥ 0 and never falls as the base rises; the AEAT's figures 2,800 → 532, 130,000 → 28,780,
  the 2025 band edges, and the ch. 12 example.
* ES-7: `esTaxOnSale` = the year's tax with the sale less the tax without it, ≥ 0; with gains ≥ 0 and the
  losses waiting ≥ 0 the `max … 0` never bites (art. 49 is monotone in the gains saldo).

Where the model departs from the code:

* the book keeps only lots with coins left (the code keeps used-up lots at 0 coins, which no sale takes);
* crumbs: the code treats a shortfall at a sale or a move of at most `qty × CRUMB` (beyond the 40 digits decimal.js
  keeps) as no coins missing; the model has no such tolerance, and any shortfall is a lot at cost 0;
* `toQty` scaling: the code scales a wrap's slices by `toQty ÷` the coins taken and gives the last slice what is left,
  so they add up to `toQty` in 40 digits; the model scales every slice, the last too, which in exact fractions is the
  same amount; a `toQty` of 0 or less is not modelled (`wrapped` asks `0 < toQty`);
* the code's `++seq` is one counter for all coins and wallets, for roots and steps; `bought`, `sold` and `moved` ask
  only that a new root exceed every root in the pool, and `wrapped` that the new steps follow each other and exceed
  every step in the arriving pool (and a missing coins' root exceed its roots, taken before the steps), which the
  code's do;
* the code's step is absent for none; the model writes 0 for it (the code's steps, from `++seq`, are ≥ 1; `wrapped`
  asks its steps to exceed every step in the arriving pool, so a step of 0 arrives only in an empty pool);
* a slice the code moves or wraps gets a new id (`id~n`); the model keeps the lot's id, which with its day and `seq`
  is the place a sale reads;
* decimal.js computes at 40 significant digits; the model uses exact fractions;
* dates are the number yyyymmdd, which orders like the app's ISO strings;
* loss ids are taken as distinct (the app's event ids are);
* a sale's rows are taken summed into its line; the split of proceeds across several lots is not modelled;
* years before 2015 (no art. 49 cross rate) let the losses waiting pass through untouched;
* negative saldos of 2011-2014 (DT 7ª LIRPF, with their own offset rules) are treated as ordinary losses waiting;
  this has no effect on any year after their four-year carry ended (2018 at the latest);
* `W2` keeps the counts made in a loss's own year in a list (`same`) that the code only takes off `deferred`;
* the pending years are integers, and `YearOut` carries three fields more than the code's (`crossGp`, `crossRcm`,
  `made`) so the sums can be stated.

Out of scope (the app's and its tests'): reading the chains and exchanges, the euro prices, which events are sales,
the CSV and PDF output and the screens.

Found in review and fixed in kanon-app 268c7fa: `Book.add` used to put a lot moved between own wallets after the other
lots bought the same day, so a later FIFO sale picked a different same-day lot. Each lot now has its arrival order
(`rank`, here `seq`) and `byFifo` sorts by day, then arrival; `transfer_same_sale` proves a move no longer changes a
later sale, from any pool the ledger can reach (`Reach`: purchases, sales, moves, also after a move of part of a lot,
whose remainder and moved slice share one place, as in the code); `same_day_move` and `two_moves` check the case
found (two lots of one day at 100 and 200: a sale of one coin costs 100 before a move, after it, and after two moves
that each take half of the first lot). Found in the second review: a wrap (a move to another coin, `toAsset`, scaled
by `toQty`) gave its slices their lot's `seq`, so two wraps of one lot at different rates left two slices of one place
at different costs per coin, and a later move changed a later sale (2 coins for 200, wrapped 1 → 1 and 1 → 1/2: a
sale of one wrapped coin after a move cost 150, not 100). A new root for each wrapped slice would put a lot wrapped
and unwrapped the same day after the other lots of that day (A at 100 and B at 300: a sale would take B). The rule
modelled (kanon-app a4a0731, `claude/wrap-rank`, lots.ts:149-150, 201-202, 252-258) makes `seq` a root and a step, ordered
by day, then root, then step, no step first: a plain move keeps it, a move to another coin or with a `toQty` keeps the
root and takes a new step, in the order the slices are taken, and an unknown-cost lot gets a new root and no step;
`Reach.wrapped` models it, `transfer_same_sale` covers pools reached through wraps, and `wrap_then_move` (100) and
`round_trip` (A stays first) check both cases.
-/

namespace Kanon.Spain

/-! ## 1. One pool per coin across all wallets, first in first out (`runLedger(events, "FIFO", "universal")`) -/

/-- A lot: its wallet, the day it was bought (yyyymmdd), how many coins are left and what they cost, and `seq` its
place in the order lots arrived (the code's `rank`), a root and a step (0 for none), compared root first: a purchase,
or the lot at cost 0 for coins missing at a sale or a move, gets a new root and no step; a slice moved between the
person's own wallets keeps the `seq` of the lot it came from; a slice moved to another coin, or with a `toQty`, keeps
its lot's root and gets a new step. -/
structure Lot where
  id : ℕ
  wallet : ℕ
  acquired : ℕ
  qty : ℚ
  cost : ℚ
  seq : ℕ × ℕ

/-- `runLedger`'s book key: the coin alone when the scope is universal (Spain), the coin and wallet otherwise. -/
inductive Scope
  | wallet
  | universal

def bookKey : Scope → ℕ → ℕ → ℕ × Option ℕ
  | .universal, asset, _ => (asset, none)
  | .wallet, asset, wallet => (asset, some wallet)

/-- **ES-1** With Spain's universal scope, a sale or purchase of a coin in any wallet uses the same book: the coin's
one pool. -/
theorem universal_one_pool (asset w w' : ℕ) : bookKey .universal asset w = bookKey .universal asset w' := rfl

/-- `byFifo(a, b) ≤ 0`: `a` was bought on an earlier day, or the same day and arrived no later. -/
abbrev before (a b : Lot) : Prop :=
  a.acquired < b.acquired ∨
    (a.acquired = b.acquired ∧ (a.seq.1 < b.seq.1 ∨ (a.seq.1 = b.seq.1 ∧ a.seq.2 ≤ b.seq.2)))

/-- `Book.add`: a lot goes after every lot `byFifo` puts no later than it (the code's push, or its binary search for
the first lot that sorts after it). -/
def add (l : Lot) : List Lot → List Lot
  | [] => [l]
  | x :: xs => if before x l then x :: add l xs else l :: x :: xs

/-- One slice a sale takes: the lot, how many coins and their cost (`basis`). -/
structure Pick where
  lot : Lot
  take : ℚ
  basis : ℚ

/-- `pickLots` (FIFO) and the slices' bookkeeping: oldest lot first, each taking `min(left, lot.qty)` at
`cost × take ÷ qty`; a lot used up leaves the book, a lot used in part keeps the rest of its coins and cost. -/
def sell : List Lot → ℚ → List Pick × List Lot
  | [], _ => ([], [])
  | l :: ls, q =>
    if q ≤ 0 then ([], l :: ls)
    else if q < l.qty then
      ([⟨l, q, l.cost * q / l.qty⟩], { l with qty := l.qty - q, cost := l.cost - l.cost * q / l.qty } :: ls)
    else
      ((⟨l, l.qty, l.cost * l.qty / l.qty⟩ :: (sell ls (q - l.qty)).1), (sell ls (q - l.qty)).2)

def held (ls : List Lot) : ℚ := (ls.map Lot.qty).sum
def totalCost (ls : List Lot) : ℚ := (ls.map Lot.cost).sum

/-- A sale with `unknownCost`: when the pool holds fewer coins than are sold, the missing ones are a lot bought that
day at cost 0 (`unknownLot`, with a new `seq`), then the sale runs. -/
def sale (ls : List Lot) (q : ℚ) (id wallet date seq : ℕ) : List Pick × List Lot :=
  if held ls < q then sell (add ⟨id, wallet, date, q - held ls, 0, (seq, 0)⟩ ls) q else sell ls q

theorem add_perm (l : Lot) (ls : List Lot) : (add l ls).Perm (l :: ls) := by
  induction ls with
  | nil => simp [add]
  | cons x xs ih =>
    unfold add; split_ifs
    · exact (ih.cons x).trans (List.Perm.swap l x xs)
    · exact List.Perm.refl _

theorem held_add (l : Lot) (ls : List Lot) : held (add l ls) = l.qty + held ls := by
  unfold held; rw [(add_perm l ls).map Lot.qty |>.sum_eq]; simp

theorem totalCost_add (l : Lot) (ls : List Lot) : totalCost (add l ls) = l.cost + totalCost ls := by
  unfold totalCost; rw [(add_perm l ls).map Lot.cost |>.sum_eq]; simp

/-- Oldest first: the book's lots in `byFifo` order (the day, then the order they arrived). -/
def Sorted (ls : List Lot) : Prop := ls.Pairwise before

theorem before_trans {a b c : Lot} (h1 : before a b) (h2 : before b c) : before a c := by
  unfold before at *; omega

theorem before_of_not {a b : Lot} (h : ¬ before a b) : before b a := by
  unfold before at *; omega

theorem before_antisymm {a b : Lot} (h1 : before a b) (h2 : before b a) :
    a.acquired = b.acquired ∧ a.seq = b.seq := by
  unfold before at *; exact ⟨by omega, Prod.ext (by omega) (by omega)⟩

theorem add_sorted (l : Lot) (ls : List Lot) (h : Sorted ls) : Sorted (add l ls) := by
  induction ls with
  | nil => simp [add, Sorted]
  | cons x xs ih =>
    unfold Sorted at h; rw [List.pairwise_cons] at h
    unfold add; split_ifs with hx
    · unfold Sorted; rw [List.pairwise_cons]
      refine ⟨fun y hy => ?_, ih h.2⟩
      rcases List.mem_cons.mp ((add_perm l xs).mem_iff.mp hy) with rfl | hy
      · exact hx
      · exact h.1 y hy
    · unfold Sorted; rw [List.pairwise_cons, List.pairwise_cons]
      have hl := before_of_not hx
      refine ⟨fun y hy => ?_, h.1, h.2⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hl
      · exact before_trans hl (h.1 y hy)

/-- **ES-1** Coins: a sale's slices and the coins left add up to the pool before. -/
theorem sell_qty (ls : List Lot) (q : ℚ) : ((sell ls q).1.map Pick.take).sum + held (sell ls q).2 = held ls := by
  induction ls generalizing q with
  | nil => simp [sell, held]
  | cons l ls ih =>
    unfold sell; split_ifs with h0 h1
    · simp
    · simp [held]; ring
    · have := ih (q - l.qty); simp [held] at this ⊢; linarith

/-- **ES-1** Cost: the cost of the coins sold and the cost left add up to the pool's cost before (every lot in the
pool holding coins, as the book's live lots do). -/
theorem sell_cost (ls : List Lot) (q : ℚ) (hq : ∀ l ∈ ls, 0 < l.qty) :
    ((sell ls q).1.map Pick.basis).sum + totalCost (sell ls q).2 = totalCost ls := by
  induction ls generalizing q with
  | nil => simp [sell, totalCost]
  | cons l ls ih =>
    unfold sell; split_ifs with h0 h1
    · simp
    · simp [totalCost]; ring
    · have := ih (q - l.qty) (fun x hx => hq x (by simp [hx]))
      have hl := hq l (by simp)
      simp [totalCost] at this ⊢
      rw [mul_div_assoc, div_self hl.ne', mul_one]; linarith

/-- **ES-1** A sale of no more than the pool holds sells exactly that many coins. -/
theorem sell_exact (ls : List Lot) (q : ℚ) (h0 : 0 ≤ q) (h : q ≤ held ls) :
    ((sell ls q).1.map Pick.take).sum = q := by
  induction ls generalizing q with
  | nil => simp [held] at h; simp [sell]; linarith
  | cons l ls ih =>
    unfold sell; split_ifs with ha hb
    · simp; linarith
    · simp
    · simp [held] at h
      have := ih (q - l.qty) (by linarith) (by simp [held]; linarith)
      simp [this]

/-- The lots a sale leaves were all in the pool before, with the same day. -/
theorem sell_left_days (ls : List Lot) (q : ℚ) :
    ∀ x ∈ (sell ls q).2, ∃ y ∈ ls, y.acquired = x.acquired := by
  induction ls generalizing q with
  | nil => simp [sell]
  | cons l ls ih =>
    unfold sell; split_ifs
    · intro x hx; exact ⟨x, hx, rfl⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨l, by simp, rfl⟩
      · exact ⟨x, by simp [hx], rfl⟩
    · intro x hx
      obtain ⟨y, hy, e⟩ := ih (q - l.qty) x hx
      exact ⟨y, by simp [hy], e⟩

/-- The lots a sale leaves were all in the pool before, with the same day and arrival order. -/
theorem sell_left_keys (ls : List Lot) (q : ℚ) :
    ∀ x ∈ (sell ls q).2, ∃ y ∈ ls, y.acquired = x.acquired ∧ y.seq = x.seq := by
  induction ls generalizing q with
  | nil => simp [sell]
  | cons l ls ih =>
    unfold sell; split_ifs
    · intro x hx; exact ⟨x, hx, rfl, rfl⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨l, by simp, rfl, rfl⟩
      · exact ⟨x, by simp [hx], rfl, rfl⟩
    · intro x hx
      obtain ⟨y, hy, e⟩ := ih (q - l.qty) x hx
      exact ⟨y, by simp [hy], e⟩

/-- **ES-1** First in first out: in a pool kept oldest first, every lot a sale takes from comes no later than every
lot it leaves, in the pool's order (by day, then arrival). -/
theorem sell_oldest (ls : List Lot) (q : ℚ) (h : Sorted ls) :
    ∀ p ∈ (sell ls q).1, ∀ x ∈ (sell ls q).2, before p.lot x := by
  induction ls generalizing q with
  | nil => simp [sell]
  | cons l ls ih =>
    unfold Sorted at h; rw [List.pairwise_cons] at h
    unfold sell; split_ifs
    · simp
    · intro p hp x hx
      simp at hp; subst hp
      rcases List.mem_cons.mp hx with rfl | hx
      · right; exact ⟨rfl, Or.inr ⟨rfl, le_refl _⟩⟩
      · exact h.1 x hx
    · intro p hp x hx
      rcases List.mem_cons.mp hp with rfl | hp
      · obtain ⟨y, hy, e1, e2⟩ := sell_left_keys ls (q - l.qty) x hx
        have := h.1 y hy; unfold before at this ⊢; rw [← e1, ← e2]; exact this
      · exact ih (q - l.qty) h.2 p hp x hx

/-- **ES-1** Newer lots untouched: a sale takes the first lots of the pool in order, and what it leaves is the rest
of the pool as it was, after at most one lot whose coins were partly sold. -/
theorem sell_prefix (ls : List Lot) (q : ℚ) :
    (sell ls q).1.map Pick.lot = ls.take (sell ls q).1.length ∧
      ((sell ls q).2 = ls.drop (sell ls q).1.length ∨
        ∃ l', (sell ls q).2 = l' :: ls.drop (sell ls q).1.length) := by
  induction ls generalizing q with
  | nil => simp [sell]
  | cons l ls ih =>
    unfold sell; split_ifs with h0 h1
    · simp
    · exact ⟨by simp, Or.inr ⟨_, rfl⟩⟩
    · obtain ⟨ih1, ih2⟩ := ih (q - l.qty)
      refine ⟨by simp [ih1], ?_⟩
      rcases ih2 with e | ⟨l', e⟩
      · left; simpa using e
      · right; exact ⟨l', by simpa using e⟩

/-- A sale of at least what the pool holds takes every lot, for their whole cost, and leaves nothing. -/
theorem sell_all (ls : List Lot) (q : ℚ) (hq : ∀ l ∈ ls, 0 < l.qty) (h : held ls ≤ q) :
    (sell ls q).2 = [] ∧ ((sell ls q).1.map Pick.basis).sum = totalCost ls := by
  have hc := sell_cost ls q hq
  suffices e : (sell ls q).2 = [] by refine ⟨e, ?_⟩; rw [e] at hc; simpa [totalCost] using hc
  induction ls generalizing q with
  | nil => simp [sell]
  | cons l ls ih =>
    have hl := hq l (by simp)
    have hr : 0 ≤ held ls := List.sum_nonneg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact (hq y (by simp [hy])).le)
    simp [held] at h
    unfold sell
    rw [if_neg (by unfold held at hr; linarith), if_neg (by unfold held at hr; linarith)]
    exact ih (q - l.qty) (fun x hx => hq x (by simp [hx])) (by unfold held at hr ⊢; linarith)
      (sell_cost ls _ (fun x hx => hq x (by simp [hx])))

/-- **ES-1** A sale of more coins than the pool holds takes the whole pool, plus the missing coins at cost 0. -/
theorem sale_short (ls : List Lot) (q : ℚ) (id w date seq : ℕ) (hq : ∀ l ∈ ls, 0 < l.qty) (h : held ls < q) :
    ((sale ls q id w date seq).1.map Pick.take).sum = q ∧
      ((sale ls q id w date seq).1.map Pick.basis).sum = totalCost ls ∧ (sale ls q id w date seq).2 = [] := by
  unfold sale; rw [if_pos h]
  set L := add ⟨id, w, date, q - held ls, 0, (seq, 0)⟩ ls
  have hL : ∀ l ∈ L, 0 < l.qty := fun l hl => by
    rcases List.mem_cons.mp ((add_perm _ ls).mem_iff.mp hl) with rfl | hl
    · simp; linarith
    · exact hq l hl
  have hh : held L = q := by simp [L, held_add]
  obtain ⟨e, c⟩ := sell_all L q hL hh.le
  have hs := sell_qty L q
  rw [e, hh] at hs
  refine ⟨by simpa [held] using hs, by rw [c]; simp [L, totalCost_add], e⟩

/-- What a sale leaves is still oldest first. -/
theorem sell_sorted (ls : List Lot) (q : ℚ) (h : Sorted ls) : Sorted (sell ls q).2 := by
  induction ls generalizing q with
  | nil => simp [sell, Sorted]
  | cons l ls ih =>
    have h' := h
    unfold Sorted at h; rw [List.pairwise_cons] at h
    unfold sell; split_ifs
    · exact h'
    · unfold Sorted; rw [List.pairwise_cons]; exact ⟨fun y hy => h.1 y hy, h.2⟩
    · exact ih (q - l.qty) h.2

/-- A move between the person's own wallets of one coin (no `toAsset`, or the same coin with no `toQty`): with one pool per coin, the oldest coins of
the pool move; each slice comes back into the same pool with its day, cost and `seq` (`moved.forEach((l) => add(l, source.get(l)))`). -/
def transfer (ls : List Lot) (q : ℚ) (dest : ℕ) : List Lot :=
  (sell ls q).1.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) (sell ls q).2

theorem foldl_add_held (dest : ℕ) (ps : List Pick) (b : List Lot) :
    held (ps.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) b) =
      held b + (ps.map Pick.take).sum := by
  induction ps generalizing b with
  | nil => simp
  | cons p ps ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih, held_add]; ring

theorem foldl_add_cost (dest : ℕ) (ps : List Pick) (b : List Lot) :
    totalCost (ps.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) b) =
      totalCost b + (ps.map Pick.basis).sum := by
  induction ps generalizing b with
  | nil => simp
  | cons p ps ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih, totalCost_add]; ring

theorem foldl_add_sorted (dest : ℕ) (ps : List Pick) (b : List Lot) (h : Sorted b) :
    Sorted (ps.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) b) := by
  induction ps generalizing b with
  | nil => simpa
  | cons p ps ih => exact ih _ (add_sorted _ _ h)

/-- **ES-1** A move between the person's own wallets is not a sale: the coin's pool keeps every coin and every cent
of cost, and stays oldest first. -/
theorem transfer_keeps (ls : List Lot) (q : ℚ) (dest : ℕ) (hq : ∀ l ∈ ls, 0 < l.qty) (h : Sorted ls) :
    held (transfer ls q dest) = held ls ∧ totalCost (transfer ls q dest) = totalCost ls ∧ Sorted (transfer ls q dest) := by
  have hs : Sorted (sell ls q).2 := sell_sorted ls q h
  refine ⟨?_, ?_, foldl_add_sorted _ _ _ hs⟩
  · unfold transfer; rw [foldl_add_held]; linarith [sell_qty ls q]
  · unfold transfer; rw [foldl_add_cost]; linarith [sell_cost ls q hq]

/-- A move of more coins than the wallet holds, with `unknownCost`: every lot moves, and the missing coins arrive in
the destination as a lot bought that day at cost 0 with a new `seq` (`unknownLot`, its slice added last). -/
def move (ls : List Lot) (q : ℚ) (id dest date seq : ℕ) : List Lot :=
  if held ls < q then add ⟨id, dest, date, q - held ls, 0, (seq, 0)⟩ (transfer ls q dest) else transfer ls q dest

/-- **ES-1** A move with missing coins adds just those coins, at cost 0; the pool stays oldest first. -/
theorem move_keeps (ls : List Lot) (q : ℚ) (id dest date seq : ℕ) (hq : ∀ l ∈ ls, 0 < l.qty) (h : Sorted ls) :
    held (move ls q id dest date seq) = max (held ls) q ∧ totalCost (move ls q id dest date seq) = totalCost ls ∧
      Sorted (move ls q id dest date seq) := by
  obtain ⟨h1, h2, h3⟩ := transfer_keeps ls q dest hq h
  unfold move; split_ifs with hl
  · refine ⟨?_, ?_, add_sorted _ _ h3⟩
    · rw [held_add, h1, max_eq_right hl.le]; ring
    · rw [totalCost_add, h2]; simp
  · exact ⟨by rw [h1, max_eq_left (not_lt.mp hl)], h2, h3⟩

/-- A lot's place, whatever wallet holds it: its id, its day and its `seq`. A slice moved between the person's own
wallets keeps all three. -/
def key (l : Lot) : ℕ × ℕ × (ℕ × ℕ) := (l.id, l.acquired, l.seq)

/-- The coins a sale takes from the lot with place `k`, and their cost. -/
def takeAt (k : ℕ × ℕ × (ℕ × ℕ)) (ps : List Pick) : ℚ := ((ps.filter (fun p => key p.lot = k)).map Pick.take).sum
def basisAt (k : ℕ × ℕ × (ℕ × ℕ)) (ps : List Pick) : ℚ := ((ps.filter (fun p => key p.lot = k)).map Pick.basis).sum

theorem takeAt_cons (k : ℕ × ℕ × (ℕ × ℕ)) (p : Pick) (ps : List Pick) :
    takeAt k (p :: ps) = (if key p.lot = k then p.take else 0) + takeAt k ps := by
  unfold takeAt; rw [List.filter_cons]; split_ifs <;> simp_all

theorem basisAt_cons (k : ℕ × ℕ × (ℕ × ℕ)) (p : Pick) (ps : List Pick) :
    basisAt k (p :: ps) = (if key p.lot = k then p.basis else 0) + basisAt k ps := by
  unfold basisAt; rw [List.filter_cons]; split_ifs <;> simp_all

theorem sell_le (l : Lot) (ls : List Lot) (q : ℚ) (h : q ≤ 0) : sell (l :: ls) q = ([], l :: ls) := by
  simp [sell, h]

theorem sell_lt (l : Lot) (ls : List Lot) (q : ℚ) (h0 : ¬ q ≤ 0) (h : q < l.qty) :
    sell (l :: ls) q =
      ([⟨l, q, l.cost * q / l.qty⟩], { l with qty := l.qty - q, cost := l.cost - l.cost * q / l.qty } :: ls) := by
  simp [sell, h0, h]

theorem sell_ge (l : Lot) (ls : List Lot) (q : ℚ) (h0 : ¬ q ≤ 0) (h : ¬ q < l.qty) :
    sell (l :: ls) q = ((⟨l, l.qty, l.cost * l.qty / l.qty⟩ :: (sell ls (q - l.qty)).1), (sell ls (q - l.qty)).2) := by
  simp [sell, h0, h]

/-- Two pools a later sale cannot tell apart: a sale of any amount takes the same total cost from each, and the same
coins and cost from each lot place. -/
def Out (L M : List Lot) : Prop :=
  ∀ r, ((sell L r).1.map Pick.basis).sum = ((sell M r).1.map Pick.basis).sum ∧
    ∀ k, takeAt k (sell L r).1 = takeAt k (sell M r).1 ∧ basisAt k (sell L r).1 = basisAt k (sell M r).1

theorem out_refl (L : List Lot) : Out L L := fun _ => ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem out_symm {L M : List Lot} (h : Out L M) : Out M L := fun r =>
  ⟨(h r).1.symm, fun k => ⟨((h r).2 k).1.symm, ((h r).2 k).2.symm⟩⟩

theorem out_trans {L M N : List Lot} (h1 : Out L M) (h2 : Out M N) : Out L N := fun r =>
  ⟨(h1 r).1.trans (h2 r).1, fun k => ⟨((h1 r).2 k).1.trans ((h2 r).2 k).1, ((h1 r).2 k).2.trans ((h2 r).2 k).2⟩⟩

/-- The same first lot (in any wallet) in front of two such pools. -/
theorem out_cons (x y : Lot) (L M : List Lot) (hk : key y = key x) (hq : y.qty = x.qty) (hc : y.cost = x.cost)
    (h : Out L M) : Out (x :: L) (y :: M) := by
  intro r
  by_cases r0 : r ≤ 0
  · rw [sell_le _ _ _ r0, sell_le _ _ _ r0]; simp
  by_cases r1 : r < x.qty
  · rw [sell_lt _ _ _ r0 r1, sell_lt _ _ _ r0 (by rwa [hq])]
    refine ⟨by simp [hq, hc], fun k => ?_⟩
    simp only [takeAt_cons, basisAt_cons, hk, hq, hc]; constructor <;> first | trivial | rfl
  · rw [sell_ge _ _ _ r0 r1, sell_ge _ _ _ r0 (by rwa [hq])]
    obtain ⟨i1, i2⟩ := h (r - x.qty)
    refine ⟨by simp [hq, hc, i1], fun k => ?_⟩
    simp only [takeAt_cons, basisAt_cons, hk, hq, hc, (i2 k).1, (i2 k).2]; constructor <;> first | trivial | rfl

/-- A first lot split into two slices of its place, whose coins and cost add up to it, at its cost per coin. -/
theorem out_split (x a b : Lot) (L M : List Lot) (hka : key a = key x) (hkb : key b = key x) (ha : 0 < a.qty)
    (hb : 0 < b.qty) (hq : a.qty + b.qty = x.qty) (hc : a.cost * x.qty = x.cost * a.qty)
    (hs : a.cost + b.cost = x.cost) (h : Out L M) : Out (x :: L) (a :: b :: M) := by
  intro r
  have hx : 0 < x.qty := by linarith
  have ea : a.cost = x.cost * a.qty / x.qty := by rw [eq_div_iff hx.ne']; linarith
  have eb : b.cost = x.cost * b.qty / x.qty := by
    rw [eq_div_iff hx.ne', show b.qty = x.qty - a.qty by linarith, show b.cost = x.cost - a.cost by linarith]
    linear_combination -hc
  have fa : a.cost * a.qty / a.qty = a.cost := by field_simp
  have fb : b.cost * b.qty / b.qty = b.cost := by field_simp
  have fx : x.cost * x.qty / x.qty = x.cost := by field_simp
  by_cases r0 : r ≤ 0
  · rw [sell_le _ _ _ r0, sell_le _ _ _ r0]; simp
  by_cases r1 : r < a.qty
  · have r2 : r < x.qty := by linarith
    rw [sell_lt _ _ _ r0 r2, sell_lt _ _ _ r0 r1]
    have e : x.cost * r / x.qty = a.cost * r / a.qty := by rw [ea]; field_simp
    refine ⟨by simp [e], fun k => ?_⟩
    simp only [takeAt_cons, basisAt_cons, hka, e]; constructor <;> first | trivial | rfl
  rw [sell_ge _ _ _ r0 r1]
  by_cases r3 : r - a.qty ≤ 0
  · have r2 : r < x.qty := by linarith
    have ra : r = a.qty := by linarith
    rw [sell_lt _ _ _ r0 r2, sell_le _ _ _ r3]
    have e : x.cost * r / x.qty = a.cost := by rw [ea, ra]
    refine ⟨by simp [fa, e], fun k => ?_⟩
    simp only [takeAt_cons, basisAt_cons, hka, fa, e]; simp [takeAt, basisAt, ra]
  by_cases r2 : r < x.qty
  · have r4 : r - a.qty < b.qty := by linarith
    rw [sell_lt _ _ _ r0 r2, sell_lt _ _ _ r3 r4]
    have e : a.cost + b.cost * (r - a.qty) / b.qty = x.cost * r / x.qty := by
      rw [ea, eb]; field_simp; ring
    refine ⟨by simp [fa]; linarith, fun k => ?_⟩
    simp only [takeAt_cons, basisAt_cons, hka, hkb, fa]
    constructor
    · split_ifs <;> simp [takeAt]
    · split_ifs <;> simp [basisAt, ← e]
  · have r4 : ¬ r - a.qty < b.qty := by linarith
    have e : r - a.qty - b.qty = r - x.qty := by linarith
    rw [sell_ge _ _ _ r0 r2, sell_ge _ _ _ r3 r4, e]
    obtain ⟨i1, i2⟩ := h (r - x.qty)
    refine ⟨by simp [fa, fb, fx]; linarith, fun k => ?_⟩
    simp only [takeAt_cons, basisAt_cons, hka, hkb, fa, fb, fx, (i2 k).1, (i2 k).2]
    constructor
    · split_ifs <;> linarith
    · split_ifs <;> linarith

/-- The coins and the cost the pool holds at place `k`. -/
def heldAt (k : ℕ × ℕ × (ℕ × ℕ)) (L : List Lot) : ℚ := ((L.filter (fun l => key l = k)).map Lot.qty).sum
def costAt (k : ℕ × ℕ × (ℕ × ℕ)) (L : List Lot) : ℚ := ((L.filter (fun l => key l = k)).map Lot.cost).sum

theorem heldAt_cons (k : ℕ × ℕ × (ℕ × ℕ)) (l : Lot) (L : List Lot) :
    heldAt k (l :: L) = (if key l = k then l.qty else 0) + heldAt k L := by
  unfold heldAt; rw [List.filter_cons]; split_ifs <;> simp_all

theorem costAt_cons (k : ℕ × ℕ × (ℕ × ℕ)) (l : Lot) (L : List Lot) :
    costAt k (l :: L) = (if key l = k then l.cost else 0) + costAt k L := by
  unfold costAt; rw [List.filter_cons]; split_ifs <;> simp_all

theorem heldAt_add (k : ℕ × ℕ × (ℕ × ℕ)) (l : Lot) (L : List Lot) :
    heldAt k (add l L) = (if key l = k then l.qty else 0) + heldAt k L := by
  rw [← heldAt_cons]; unfold heldAt; exact (((add_perm l L).filter _).map _).sum_eq

theorem costAt_add (k : ℕ × ℕ × (ℕ × ℕ)) (l : Lot) (L : List Lot) :
    costAt k (add l L) = (if key l = k then l.cost else 0) + costAt k L := by
  rw [← costAt_cons]; unfold costAt; exact (((add_perm l L).filter _).map _).sum_eq

theorem heldAt_nonneg (k : ℕ × ℕ × (ℕ × ℕ)) (L : List Lot) (hq : ∀ x ∈ L, 0 < x.qty) : 0 ≤ heldAt k L := by
  induction L with
  | nil => simp [heldAt]
  | cons l L ih =>
    have := ih (fun x hx => hq x (by simp [hx])); have := hq l (by simp)
    rw [heldAt_cons]; split_ifs <;> linarith

theorem heldAt_pos (L : List Lot) (hq : ∀ x ∈ L, 0 < x.qty) {x : Lot} (hx : x ∈ L) : 0 < heldAt (key x) L := by
  induction L with
  | nil => simp at hx
  | cons l L ih =>
    have h1 := heldAt_nonneg (key x) L (fun y hy => hq y (by simp [hy]))
    rw [heldAt_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [if_pos rfl]; linarith [hq x (by simp)]
    · have := ih (fun y hy => hq y (by simp [hy])) hx
      split_ifs <;> linarith [hq l (by simp)]

theorem heldAt_exists {k : ℕ × ℕ × (ℕ × ℕ)} {L : List Lot} (h : 0 < heldAt k L) : ∃ y ∈ L, key y = k := by
  induction L with
  | nil => simp [heldAt] at h
  | cons l L ih =>
    by_cases e : key l = k
    · exact ⟨l, by simp, e⟩
    · rw [heldAt_cons, if_neg e, zero_add] at h
      obtain ⟨y, hy, e⟩ := ih h; exact ⟨y, by simp [hy], e⟩

/-- A place's cost is its coins at the cost per coin of any of its lots. -/
theorem costAt_unit (l : Lot) (L : List Lot)
    (h : ∀ a ∈ L, a.acquired = l.acquired → a.seq = l.seq → a.cost * l.qty = l.cost * a.qty) :
    costAt (key l) L * l.qty = l.cost * heldAt (key l) L := by
  induction L with
  | nil => simp [costAt, heldAt]
  | cons a L ih =>
    have ih' := ih (fun b hb => h b (by simp [hb]))
    rw [costAt_cons, heldAt_cons]
    split_ifs with e
    · simp only [key, Prod.mk.injEq] at e
      linear_combination h a (by simp) e.2.1 e.2.2 + ih'
    · simpa using ih'

/-- A pool as the ledger keeps it: oldest first, every lot holding coins, and lots sharing a day and arrival order
are slices of one lot (the same id and the same cost per coin). -/
def Kept (L : List Lot) : Prop :=
  Sorted L ∧ (∀ x ∈ L, 0 < x.qty) ∧
    ∀ a ∈ L, ∀ b ∈ L, a.acquired = b.acquired → a.seq = b.seq → a.id = b.id ∧ a.cost * b.qty = b.cost * a.qty

/-- `x` is a slice of a lot of `L`: the same id, day and arrival order, at the same cost per coin. -/
def Like (L : List Lot) (x : Lot) : Prop :=
  ∃ y ∈ L, y.id = x.id ∧ y.acquired = x.acquired ∧ y.seq = x.seq ∧ x.cost * y.qty = y.cost * x.qty

theorem like_self {L : List Lot} {x : Lot} (hx : x ∈ L) : Like L x := ⟨x, hx, rfl, rfl, rfl, rfl⟩

theorem like_good {L M : List Lot} (hL : Kept L) (hs : Sorted M) (hq : ∀ x ∈ M, 0 < x.qty)
    (hl : ∀ x ∈ M, Like L x) : Kept M := by
  refine ⟨hs, hq, fun a ha b hb e1 e2 => ?_⟩
  obtain ⟨ya, hya, i1, a1, s1, c1⟩ := hl a ha
  obtain ⟨yb, hyb, i2, a2, s2, c2⟩ := hl b hb
  obtain ⟨hi, hc⟩ := hL.2.2 ya hya yb hyb (by rw [a1, a2, e1]) (by rw [s1, s2, e2])
  refine ⟨by rw [← i1, ← i2, hi], ?_⟩
  have pa := hL.2.1 ya hya
  have pb := hL.2.1 yb hyb
  have : (a.cost * b.qty - b.cost * a.qty) * (ya.qty * yb.qty) = 0 := by
    linear_combination (b.qty * yb.qty) * c1 - (a.qty * ya.qty) * c2 + (a.qty * b.qty) * hc
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · nlinarith [mul_pos pa pb]

theorem good_tail {l : Lot} {L : List Lot} (h : Kept (l :: L)) : Kept L := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold Sorted at h1; rw [List.pairwise_cons] at h1
  exact ⟨h1.2, fun x hx => h2 x (by simp [hx]), fun a ha b hb => h3 a (by simp [ha]) b (by simp [hb])⟩

theorem head_before {m y : Lot} {M : List Lot} (h : Sorted (m :: M)) (hy : y ∈ m :: M) : before m y := by
  unfold Sorted at h; rw [List.pairwise_cons] at h
  rcases List.mem_cons.mp hy with rfl | hy
  · right; exact ⟨rfl, Or.inr ⟨rfl, le_refl _⟩⟩
  · exact h.1 y hy

/-- The first `q` coins of a lot, and the rest of it, at its cost per coin. -/
def cutOf (m : Lot) (q : ℚ) : Lot := { m with qty := q, cost := m.cost * q / m.qty }
def leftOf (m : Lot) (q : ℚ) : Lot := { m with qty := m.qty - q, cost := m.cost - m.cost * q / m.qty }

theorem data_step (l m : Lot) (L M : List Lot)
    (IH : ∀ L2 M2 : List Lot, L2.length + M2.length ≤ L.length + M.length + 1 → Kept L2 → Kept M2 →
      (∀ k, heldAt k L2 = heldAt k M2) → (∀ k, costAt k L2 = costAt k M2) → Out L2 M2)
    (hL : Kept (l :: L)) (hM : Kept (m :: M)) (hh : ∀ k, heldAt k (l :: L) = heldAt k (m :: M))
    (hc : ∀ k, costAt k (l :: L) = costAt k (m :: M)) (hk : key m = key l)
    (hu : l.cost * m.qty = m.cost * l.qty) (hlt : l.qty < m.qty) : Out (l :: L) (m :: M) := by
  have hl := hL.2.1 l (by simp)
  have hm := hM.2.1 m (by simp)
  have hcl : m.cost * l.qty / m.qty = l.cost := by rw [div_eq_iff hm.ne']; linarith
  have h1 : Out (m :: M) (cutOf m l.qty :: leftOf m l.qty :: M) :=
    out_split m _ _ M M rfl rfl hl (by simp only [leftOf]; linarith) (by simp only [cutOf, leftOf]; ring)
      (by simp only [cutOf]; field_simp) (by simp only [cutOf, leftOf]; ring) (out_refl M)
  have g2 : Kept (leftOf m l.qty :: M) := by
    have s := hM.1; unfold Sorted at s; rw [List.pairwise_cons] at s
    refine like_good hM ?_ ?_ ?_
    · unfold Sorted; rw [List.pairwise_cons]; exact ⟨fun y hy => s.1 y hy, s.2⟩
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · simp only [leftOf]; linarith
      · exact hM.2.1 x (by simp [hx])
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨m, by simp, rfl, rfl, rfl, by simp only [leftOf]; rw [hcl]; field_simp; linarith⟩
      · exact like_self (by simp [hx])
  have ek : key (leftOf m l.qty) = key l := hk
  have h2 : Out (l :: L) (cutOf m l.qty :: leftOf m l.qty :: M) := by
    refine out_cons l _ L _ hk rfl (by simp only [cutOf]; exact hcl) (IH L _ (by simp only [List.length_cons]; omega) (good_tail hL) g2 ?_ ?_)
    · intro k; have := hh k; rw [heldAt_cons, heldAt_cons, hk] at this; rw [heldAt_cons, ek]
      simp only [leftOf]; split_ifs at this ⊢ <;> linarith
    · intro k; have := hc k; rw [costAt_cons, costAt_cons, hk] at this; rw [costAt_cons, ek]
      simp only [leftOf]; rw [hcl]; split_ifs at this ⊢ <;> linarith
  exact out_trans h2 (out_symm h1)

/-- Two pools as the ledger keeps them, holding at each place the same coins at the same cost, cannot be told apart
by a later sale. -/
theorem data_out (n : ℕ) : ∀ L M : List Lot, L.length + M.length ≤ n → Kept L → Kept M →
    (∀ k, heldAt k L = heldAt k M) → (∀ k, costAt k L = costAt k M) → Out L M := by
  induction n with
  | zero =>
    intro L M hn _ _ _ _
    rw [List.eq_nil_of_length_eq_zero (by omega : L.length = 0),
      List.eq_nil_of_length_eq_zero (by omega : M.length = 0)]
    exact out_refl _
  | succ n ih =>
    intro L M hn hL hM hh hc
    rcases L with _ | ⟨l, L⟩ <;> rcases M with _ | ⟨m, M⟩
    · exact out_refl _
    · have := hh (key m); rw [show heldAt (key m) [] = 0 by simp [heldAt]] at this
      linarith [heldAt_pos _ hM.2.1 (show m ∈ m :: M by simp)]
    · have := hh (key l); rw [show heldAt (key l) [] = 0 by simp [heldAt]] at this
      linarith [heldAt_pos _ hL.2.1 (show l ∈ l :: L by simp)]
    · have hl := hL.2.1 l (by simp)
      have hm := hM.2.1 m (by simp)
      have pl : 0 < heldAt (key l) (m :: M) := by rw [← hh]; exact heldAt_pos _ hL.2.1 (by simp)
      have pm : 0 < heldAt (key m) (l :: L) := by rw [hh]; exact heldAt_pos _ hM.2.1 (by simp)
      obtain ⟨y, hy, ey⟩ := heldAt_exists pl
      obtain ⟨z, hz, ez⟩ := heldAt_exists pm
      have b1 := head_before hM.1 hy
      have b2 := head_before hL.1 hz
      simp only [key, Prod.mk.injEq] at ey ez
      obtain ⟨ey1, ey2, ey3⟩ := ey
      obtain ⟨ez1, ez2, ez3⟩ := ez
      have b1' : before m l := by unfold before at b1 ⊢; rw [← ey2, ← ey3]; exact b1
      have b2' : before l m := by unfold before at b2 ⊢; rw [← ez2, ← ez3]; exact b2
      obtain ⟨ea, es⟩ := before_antisymm b1' b2'
      have hk : key m = key l := by
        have := (hM.2.2 m (by simp) y hy (by rw [ea, ey2]) (by rw [es, ey3])).1
        simp only [key, Prod.mk.injEq]; exact ⟨by rw [this, ey1], ea, es⟩
      have u1 := costAt_unit l (l :: L) (fun a ha e1 e2 => (hL.2.2 a ha l (by simp) e1 e2).2)
      have u2 := costAt_unit m (m :: M) (fun a ha e1 e2 => (hM.2.2 a ha m (by simp) e1 e2).2)
      rw [hk, ← hh, ← hc] at u2
      have hu : l.cost * m.qty = m.cost * l.qty := by
        have hH := heldAt_pos _ hL.2.1 (show l ∈ l :: L by simp)
        have : (l.cost * m.qty - m.cost * l.qty) * heldAt (key l) (l :: L) = 0 := by
          linear_combination (-m.qty) * u1 + l.qty * u2
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
      simp only [List.length_cons] at hn
      rcases lt_trichotomy l.qty m.qty with h | h | h
      · exact data_step l m L M (fun L2 M2 h2 => ih L2 M2 (by omega)) hL hM hh hc hk hu h
      · have hcm : m.cost = l.cost := by
          have := hu; rw [h] at this; exact (mul_right_cancel₀ hm.ne' this).symm
        refine out_cons l m L M hk h.symm hcm (ih L M (by omega) (good_tail hL) (good_tail hM) ?_ ?_)
        · intro k; have := hh k; rw [heldAt_cons, heldAt_cons, hk, h] at this; linarith
        · intro k; have := hc k; rw [costAt_cons, costAt_cons, hk, hcm] at this; linarith
      · exact out_symm (data_step m l M L (fun L2 M2 h2 => ih L2 M2 (by omega)) hM hL (fun k => (hh k).symm)
          (fun k => (hc k).symm) hk.symm hu.symm h)

/-- What a sale takes from each place and what it leaves there add up to what the place held. -/
theorem sell_at (L : List Lot) (r : ℚ) (k : ℕ × ℕ × (ℕ × ℕ)) (hq : ∀ l ∈ L, 0 < l.qty) :
    takeAt k (sell L r).1 + heldAt k (sell L r).2 = heldAt k L ∧
      basisAt k (sell L r).1 + costAt k (sell L r).2 = costAt k L := by
  have t0 : takeAt k [] = 0 := by simp [takeAt]
  have b0 : basisAt k [] = 0 := by simp [basisAt]
  induction L generalizing r with
  | nil => simp [sell, t0, b0, heldAt, costAt]
  | cons l L ih =>
    have hl := hq l (by simp)
    by_cases r0 : r ≤ 0
    · rw [sell_le _ _ _ r0]; simp [t0, b0]
    by_cases r1 : r < l.qty
    · rw [sell_lt _ _ _ r0 r1]
      have e : key { l with qty := l.qty - r, cost := l.cost - l.cost * r / l.qty } = key l := rfl
      simp only [takeAt_cons, basisAt_cons, heldAt_cons, costAt_cons, e, t0, b0]
      constructor <;> split_ifs <;> ring
    · rw [sell_ge _ _ _ r0 r1]
      obtain ⟨i1, i2⟩ := ih (r - l.qty) (fun x hx => hq x (by simp [hx]))
      have fl : l.cost * l.qty / l.qty = l.cost := by field_simp
      simp only [takeAt_cons, basisAt_cons, heldAt_cons, costAt_cons, fl]
      constructor <;> split_ifs <;> linarith

/-- The lots a sale leaves hold coins and are slices of lots of the pool. -/
theorem sell_left_like (L : List Lot) (r : ℚ) (hq : ∀ l ∈ L, 0 < l.qty) :
    ∀ x ∈ (sell L r).2, Like L x ∧ 0 < x.qty := by
  induction L generalizing r with
  | nil => simp [sell]
  | cons l L ih =>
    have hl := hq l (by simp)
    by_cases r0 : r ≤ 0
    · rw [sell_le _ _ _ r0]; intro x hx; exact ⟨like_self hx, hq x hx⟩
    by_cases r1 : r < l.qty
    · rw [sell_lt _ _ _ r0 r1]; intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨⟨l, by simp, rfl, rfl, rfl, by dsimp only; rw [sub_mul, div_mul_cancel₀ _ hl.ne']; ring⟩,
          by dsimp only; linarith⟩
      · exact ⟨like_self (by simp [hx]), hq x (by simp [hx])⟩
    · rw [sell_ge _ _ _ r0 r1]; intro x hx
      obtain ⟨⟨y, hy, h1⟩, h2⟩ := ih (r - l.qty) (fun x hx => hq x (by simp [hx])) x hx
      exact ⟨⟨y, by simp [hy], h1⟩, h2⟩

/-- Each slice a sale takes comes from a lot of the pool, holds coins, and costs that lot's cost per coin. -/
theorem sell_picks (L : List Lot) (r : ℚ) (hq : ∀ l ∈ L, 0 < l.qty) :
    ∀ p ∈ (sell L r).1, p.lot ∈ L ∧ 0 < p.take ∧ p.basis = p.lot.cost * p.take / p.lot.qty := by
  induction L generalizing r with
  | nil => simp [sell]
  | cons l L ih =>
    have hl := hq l (by simp)
    by_cases r0 : r ≤ 0
    · rw [sell_le _ _ _ r0]; simp
    by_cases r1 : r < l.qty
    · rw [sell_lt _ _ _ r0 r1]; intro p hp; simp only [List.mem_singleton] at hp; subst hp
      exact ⟨by simp, not_le.mp r0, rfl⟩
    · rw [sell_ge _ _ _ r0 r1]; intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by simp, hl, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ih (r - l.qty) (fun x hx => hq x (by simp [hx])) p hp
        exact ⟨by simp [h1], h2, h3⟩

theorem mem_foldl (dest : ℕ) (ps : List Pick) (R : List Lot) :
    ∀ x ∈ ps.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) R,
      x ∈ R ∨ ∃ p ∈ ps, x = { p.lot with wallet := dest, qty := p.take, cost := p.basis } := by
  induction ps generalizing R with
  | nil => intro x hx; exact Or.inl hx
  | cons p ps ih =>
    intro x hx
    simp only [List.foldl_cons] at hx
    rcases ih _ x hx with h | ⟨p', hp', e⟩
    · rcases List.mem_cons.mp ((add_perm _ _).mem_iff.mp h) with e | h
      · exact Or.inr ⟨p, by simp, e⟩
      · exact Or.inl h
    · exact Or.inr ⟨p', by simp [hp'], e⟩

theorem foldl_at (dest : ℕ) (ps : List Pick) (R : List Lot) (k : ℕ × ℕ × (ℕ × ℕ)) :
    heldAt k (ps.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) R) =
        heldAt k R + takeAt k ps ∧
      costAt k (ps.foldl (fun b p => add { p.lot with wallet := dest, qty := p.take, cost := p.basis } b) R) =
        costAt k R + basisAt k ps := by
  induction ps generalizing R with
  | nil => simp [takeAt, basisAt]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    obtain ⟨i1, i2⟩ := ih (add { p.lot with wallet := dest, qty := p.take, cost := p.basis } R)
    have e : key { p.lot with wallet := dest, qty := p.take, cost := p.basis } = key p.lot := rfl
    rw [i1, i2, heldAt_add, costAt_add, takeAt_cons, basisAt_cons]
    simp only [e]
    constructor <;> ring

/-- A move between the person's own wallets keeps, at every place, the coins and their cost. -/
theorem transfer_at (L : List Lot) (q : ℚ) (dest : ℕ) (k : ℕ × ℕ × (ℕ × ℕ)) (hq : ∀ l ∈ L, 0 < l.qty) :
    heldAt k (transfer L q dest) = heldAt k L ∧ costAt k (transfer L q dest) = costAt k L := by
  obtain ⟨a1, a2⟩ := foldl_at dest (sell L q).1 (sell L q).2 k
  obtain ⟨b1, b2⟩ := sell_at L q k hq
  unfold transfer; rw [a1, a2]; constructor <;> linarith

theorem transfer_like (L : List Lot) (q : ℚ) (dest : ℕ) (hq : ∀ l ∈ L, 0 < l.qty) :
    ∀ x ∈ transfer L q dest, Like L x ∧ 0 < x.qty := by
  intro x hx; unfold transfer at hx
  rcases mem_foldl dest _ _ x hx with h | ⟨p, hp, rfl⟩
  · exact sell_left_like L q hq x h
  · obtain ⟨h1, h2, h3⟩ := sell_picks L q hq p hp
    have := hq _ h1
    exact ⟨⟨p.lot, h1, rfl, rfl, rfl, by dsimp only; rw [h3, div_mul_cancel₀ _ this.ne']⟩, h2⟩

theorem good_transfer {L : List Lot} (q : ℚ) (dest : ℕ) (h : Kept L) : Kept (transfer L q dest) :=
  like_good h (transfer_keeps L q dest h.2.1 h.1).2.2 (fun x hx => (transfer_like L q dest h.2.1 x hx).2)
    (fun x hx => (transfer_like L q dest h.2.1 x hx).1)

theorem good_sell {L : List Lot} (r : ℚ) (h : Kept L) : Kept (sell L r).2 :=
  like_good h (sell_sorted L r h.1) (fun x hx => (sell_left_like L r h.2.1 x hx).2)
    (fun x hx => (sell_left_like L r h.2.1 x hx).1)

theorem good_add {L : List Lot} {l : Lot} (h : Kept L) (hl : 0 < l.qty) (hf : ∀ x ∈ L, x.seq ≠ l.seq) :
    Kept (add l L) := by
  refine ⟨add_sorted l L h.1, fun x hx => ?_, fun a ha b hb e1 e2 => ?_⟩
  · rcases List.mem_cons.mp ((add_perm l L).mem_iff.mp hx) with rfl | hx
    · exact hl
    · exact h.2.1 x hx
  · rcases List.mem_cons.mp ((add_perm l L).mem_iff.mp ha) with ea | ma <;>
      rcases List.mem_cons.mp ((add_perm l L).mem_iff.mp hb) with eb | mb
    · subst ea eb; exact ⟨rfl, rfl⟩
    · subst ea; exact absurd e2.symm (hf b mb)
    · subst eb; exact absurd e2 (hf a ma)
    · exact h.2.2 a ma b mb e1 e2

/-- The slices a wrap (a move with `toAsset`) takes, in the order the code's `moved` holds them: the pool's lots
oldest first, then, for coins missing, the lot at cost 0 for them (`unknownLot`, bought that day, a new root `s`) last. -/
def wrapPicks (L : List Lot) (q : ℚ) (id w date s : ℕ) : List Pick :=
  if held L < q then (sell L q).1 ++ [⟨⟨id, w, date, q - held L, 0, (s, 0)⟩, q - held L, 0⟩] else (sell L q).1

/-- A slice's coins on arrival: as taken when the wrap has no `toQty`, else scaled by `toQty ÷` all coins taken. -/
def scaled (tq : Option ℚ) (all take : ℚ) : ℚ :=
  match tq with
  | none => take
  | some t => take * t / all

/-- The slices arriving from a move that names another coin or a `toQty`: each keeps its id, day and cost, its coins
are `scaled`, and its `seq` is its lot's root with a new step, the steps following each other in the order taken, from
`c`. -/
def wrapSlices : List Pick → ℕ → Option ℚ → ℚ → ℕ → List Lot
  | [], _, _, _, _ => []
  | p :: ps, dest, tq, all, c =>
    { p.lot with wallet := dest, qty := scaled tq all p.take, cost := p.basis, seq := (p.lot.seq.1, c) } ::
      wrapSlices ps dest tq all (c + 1)

/-- The arriving coin's pool `T` after a wrap of `q` coins from the pool `L` (kanon-app 3ed8522): the slices of the
pool's lots with their new steps from `c0`, then, for coins missing, the unknown-cost slice, which keeps its own new
root `s`; all scaled to what arrives. -/
def wrapIn (T L : List Lot) (q : ℚ) (id w date s dest : ℕ) (tq : Option ℚ) (c0 : ℕ) : List Lot :=
  (wrapSlices (sell L q).1 dest tq ((wrapPicks L q id w date s).map Pick.take).sum c0 ++
      (if held L < q then
        [(⟨id, dest, date, scaled tq ((wrapPicks L q id w date s).map Pick.take).sum (q - held L), 0, (s, 0)⟩ : Lot)]
      else [])).foldl (fun b l => add l b) T

theorem wrapSlices_mem (ps : List Pick) (dest : ℕ) (tq : Option ℚ) (all : ℚ) (c : ℕ) :
    ∀ x ∈ wrapSlices ps dest tq all c, ∃ p ∈ ps, ∃ n, c ≤ n ∧ x.seq = (p.lot.seq.1, n) ∧
      x.qty = scaled tq all p.take := by
  induction ps generalizing c with
  | nil => simp [wrapSlices]
  | cons p ps ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨p, by simp, c, le_refl _, rfl, rfl⟩
    · obtain ⟨q, hq, n, h1, e1, e2⟩ := ih (c + 1) x hx
      exact ⟨q, by simp [hq], n, by omega, e1, e2⟩

theorem wrapSlices_order (ps : List Pick) (dest : ℕ) (tq : Option ℚ) (all : ℚ) (c : ℕ) :
    (wrapSlices ps dest tq all c).Pairwise (fun a b => a.seq ≠ b.seq) := by
  induction ps generalizing c with
  | nil => simp [wrapSlices]
  | cons p ps ih =>
    simp only [wrapSlices, List.pairwise_cons]
    refine ⟨fun x hx e => ?_, ih (c + 1)⟩
    obtain ⟨q, -, n, h1, e1, -⟩ := wrapSlices_mem ps dest tq all (c + 1) x hx
    rw [e1] at e
    have := congrArg Prod.snd e
    simp at this; omega

/-- Lots arriving one after another, each with a `seq` larger than every one before, keep a pool as the ledger keeps
it. -/
theorem good_arrive (S : List Lot) : ∀ T : List Lot, Kept T → (∀ x ∈ S, 0 < x.qty) →
    S.Pairwise (fun a b => a.seq ≠ b.seq) → (∀ x ∈ T, ∀ y ∈ S, x.seq ≠ y.seq) →
    Kept (S.foldl (fun b l => add l b) T) := by
  induction S with
  | nil => intro T h _ _ _; exact h
  | cons y S ih =>
    intro T h hq hs hf
    rw [List.pairwise_cons] at hs
    simp only [List.foldl_cons]
    refine ih _ (good_add h (hq y (by simp)) (fun x hx => hf x hx y (by simp)))
      (fun x hx => hq x (by simp [hx])) hs.2 (fun x hx z hz => ?_)
    rcases List.mem_cons.mp ((add_perm y T).mem_iff.mp hx) with rfl | hx
    · exact hs.1 z hz
    · exact hf x hx z (by simp [hz])

/-- A wrap keeps the arriving pool as the ledger keeps it, when its new steps are larger than every step in that pool
and, for coins missing, the unknown-cost slice's new root `s` is larger than every root in that pool and taken before
those steps. -/
theorem good_wrap {L T : List Lot} (q : ℚ) (id w date s dest : ℕ) (tq : Option ℚ) (c0 : ℕ) (hL : Kept L)
    (hT : Kept T) (hc0 : ∀ x ∈ T, x.seq.2 < c0)
    (hs : held L < q → (∀ x ∈ T, x.seq.1 < s) ∧ s < c0) (hto : ∀ t, tq = some t → 0 < t) :
    Kept (wrapIn T L q id w date s dest tq c0) := by
  set ps := wrapPicks L q id w date s
  set all := (ps.map Pick.take).sum
  have hp : ∀ p ∈ ps, 0 < p.take := by
    simp only [ps]; unfold wrapPicks; split_ifs with hh
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (sell_picks L q hL.2.1 p hp).2.1
      · simp only [List.mem_singleton] at hp; subst hp; dsimp only; linarith
    · exact fun p hp => (sell_picks L q hL.2.1 p hp).2.1
  have hsc : ∀ p ∈ ps, 0 < scaled tq all p.take := by
    intro p hpm
    have h1 := hp p hpm
    cases tq with
    | none => exact h1
    | some t =>
      have h2 : p.take ≤ all :=
        List.single_le_sum (fun a ha => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact (hp b hb).le) _ (List.mem_map.mpr ⟨p, hpm, rfl⟩)
      exact div_pos (mul_pos h1 (hto t rfl)) (lt_of_lt_of_le h1 h2)
  have hsub : ∀ p ∈ (sell L q).1, p ∈ ps := by
    intro p hp; simp only [ps]; unfold wrapPicks; split_ifs <;> simp [hp]
  have hmiss : held L < q → (⟨⟨id, w, date, q - held L, 0, (s, 0)⟩, q - held L, 0⟩ : Pick) ∈ ps := by
    intro hh; simp only [ps]; unfold wrapPicks; rw [if_pos hh]; simp
  unfold wrapIn
  refine good_arrive _ T hT (fun x hx => ?_) ?_ (fun x hx y hy e => ?_)
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, hpm, n, -, -, e⟩ := wrapSlices_mem _ _ _ _ _ x hx
      rw [e]; exact hsc p (hsub p hpm)
    · split_ifs at hx with hh
      · simp only [List.mem_singleton] at hx; subst hx; exact hsc _ (hmiss hh)
      · simp at hx
  · rw [List.pairwise_append]
    refine ⟨wrapSlices_order _ _ _ _ _, by split_ifs <;> simp, fun a ha b hb e => ?_⟩
    split_ifs at hb with hh
    · simp only [List.mem_singleton] at hb; subst hb
      obtain ⟨p, -, n, hn, e1, -⟩ := wrapSlices_mem _ _ _ _ _ a ha
      have h1 := congrArg Prod.snd (e1.symm.trans e)
      simp at h1; have := (hs hh).2; omega
    · simp at hb
  · rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨p, -, n, hn, e1, -⟩ := wrapSlices_mem _ _ _ _ _ y hy
      have := hc0 x hx
      rw [e, e1] at this; simp at this; omega
    · split_ifs at hy with hh
      · simp only [List.mem_singleton] at hy; subst hy
        have := (hs hh).1 x hx
        rw [e] at this; simp at this
      · simp at hy

/-- The pools the ledger can reach: from empty, by purchases (each with a new root, larger than every one before),
sales (with `unknownCost`), moves between the person's own wallets, moves of more coins than held, and wraps. A move
with a `toAsset` of the same coin and no `toQty` is a plain move (`transferred`, `moved`). Any other wrap leaves its
pool as `sent` (the coins taken; the lot at cost 0 for coins missing never enters it) and arrives in the pool `T` of
the coin named (the same coin too, after `sent`) as `wrapped`: its slices in the order taken, coins `scaled`, each
with its lot's root and a new step, the steps one after another and larger than every step in `T`, and for coins
missing the unknown-cost slice last with its own new root `s`, taken before those steps. -/
inductive Reach : List Lot → Prop
  | empty : Reach []
  | bought (L : List Lot) (l : Lot) : Reach L → 0 < l.qty → (∀ x ∈ L, x.seq.1 < l.seq.1) → Reach (add l L)
  | sold (L : List Lot) (q : ℚ) (id w date seq : ℕ) : Reach L → (∀ x ∈ L, x.seq.1 < seq) →
      Reach (sale L q id w date seq).2
  | transferred (L : List Lot) (q : ℚ) (dest : ℕ) : Reach L → Reach (transfer L q dest)
  | moved (L : List Lot) (q : ℚ) (id dest date seq : ℕ) : Reach L → (∀ x ∈ L, x.seq.1 < seq) →
      Reach (move L q id dest date seq)
  | sent (L : List Lot) (q : ℚ) : Reach L → Reach (sell L q).2
  | wrapped (L T : List Lot) (q : ℚ) (id w date s dest : ℕ) (tq : Option ℚ) (c0 : ℕ) : Reach L → Reach T →
      (∀ x ∈ T, x.seq.2 < c0) → (held L < q → (∀ x ∈ T, x.seq.1 < s) ∧ s < c0) →
      (∀ t, tq = some t → 0 < t) → Reach (wrapIn T L q id w date s dest tq c0)

/-- Every pool the ledger can reach is oldest first, its lots hold coins, and lots sharing a day and arrival order
are slices of one lot at one cost per coin. -/
theorem good_of_reach {L : List Lot} (h : Reach L) : Kept L := by
  induction h with
  | empty => exact ⟨by simp [Sorted], by simp, by simp⟩
  | bought L l _ hl hf ih => exact good_add ih hl (fun x hx e => by have := hf x hx; rw [e] at this; omega)
  | sold L q id w date seq _ hf ih =>
    unfold sale; split_ifs with hs
    · exact good_sell q (good_add ih (show 0 < q - held L by linarith)
      (fun x hx e => by have := hf x hx; rw [e] at this; simp at this))
    · exact good_sell q ih
  | transferred L q dest _ ih => exact good_transfer q dest ih
  | moved L q id dest date seq _ hf ih =>
    unfold move; split_ifs with hs
    · refine good_add (good_transfer q dest ih) (show 0 < q - held L by linarith) (fun x hx => ?_)
      obtain ⟨⟨y, hy, _, _, e, _⟩, _⟩ := transfer_like L q dest ih.2.1 x hx
      intro e2; have := hf y hy; rw [e, e2] at this; simp at this
    · exact good_transfer q dest ih
  | sent L q _ ih => exact good_sell q ih
  | wrapped L T q id w date s dest tq c0 _ _ hc0 hs hto ihL ihT =>
    exact good_wrap q id w date s dest tq c0 ihL ihT hc0 hs hto

/-- **ES-1** A move between the person's own wallets does not change a later sale: from any pool the ledger can
reach (purchases, sales, moves, including after earlier moves of part of a lot), a sale of any amount after the move
takes the same coins from the same lots, at the same cost, as it would have before the move. -/
theorem transfer_same_sale (ls : List Lot) (q r : ℚ) (dest : ℕ) (h : Reach ls) :
    ((sell (transfer ls q dest) r).1.map Pick.basis).sum = ((sell ls r).1.map Pick.basis).sum ∧
      ∀ k, takeAt k (sell (transfer ls q dest) r).1 = takeAt k (sell ls r).1 ∧
        basisAt k (sell (transfer ls q dest) r).1 = basisAt k (sell ls r).1 := by
  have g := good_of_reach h
  exact data_out _ _ _ le_rfl (good_transfer q dest g) g (fun k => (transfer_at ls q dest k g.2.1).1)
    (fun k => (transfer_at ls q dest k g.2.1).2) r

/-- **ES-1** The same for a move of no more coins than the wallet holds, written as the code runs it. -/
theorem move_same_sale (ls : List Lot) (q r : ℚ) (id dest date seq : ℕ) (h : Reach ls) (hle : q ≤ held ls) :
    ((sell (move ls q id dest date seq) r).1.map Pick.basis).sum = ((sell ls r).1.map Pick.basis).sum ∧
      ∀ k, takeAt k (sell (move ls q id dest date seq) r).1 = takeAt k (sell ls r).1 ∧
        basisAt k (sell (move ls q id dest date seq) r).1 = basisAt k (sell ls r).1 := by
  unfold move; rw [if_neg (not_lt.mpr hle)]; exact transfer_same_sale ls q r dest h

/-- **ES-1** The case found in review: two lots bought the same day, the first for 100, the second for 200. A sale of
one coin costs 100, before a move of one coin between the person's own wallets and after it. -/
theorem same_day_move :
    let L : List Lot := [⟨1, 0, 20250101, 1, 100, (1, 0)⟩, ⟨2, 0, 20250101, 1, 200, (2, 0)⟩]
    ((sell L 1).1.map Pick.basis).sum = 100 ∧ ((sell (transfer L 1 7) 1).1.map Pick.basis).sum = 100 := by
  norm_num (config := { decide := true }) [sell, transfer, add, before]

/-- **ES-1** Two moves: the lots of 100 and 200 bought the same day; half of the first lot moves to another wallet,
then the other half moves to a third. A sale of one coin still takes the first lot and costs 100. -/
theorem two_moves :
    let L : List Lot := [⟨1, 0, 20250101, 1, 100, (1, 0)⟩, ⟨2, 0, 20250101, 1, 200, (2, 0)⟩]
    ((sell (transfer (transfer L (1 / 2) 7) (1 / 2) 8) 1).1.map Pick.basis).sum = 100 := by
  norm_num (config := { decide := true }) [sell, transfer, add, before]

/-- **ES-1** The wrap found in review: 2 coins bought for 200 (`seq` `(1, 0)`, a root and no step); one is wrapped into 1 coin of another
asset (its slice gets `(1, 2)`), then another into 1/2 coin (`(1, 3)`). A sale of one wrapped coin takes the first
slice and costs 100, before a move of one wrapped coin between the person's own wallets and after it. -/
theorem wrap_then_move :
    let L : List Lot := [⟨1, 0, 20250101, 2, 200, (1, 0)⟩]
    let W := wrapIn (wrapIn [] L 1 9 0 20250102 0 0 (some 1) 2) (sell L 1).2 1 9 0 20250103 0 0 (some (1 / 2)) 3
    Reach W ∧ ((sell W 1).1.map Pick.basis).sum = 100 ∧ ((sell (transfer W 1 7) 1).1.map Pick.basis).sum = 100 := by
  have r0 : Reach [⟨1, 0, 20250101, 2, 200, (1, 0)⟩] := by
    have := Reach.bought [] ⟨1, 0, 20250101, 2, 200, (1, 0)⟩ Reach.empty (by norm_num) (by simp)
    simpa [add] using this
  refine ⟨?_, ?_⟩
  · refine Reach.wrapped _ _ 1 9 0 20250103 0 0 (some (1 / 2)) 3 (Reach.sent _ 1 r0) ?_ ?_ ?_ (by simp)
    · exact Reach.wrapped _ [] 1 9 0 20250102 0 0 (some 1) 2 r0 Reach.empty (by simp)
        (by norm_num [held]) (by simp)
    · norm_num (config := { decide := true }) [wrapIn, wrapPicks, wrapSlices, scaled, held, sell, add]
    · norm_num [held, sell]
  · norm_num (config := { decide := true }) [wrapIn, wrapPicks, wrapSlices, scaled, held, sell, transfer, add, before]

/-- **ES-1** A round trip keeps a lot's place: lot A (1 coin for 100, `seq` `(1, 0)`) and lot B (1 coin
for 300, `(2, 0)`) are bought the same day; A is wrapped into another coin (`(1, 3)`) and back (`(1, 4)`, root 1
sorting before root 2). A sale of one coin still takes A and costs 100. -/
theorem round_trip :
    let L : List Lot := [⟨1, 0, 20250101, 1, 100, (1, 0)⟩, ⟨2, 0, 20250101, 1, 300, (2, 0)⟩]
    let E := wrapIn (sell L 1).2 (wrapIn [] L 1 9 0 20250102 0 0 none 3) 1 9 0 20250103 0 0 none 4
    Reach E ∧ (sell E 1).1.map (fun p => p.lot.id) = [1] ∧ ((sell E 1).1.map Pick.basis).sum = 100 := by
  have r0 : Reach [⟨1, 0, 20250101, 1, 100, (1, 0)⟩, ⟨2, 0, 20250101, 1, 300, (2, 0)⟩] := by
    have h1 := Reach.bought [] ⟨1, 0, 20250101, 1, 100, (1, 0)⟩ Reach.empty (by norm_num) (by simp)
    have h2 := Reach.bought _ ⟨2, 0, 20250101, 1, 300, (2, 0)⟩ h1 (by norm_num) (by simp [add])
    simpa [add, before] using h2
  refine ⟨?_, ?_⟩
  · refine Reach.wrapped _ _ 1 9 0 20250103 0 0 none 4 ?_ (Reach.sent _ 1 r0) ?_ ?_ (by simp)
    · exact Reach.wrapped _ [] 1 9 0 20250102 0 0 none 3 r0 Reach.empty (by simp) (by norm_num [held]) (by simp)
    · norm_num (config := { decide := true }) [held, sell]
    · norm_num [wrapIn, wrapPicks, wrapSlices, scaled, held, sell, add]
  · norm_num (config := { decide := true }) [wrapIn, wrapPicks, wrapSlices, scaled, held, sell, add, before]

/-- Under the old rule (a wrapped slice keeps its lot's `seq`), the two wraps give two slices of one place at
different costs per coin, and the sale after the move costs 150. -/
example :
    let W : List Lot := [⟨1, 0, 20250101, 1, 100, (1, 0)⟩, ⟨1, 0, 20250101, 1 / 2, 100, (1, 0)⟩]
    ((sell W 1).1.map Pick.basis).sum = 100 ∧ ((sell (transfer W 1 7) 1).1.map Pick.basis).sum = 150 := by
  norm_num (config := { decide := true }) [sell, transfer, add, before]

/-- Under the rule of a new root for every wrapped slice, the round trip puts A after B (`(4, 0)` after `(2, 0)`),
and the sale takes B at 300. -/
example :
    let E : List Lot := [⟨2, 0, 20250101, 1, 300, (2, 0)⟩, ⟨1, 0, 20250101, 1, 100, (4, 0)⟩]
    Sorted E ∧ ((sell E 1).1.map Pick.basis).sum = 300 := by
  norm_num (config := { decide := true }) [Sorted, sell, before]

/-! ## 2. Rounding to the cent (`cents`: Decimal's ROUND_HALF_UP, half away from zero) -/

def cents (x : ℚ) : ℚ := if 0 ≤ x then (⌊x * 100 + 1 / 2⌋ : ℚ) / 100 else -((⌊-x * 100 + 1 / 2⌋ : ℚ) / 100)

/-- A whole number of cents. -/
def IsCents (x : ℚ) : Prop := ∃ n : ℤ, x = n / 100

theorem cents_nonneg {x : ℚ} (h : 0 ≤ x) : 0 ≤ cents x := by
  unfold cents; rw [if_pos h]
  have : (0 : ℤ) ≤ ⌊x * 100 + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
  have : (0 : ℚ) ≤ (⌊x * 100 + 1 / 2⌋ : ℚ) := by exact_mod_cast this
  positivity

theorem cents_nonpos {x : ℚ} (h : x < 0) : cents x ≤ 0 := by
  unfold cents; rw [if_neg (not_le.mpr h)]
  have : (0 : ℤ) ≤ ⌊-x * 100 + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
  have : (0 : ℚ) ≤ (⌊-x * 100 + 1 / 2⌋ : ℚ) := by exact_mod_cast this
  have : 0 ≤ (⌊-x * 100 + 1 / 2⌋ : ℚ) / 100 := by positivity
  linarith

/-- Rounding to the cent never reverses an order. -/
theorem cents_mono {x y : ℚ} (h : x ≤ y) : cents x ≤ cents y := by
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := le_trans hx h
    unfold cents; rw [if_pos hx, if_pos hy]
    have : ⌊x * 100 + 1 / 2⌋ ≤ ⌊y * 100 + 1 / 2⌋ := Int.floor_le_floor (by linarith)
    have : (⌊x * 100 + 1 / 2⌋ : ℚ) ≤ ⌊y * 100 + 1 / 2⌋ := by exact_mod_cast this
    linarith
  · by_cases hy : 0 ≤ y
    · exact le_trans (cents_nonpos (not_le.mp hx)) (cents_nonneg hy)
    · unfold cents; rw [if_neg hx, if_neg hy]
      have : ⌊-y * 100 + 1 / 2⌋ ≤ ⌊-x * 100 + 1 / 2⌋ := Int.floor_le_floor (by linarith)
      have : (⌊-y * 100 + 1 / 2⌋ : ℚ) ≤ ⌊-x * 100 + 1 / 2⌋ := by exact_mod_cast this
      linarith

/-- A whole number of cents rounds to itself. -/
theorem cents_of_isCents {x : ℚ} (h : IsCents x) : cents x = x := by
  obtain ⟨n, rfl⟩ := h
  unfold cents
  have e1 : (n : ℚ) / 100 * 100 + 1 / 2 = ((n : ℚ) + 1 / 2) := by ring
  have e2 : -((n : ℚ) / 100) * 100 + 1 / 2 = ((-n : ℤ) : ℚ) + 1 / 2 := by push_cast; ring
  have f1 : ⌊(n : ℚ) + 1 / 2⌋ = n := by rw [Int.floor_eq_iff]; constructor <;> linarith
  have f2 : ⌊((-n : ℤ) : ℚ) + 1 / 2⌋ = -n := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  split_ifs
  · rw [e1, f1]
  · rw [e2, f2]; push_cast; ring

theorem isCents_cents (x : ℚ) : IsCents (cents x) := by
  unfold cents; split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨-⌊-x * 100 + 1 / 2⌋, by push_cast; ring⟩

theorem isCents_sub {x y : ℚ} (hx : IsCents x) (hy : IsCents y) : IsCents (x - y) := by
  obtain ⟨n, rfl⟩ := hx; obtain ⟨m, rfl⟩ := hy; exact ⟨n - m, by push_cast; ring⟩

/-- An amount no larger than a whole number of cents rounds to no more than it. -/
theorem cents_le_of_le {x L : ℚ} (h : x ≤ L) (hL : IsCents L) : cents x ≤ L :=
  (cents_of_isCents hL) ▸ cents_mono h

/-! ## 3. The year's entries, boxes 1802-1814 (`esReport`) -/

/-- What one sale (or the line of a loss counted later) adds to an entry: its 1804 `p`, its 1806 `c` (each a sum of
cents) and the loss put off `off` (`deferredOf` of the sale, 0 for the others and on every other line). -/
structure Line where
  key : ℕ
  p : ℚ
  c : ℚ
  off : ℚ

/-- An entry: a coin and what was received for it (or a sale with a loss put off, or a loss counted later). -/
structure Entry where
  key : ℕ
  p : ℚ
  c : ℚ
  off : ℚ

/-- `y.entries.get(ek) ?? {...}`, then the sums: into the entry of that key, or a new one at the end. -/
def put : List Entry → Line → List Entry
  | [], ln => [⟨ln.key, ln.p, ln.c, ln.off⟩]
  | e :: es, ln =>
    if e.key = ln.key then { e with p := e.p + ln.p, c := e.c + ln.c, off := e.off + ln.off } :: es
    else e :: put es ln

def entries (ls : List Line) : List Entry := ls.foldl put []

/-- `partOf`: the entry's part for this year, 1804 − 1806 + the loss put off. -/
def part (e : Entry) : ℚ := e.p - e.c + e.off

/-- 1807 / 1809 (`result`): 1804 − 1806. -/
def result (e : Entry) : ℚ := e.p - e.c

/-- Box 1813, the sum of the 1808s, and box 1814, the sum of the 1812s. -/
def box1813 (es : List Entry) : ℚ := (es.map fun e => max (-part e) 0).sum
def box1814 (es : List Entry) : ℚ := (es.map fun e => max (part e) 0).sum

/-- `gpOf`: saldo b, 1814 − 1813 plus futures gains `fg` less futures losses `fl`. -/
def gpOf (es : List Entry) (fg fl : ℚ) : ℚ := box1814 es - box1813 es + fg - fl

theorem put_part (es : List Entry) (ln : Line) :
    ((put es ln).map part).sum = (es.map part).sum + (ln.p - ln.c + ln.off) := by
  induction es with
  | nil => simp [put, part]
  | cons e es ih => unfold put; split_ifs <;> simp [part, ih] at * <;> ring

theorem put_p (es : List Entry) (ln : Line) : ((put es ln).map Entry.p).sum = (es.map Entry.p).sum + ln.p := by
  induction es with
  | nil => simp [put]
  | cons e es ih => unfold put; split_ifs <;> simp [ih] <;> ring

theorem put_c (es : List Entry) (ln : Line) : ((put es ln).map Entry.c).sum = (es.map Entry.c).sum + ln.c := by
  induction es with
  | nil => simp [put]
  | cons e es ih => unfold put; split_ifs <;> simp [ih] <;> ring

theorem entries_sums (ls : List Line) :
    ((entries ls).map part).sum = (ls.map fun l => l.p - l.c + l.off).sum ∧
      ((entries ls).map Entry.p).sum = (ls.map Line.p).sum ∧ ((entries ls).map Entry.c).sum = (ls.map Line.c).sum := by
  unfold entries
  suffices ∀ es : List Entry, ((ls.foldl put es).map part).sum = (es.map part).sum + (ls.map fun l => l.p - l.c + l.off).sum ∧
      ((ls.foldl put es).map Entry.p).sum = (es.map Entry.p).sum + (ls.map Line.p).sum ∧
      ((ls.foldl put es).map Entry.c).sum = (es.map Entry.c).sum + (ls.map Line.c).sum by simpa using this []
  induction ls with
  | nil => simp
  | cons l ls ih =>
    intro es; obtain ⟨h1, h2, h3⟩ := ih (put es l)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, h1, h2, h3, put_part, put_p, put_c]
    refine ⟨by ring, by ring, by ring⟩

theorem max_sub_max (x : ℚ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- **ES-2** Each entry's part for the year is 1804 − 1806 + its loss put off, and 1814 − 1813 is the sum of the
parts: the year's 1804 less its 1806 plus the losses put off, over every sale and every line of a loss counted now. -/
theorem box1814_sub_box1813 (ls : List Line) :
    box1814 (entries ls) - box1813 (entries ls) = ((entries ls).map part).sum ∧
      box1814 (entries ls) - box1813 (entries ls) =
        (ls.map Line.p).sum - (ls.map Line.c).sum + (ls.map Line.off).sum := by
  have e : ∀ es : List Entry, box1814 es - box1813 es = (es.map part).sum := by
    intro es; induction es with
    | nil => simp [box1813, box1814]
    | cons e es ih => simp only [box1813, box1814, List.map_cons, List.sum_cons] at *; linarith [max_sub_max (part e)]
  refine ⟨e _, ?_⟩
  rw [e, (entries_sums ls).1]
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **ES-2** Saldo b less the futures is 1814 − 1813. -/
theorem gp_less_futures (es : List Entry) (fg fl : ℚ) : gpOf es fg fl - (fg - fl) = box1814 es - box1813 es := by
  unfold gpOf; ring

/-! ### Box 1808 against box 1807 -/

/-- Box 1807 (a loss, the entry's result when negative) and box 1808 (the part for this year, when negative). -/
def box1807 (e : Entry) : ℚ := max (-result e) 0
def box1808 (e : Entry) : ℚ := max (-part e) 0

/-- **ES-4** On any entry whose loss put off is not below 0, box 1808 never exceeds box 1807. -/
theorem box1808_le_box1807 (e : Entry) (h : 0 ≤ e.off) : box1808 e ≤ box1807 e := by
  unfold box1808 box1807 part result
  exact max_le_max (by linarith) le_rfl

/-- **ES-4** A sale with a loss put off: its line's `off` is `cents` of what `esWash` put off, which is at most the
sale's loss `c − p` (a whole number of cents), so it is between 0 and that loss. -/
theorem off_within_loss (p c d : ℚ) (hp : IsCents p) (hc : IsCents c) (hd0 : 0 ≤ d) (hd : d ≤ c - p) :
    0 ≤ cents d ∧ cents d ≤ c - p :=
  ⟨cents_nonneg hd0, cents_le_of_le hd (isCents_sub hc hp)⟩

/-- **ES-4** So an entry of such sales (each sale's loss put off between 0 and its loss) has its part for the year at
most 0: a loss put off never turns an entry into a gain in box 1812. -/
theorem putOff_entry_part (ls : List Line) (h : ∀ l ∈ ls, 0 ≤ l.off ∧ l.off ≤ l.c - l.p) :
    ∀ e ∈ entries ls, 0 ≤ e.off ∧ e.off ≤ e.c - e.p := by
  unfold entries
  suffices ∀ es : List Entry, (∀ e ∈ es, 0 ≤ e.off ∧ e.off ≤ e.c - e.p) → ∀ e ∈ ls.foldl put es, 0 ≤ e.off ∧ e.off ≤ e.c - e.p
    from this [] (by simp)
  induction ls with
  | nil => simp
  | cons l ls ih =>
    intro es hes
    refine ih (fun x hx => h x (by simp [hx])) (put es l) ?_
    have hl := h l (by simp)
    clear ih
    induction es with
    | nil => simp [put]; exact ⟨hl.1, hl.2⟩
    | cons e es ihe =>
      have he := hes e (by simp)
      unfold put; split_ifs
      · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
        · simp; constructor <;> linarith [hl.1, hl.2, he.1, he.2]
        · exact hes x (by simp [hx])
      · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
        · exact he
        · exact ihe (fun y hy => hes y (by simp [hy])) x hx

theorem put_filter (es : List Entry) (ln : Line) (k : ℕ) :
    (put es ln).filter (fun e => e.key = k) =
      if ln.key = k then put (es.filter fun e => e.key = k) ln else es.filter fun e => e.key = k := by
  induction es with
  | nil => by_cases h : ln.key = k <;> simp [put, h]
  | cons e es ih =>
    by_cases he : e.key = ln.key
    · have hp : put (e :: es) ln = { e with p := e.p + ln.p, c := e.c + ln.c, off := e.off + ln.off } :: es := by
        simp [put, he]
      rw [hp]
      by_cases h : ln.key = k
      · have h' : e.key = k := he.trans h
        simp [List.filter_cons, h, h', put, he]
      · have h' : ¬ e.key = k := fun x => h (he.symm.trans x)
        simp [List.filter_cons, h, h']
    · have hp : put (e :: es) ln = e :: put es ln := by simp [put, he]
      rw [hp, List.filter_cons, ih]
      by_cases h : e.key = k
      · have hl : ¬ ln.key = k := fun x => he (h.trans x.symm)
        simp only [h, decide_true, if_true, hl, if_false, List.filter_cons]
      · by_cases hl : ln.key = k
        · simp only [h, decide_false, hl, if_true, List.filter_cons, Bool.false_eq_true, if_false]
        · simp only [h, decide_false, hl, if_false, List.filter_cons, Bool.false_eq_true]

/-- One key's entries depend on that key's lines only: the entries of a year, kept to one key, are the entries of
that key's lines. -/
theorem entries_filter (ls : List Line) (k : ℕ) :
    (entries ls).filter (fun e => e.key = k) = entries (ls.filter fun l => l.key = k) := by
  unfold entries
  suffices ∀ es : List Entry, (ls.foldl put es).filter (fun e => e.key = k) =
      (ls.filter fun l => l.key = k).foldl put (es.filter fun e => e.key = k) by simpa using this []
  induction ls with
  | nil => simp
  | cons l ls ih =>
    intro es
    rw [List.foldl_cons, ih, put_filter]
    by_cases h : l.key = k <;> simp [h]

/-- **ES-4** In a real year mixing gains and losses put off: every entry whose key's lines all have their loss put off
between 0 and their loss (`off_within_loss`) has its part for the year at most 0, whatever the other keys' lines. -/
theorem putOff_key (ls : List Line) (k : ℕ) (h : ∀ l ∈ ls, l.key = k → 0 ≤ l.off ∧ l.off ≤ l.c - l.p) :
    ∀ e ∈ entries ls, e.key = k → 0 ≤ e.off ∧ e.off ≤ e.c - e.p := by
  intro e he hk
  have : e ∈ entries (ls.filter fun l => l.key = k) := by
    rw [← entries_filter]; exact List.mem_filter.mpr ⟨he, by simpa using hk⟩
  exact putOff_entry_part _ (fun l hl => by
    obtain ⟨hl, hk'⟩ := List.mem_filter.mp hl; exact h l hl (by simpa using hk')) e this

/-- The line of a loss put off in an earlier year and counted this year (`releasedOf`): from the sale at a loss (its
1804 `sp`, 1806 `sc`, its loss `loss`) for the part `v` counted, `c = cents(sc × (v ÷ loss))` and `p = c − v`. -/
def releasedLine (key : ℕ) (sp sc loss v : ℚ) : Entry :=
  ⟨key, cents (sc * (v / loss)) - v, cents (sc * (v / loss)), 0⟩

/-- **ES-4** That line: 1804 = 1806 − v and is not below 0, and boxes 1807 and 1808 are both v (for a sale at a loss
whose 1804 is not below 0, `loss = sc − sp`, and a count of whole cents above 0). -/
theorem released_line (key : ℕ) (sp sc loss v : ℚ) (hsp : 0 ≤ sp) (hl : loss = sc - sp) (hpos : 0 < loss)
    (hv : 0 < v) (hvc : IsCents v) :
    let e := releasedLine key sp sc loss v
    e.p = e.c - v ∧ 0 ≤ e.p ∧ box1807 e = v ∧ box1808 e = v := by
  intro e
  have hx : v ≤ sc * (v / loss) := by
    rw [mul_div_assoc', le_div_iff₀ hpos]; nlinarith
  have := cents_mono hx
  rw [cents_of_isCents hvc] at this
  refine ⟨rfl, by simp [e, releasedLine]; linarith, ?_, ?_⟩
  · simp [e, releasedLine, box1807, result]; linarith
  · simp [e, releasedLine, box1808, part]; linarith

/-! ## 4. Art. 33.5.e LIRPF: a loss with the same coin bought again within a year (`esWash`) -/

/-- A sale at a loss (all its lots together): its coin, day (yyyymmdd), coins sold, loss, place in the day. -/
structure Loss where
  id : ℕ
  asset : ℕ
  date : ℕ
  qty : ℚ
  loss : ℚ
  seq : Option ℕ

/-- A purchase (the lot's id), its coin, day, coins and place in the day. -/
structure Buy where
  id : ℕ
  asset : ℕ
  date : ℕ
  qty : ℚ
  seq : Option ℕ

/-- A later sale of coins from a lot. -/
structure SaleOfLot where
  lot : ℕ
  date : ℕ
  qty : ℚ

def yearOf (date : ℕ) : ℕ := date / 10000

/-- `yearAfter`: the same day a year later, 29 February going to 28 February. -/
def yearAfter (d : ℕ) : ℕ := if d % 10000 = 229 then d + 9999 else d + 10000

/-- Both places in the day known and the purchase's before the sale's. -/
def earlier : Option ℕ → Option ℕ → Bool
  | some x, some y => decide (x < y)
  | _, _ => false

/-- A purchase that can put the loss off: the same coin, from the sale's day (after it, where both places are known)
to the same day a year later. -/
def eligible (l : Loss) (b : Buy) : Bool :=
  b.asset == l.asset && decide (l.date ≤ b.date) && decide (b.date ≤ yearAfter l.date) &&
    !(b.date == l.date && earlier b.seq l.seq)

/-- The purchases (oldest first, each with its coins still free) one loss takes: `min(free, need)` from each
eligible one with coins free, until the coins sold at a loss are covered. Returns the purchases with what is still
free and the coins taken from each. -/
def matchLoss (l : Loss) : ℚ → List (Buy × ℚ) → List (Buy × ℚ) × List (Buy × ℚ)
  | _, [] => ([], [])
  | need, (b, free) :: rest =>
    if need ≤ 0 then ((b, free) :: rest, [])
    else if eligible l b = true ∧ 0 < free then
      ((b, free - min free need) :: (matchLoss l (need - min free need) rest).1,
        (b, min free need) :: (matchLoss l (need - min free need) rest).2)
    else ((b, free) :: (matchLoss l need rest).1, (matchLoss l need rest).2)

/-- One part of a loss put off, on one purchase: the loss, its year, the purchase, the part (`amount`), what of it
still waits (`left`), and the purchase's coins carrying it (`qty`, of which `qLeft` not yet sold). -/
structure Part where
  loss : ℕ
  year : ℕ
  buy : ℕ
  amount : ℚ
  left : ℚ
  qty : ℚ
  qLeft : ℚ

structure W1 where
  free : List (Buy × ℚ)
  deferred : ℕ → ℚ
  parts : List Part

/-- One loss of `esWash`'s first loop: put off `loss × got ÷ qty`, shared between the purchases in proportion. -/
def washLoss (st : W1) (l : Loss) : W1 :=
  if l.loss ≤ 0 ∨ l.qty ≤ 0 then st
  else
    let m := matchLoss l l.qty st.free
    let got := (m.2.map Prod.snd).sum
    if got ≤ 0 then { st with free := m.1 }
    else
      let off := l.loss * got / l.qty
      ⟨m.1, Function.update st.deferred l.id off,
        st.parts ++ m.2.map fun x => ⟨l.id, yearOf l.date, x.1.id, off * x.2 / got, off * x.2 / got, x.2, x.2⟩⟩

/-- A sale of `sold` coins of lot `lot`: its parts in order (oldest loss first), each taking `min(sold, qLeft)`
coins and counting that share of the part (the last of its coins taking what is left of it). Returns the parts and
what was counted, by loss and the loss's year. -/
def release (lot : ℕ) : ℚ → List Part → List Part × List (ℕ × ℕ × ℚ)
  | _, [] => ([], [])
  | sold, p :: ps =>
    if p.buy ≠ lot then (p :: (release lot sold ps).1, (release lot sold ps).2)
    else if sold ≤ 0 then (p :: ps, [])
    else if p.qLeft ≤ 0 then (p :: (release lot sold ps).1, (release lot sold ps).2)
    else
      let take := min sold p.qLeft
      let r := if p.qLeft - take ≤ 0 then p.left else min p.left (p.amount * take / p.qty)
      ({ p with qLeft := p.qLeft - take, left := p.left - r } :: (release lot (sold - take) ps).1,
        (p.loss, p.year, r) :: (release lot (sold - take) ps).2)

/-- A loss counted in a later year than its own: the loss, the year it counts, how much. -/
structure Later where
  loss : ℕ
  year : ℕ
  amount : ℚ

/-- Counted in the loss's own year: it comes off the part put off; else it is counted later. -/
def count (y : ℕ) (st : (ℕ → ℚ) × List Later) (ev : ℕ × ℕ × ℚ) : (ℕ → ℚ) × List Later :=
  if y = ev.2.1 then (Function.update st.1 ev.1 (st.1 ev.1 - ev.2.2), st.2) else (st.1, st.2 ++ [⟨ev.1, y, ev.2.2⟩])

/-- The counts in the loss's own year, kept (the code only takes them off `deferred`) so they can be added up. -/
def sameList (y : ℕ) (evs : List (ℕ × ℕ × ℚ)) : List Later :=
  (evs.filter fun e => y = e.2.1).map fun e => ⟨e.1, y, e.2.2⟩

structure W2 where
  parts : List Part
  deferred : ℕ → ℚ
  later : List Later
  same : List Later

def washSale (st : W2) (s : SaleOfLot) : W2 :=
  let r := release s.lot s.qty st.parts
  let d := r.2.foldl (count (yearOf s.date)) (st.deferred, st.later)
  ⟨r.1, d.1, d.2, st.same ++ sameList (yearOf s.date) r.2⟩

/-- `esWash`: losses oldest first, purchases oldest first, then later sales oldest first (stable sorts, as the
code's). `deferred` is the part of each loss put off past its own year (0 for the others), `later` the counts in later
years, and the parts' `left` what still waits. -/
def wash (losses : List Loss) (buys : List Buy) (sales : List SaleOfLot) : W2 :=
  let w1 := (losses.mergeSort fun a b => decide (a.date ≤ b.date)).foldl washLoss
    ⟨(buys.mergeSort fun a b => decide (a.date ≤ b.date)).map fun b => (b, b.qty), fun _ => 0, []⟩
  (sales.mergeSort fun a b => decide (a.date ≤ b.date)).foldl washSale ⟨w1.parts, w1.deferred, [], []⟩

/-- What of loss `L` still waits, and what of it was counted in later years. -/
def waiting (L : ℕ) (ps : List Part) : ℚ := ((ps.filter fun p => p.loss = L).map Part.left).sum
def counted (L : ℕ) (ls : List Later) : ℚ := ((ls.filter fun e => e.loss = L).map Later.amount).sum
def evSum (L : ℕ) (evs : List (ℕ × ℕ × ℚ)) : ℚ := ((evs.filter fun e => e.1 = L).map fun e => e.2.2).sum

/-- A part as it should be: what waits is not below 0, nor is the part, and it is carried by some coins. -/
def Good (p : Part) : Prop := 0 ≤ p.left ∧ 0 ≤ p.amount ∧ 0 < p.qty

theorem matchLoss_sum (l : Loss) (need : ℚ) (fs : List (Buy × ℚ)) (h : 0 ≤ need) :
    ((matchLoss l need fs).2.map Prod.snd).sum ≤ need ∧ ∀ x ∈ (matchLoss l need fs).2, 0 < x.2 := by
  induction fs generalizing need with
  | nil => simp [matchLoss, h]
  | cons bf rest ih =>
    obtain ⟨b, free⟩ := bf
    unfold matchLoss; split_ifs with h0 h1
    · simp [h]
    · have hm : min free need ≤ need := min_le_right _ _
      obtain ⟨i1, i2⟩ := ih (need - min free need) (by linarith)
      refine ⟨by simp only [List.map_cons, List.sum_cons]; linarith, ?_⟩
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact lt_min h1.2 (not_le.mp h0)
      · exact i2 x hx
    · exact ih need h

theorem sum_scaled (xs : List (Buy × ℚ)) (off got : ℚ) :
    ((xs.map fun x => off * x.2 / got).sum) = off * (xs.map Prod.snd).sum / got := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem waiting_append (L : ℕ) (a b : List Part) : waiting L (a ++ b) = waiting L a + waiting L b := by
  simp [waiting, List.filter_append]

theorem waiting_new (L L' y : ℕ) (xs : List (Buy × ℚ)) (off got : ℚ) :
    waiting L (xs.map fun x => (⟨L', y, x.1.id, off * x.2 / got, off * x.2 / got, x.2, x.2⟩ : Part)) =
      if L = L' then off * (xs.map Prod.snd).sum / got else 0 := by
  induction xs with
  | nil => simp [waiting]
  | cons x xs ih =>
    unfold waiting at *
    simp only [List.map_cons, List.filter_cons]
    by_cases h : L' = L
    · subst h; simp at ih ⊢; rw [ih]; ring
    · simp [h, Ne.symm h] at ih ⊢; exact ih

/-- The first loop: for every loss, what is put off is what its parts hold; parts are as they should be; a loss
not yet processed has no part; and nothing put off exceeds the loss. -/
def Inv1 (st : W1) (todo done : List Loss) : Prop :=
  (∀ L, st.deferred L = waiting L st.parts) ∧ (∀ p ∈ st.parts, Good p ∧ p.amount = p.left) ∧
    (∀ p ∈ st.parts, p.loss ∉ todo.map Loss.id) ∧ (∀ l ∈ done, st.deferred l.id ≤ max l.loss 0) ∧
    (∀ L, L ∉ done.map Loss.id → st.deferred L = 0)

theorem washLoss_inv (st : W1) (l : Loss) (todo done : List Loss) (hnd : l.id ∉ todo.map Loss.id)
    (hd : l.id ∉ done.map Loss.id) (h : Inv1 st (l :: todo) done) : Inv1 (washLoss st l) todo (l :: done) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hz : waiting l.id st.parts = 0 := by
    unfold waiting
    rw [List.filter_eq_nil_iff.mpr (fun p hp => by have := h3 p hp; simp at this ⊢; exact fun e => this.1 e)]
    simp
  unfold washLoss
  dsimp only
  split_ifs with ha hg
  · refine ⟨h1, h2, fun p hp => ?_, fun x hx => ?_, fun L hL => h5 L (by simp at hL ⊢; tauto)⟩
    · have := h3 p hp; simp at this ⊢; tauto
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [h1, hz]; exact le_max_right _ _
      · exact h4 x hx
  · refine ⟨h1, h2, fun p hp => ?_, fun x hx => ?_, fun L hL => h5 L (by simp at hL ⊢; tauto)⟩
    · have := h3 p hp; simp at this ⊢; tauto
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [h1, hz]; exact le_max_right _ _
      · exact h4 x hx
  · push_neg at ha hg
    obtain ⟨hs, hpos⟩ := matchLoss_sum l l.qty st.free ha.2.le
    set m := matchLoss l l.qty st.free
    set got := (m.2.map Prod.snd).sum
    have hoff : 0 ≤ l.loss * got / l.qty := div_nonneg (mul_nonneg ha.1.le hg.le) ha.2.le
    refine ⟨fun L => ?_, fun p hp => ?_, fun p hp => ?_, fun x hx => ?_, fun L hL => ?_⟩
    · simp only [waiting_append, waiting_new]
      by_cases e : L = l.id
      · subst e; simp [hz, got]; field_simp
      · simp [e, h1]
    · rcases List.mem_append.mp hp with hp | hp
      · exact h2 p hp
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        have := hpos x hx
        exact ⟨⟨div_nonneg (mul_nonneg hoff this.le) hg.le, div_nonneg (mul_nonneg hoff this.le) hg.le, this⟩, rfl⟩
    · rcases List.mem_append.mp hp with hp | hp
      · have := h3 p hp; simp at this ⊢; tauto
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hnd
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Function.update_self]
        refine le_trans ?_ (le_max_left _ _)
        rw [div_le_iff₀ ha.2]; exact mul_le_mul_of_nonneg_left hs ha.1.le
      · have hne : x.id ≠ l.id := fun e => hd (e ▸ List.mem_map_of_mem hx)
        simp only [Function.update_of_ne hne]; exact h4 x hx
    · have hne : L ≠ l.id := fun e => hL (by simp [e])
      simp only [Function.update_of_ne hne]; exact h5 L (by simp at hL ⊢; tauto)

theorem washLosses_inv (ls : List Loss) (st : W1) (done : List Loss) (hnd : (ls.map Loss.id).Nodup)
    (hdis : ∀ l ∈ ls, l.id ∉ done.map Loss.id) (h : Inv1 st ls done) :
    Inv1 (ls.foldl washLoss st) [] (ls.reverse ++ done) := by
  induction ls generalizing st done with
  | nil => simpa using h
  | cons l ls ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    refine ih _ _ hnd.2 (fun x hx => ?_) (washLoss_inv st l ls done hnd.1 (hdis l (by simp)) h)
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨fun e => hnd.1 (e ▸ List.mem_map_of_mem hx), hdis x (by simp [hx])⟩

theorem release_spec (lot : ℕ) (sold : ℚ) (ps : List Part) (hg : ∀ p ∈ ps, Good p) :
    (∀ L, waiting L (release lot sold ps).1 + evSum L (release lot sold ps).2 = waiting L ps) ∧
      (∀ p ∈ (release lot sold ps).1, Good p) ∧ ∀ e ∈ (release lot sold ps).2, 0 ≤ e.2.2 := by
  induction ps generalizing sold with
  | nil => simp [release, waiting, evSum]
  | cons p ps ih =>
    have hp := hg p (by simp)
    have ihs := fun s => ih s (fun x hx => hg x (by simp [hx]))
    unfold release
    split_ifs with h1 h2 h3
    · obtain ⟨a, b, c⟩ := ihs sold
      refine ⟨fun L => ?_, fun x hx => ?_, c⟩
      · have := a L; unfold waiting at *; by_cases e : p.loss = L <;> simp [e] at this ⊢ <;> linarith
      · rcases List.mem_cons.mp hx with rfl | hx; exact hp; exact b x hx
    · exact ⟨fun L => by simp [evSum], hg, by simp⟩
    · obtain ⟨a, b, c⟩ := ihs sold
      refine ⟨fun L => ?_, fun x hx => ?_, c⟩
      · have := a L; unfold waiting at *; by_cases e : p.loss = L <;> simp [e] at this ⊢ <;> linarith
      · rcases List.mem_cons.mp hx with rfl | hx; exact hp; exact b x hx
    · obtain ⟨a, b, c⟩ := ihs (sold - min sold p.qLeft)
      push_neg at h2 h3
      set r := if p.qLeft - min sold p.qLeft ≤ 0 then p.left else min p.left (p.amount * min sold p.qLeft / p.qty)
      have hr : 0 ≤ r ∧ r ≤ p.left := by
        have ht : 0 ≤ min sold p.qLeft := le_min h2.le h3.le
        simp only [r]; split_ifs
        · exact ⟨hp.1, le_rfl⟩
        · exact ⟨le_min hp.1 (div_nonneg (mul_nonneg hp.2.1 ht) hp.2.2.le), min_le_left _ _⟩
      refine ⟨fun L => ?_, fun x hx => ?_, fun e he => ?_⟩
      · have := a L; unfold waiting evSum at *
        by_cases e : p.loss = L <;> simp [e] at this ⊢ <;> linarith
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨show 0 ≤ p.left - r by linarith [hr.2], hp.2.1, hp.2.2⟩
        · exact b x hx
      · rcases List.mem_cons.mp he with rfl | he
        · exact hr.1
        · exact c e he

theorem count_spec (y : ℕ) (evs : List (ℕ × ℕ × ℚ)) (st : (ℕ → ℚ) × List Later) (h : ∀ e ∈ evs, 0 ≤ e.2.2) :
    (∀ L, (evs.foldl (count y) st).1 L - counted L (evs.foldl (count y) st).2 = st.1 L - counted L st.2 - evSum L evs) ∧
      (∀ L, (evs.foldl (count y) st).1 L ≤ st.1 L) ∧
      ((∀ e ∈ st.2, 0 ≤ e.amount) → ∀ e ∈ (evs.foldl (count y) st).2, 0 ≤ e.amount) := by
  induction evs generalizing st with
  | nil => simp [evSum]
  | cons ev evs ih =>
    obtain ⟨a, b, c⟩ := ih (count y st ev) (fun e he => h e (by simp [he]))
    have h0 := h ev (by simp)
    simp only [List.foldl_cons]
    refine ⟨fun L => ?_, fun L => le_trans (b L) ?_, fun hs => c ?_⟩
    · rw [a L]; unfold count evSum counted
      by_cases e : ev.1 = L
      · subst e; split_ifs <;> simp [List.filter_append] <;> ring
      · split_ifs
        · simp [e, Function.update_of_ne (Ne.symm e)]
        · simp [List.filter_append, e]
    · unfold count; split_ifs
      · by_cases e : L = ev.1
        · subst e; simp; exact h0
        · simp [Function.update_of_ne e]
      · exact le_rfl
    · unfold count; split_ifs
      · exact hs
      · intro e he; rcases List.mem_append.mp he with he | he
        · exact hs e he
        · simp at he; subst he; exact h0

/-- The second loop: for every loss, what is put off is what was counted in later years plus what still waits. -/
def Inv2 (st : W2) : Prop :=
  (∀ L, st.deferred L = counted L st.later + waiting L st.parts) ∧ (∀ p ∈ st.parts, Good p) ∧
    ∀ e ∈ st.later, 0 ≤ e.amount

theorem washSale_inv (st : W2) (s : SaleOfLot) (h : Inv2 st) :
    Inv2 (washSale st s) ∧ ∀ L, (washSale st s).deferred L ≤ st.deferred L := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨a, b, c⟩ := release_spec s.lot s.qty st.parts h2
  obtain ⟨d, e, f⟩ := count_spec (yearOf s.date) (release s.lot s.qty st.parts).2 (st.deferred, st.later) c
  refine ⟨⟨fun L => ?_, b, f h3⟩, e⟩
  have := d L; have := a L; have := h1 L
  simp only [washSale] at *; linarith

theorem washSales_inv (ss : List SaleOfLot) (st : W2) (h : Inv2 st) :
    Inv2 (ss.foldl washSale st) ∧ ∀ L, (ss.foldl washSale st).deferred L ≤ st.deferred L := by
  induction ss generalizing st with
  | nil => exact ⟨h, fun _ => le_rfl⟩
  | cons s ss ih =>
    obtain ⟨h1, h2⟩ := washSale_inv st s h
    obtain ⟨i1, i2⟩ := ih _ h1
    exact ⟨i1, fun L => le_trans (i2 L) (h2 L)⟩

/-- **ES-3** Art. 33.5.e, for sales at a loss with distinct ids: for every loss, the part put off past its own year
is what was counted in later years plus what still waits (the coins bought again still held); every count and every
part still waiting is not below 0, and no loss has more put off than the loss itself. -/
theorem wash_conserves (losses : List Loss) (buys : List Buy) (sales : List SaleOfLot)
    (hnd : (losses.map Loss.id).Nodup) :
    let w := wash losses buys sales
    (∀ L, w.deferred L = counted L w.later + waiting L w.parts) ∧ (∀ e ∈ w.later, 0 ≤ e.amount) ∧
      (∀ p ∈ w.parts, 0 ≤ p.left) ∧ ∀ l ∈ losses, 0 ≤ w.deferred l.id ∧ w.deferred l.id ≤ max l.loss 0 := by
  intro w
  set ls := losses.mergeSort fun a b => decide (a.date ≤ b.date)
  have hperm : ls.Perm losses := List.mergeSort_perm _ _
  have hnd' : (ls.map Loss.id).Nodup := (hperm.map Loss.id).nodup_iff.mpr hnd
  have i0 : Inv1 ⟨(buys.mergeSort fun a b => decide (a.date ≤ b.date)).map fun b => (b, b.qty), fun _ => 0, []⟩ ls [] :=
    ⟨fun L => by simp [waiting], by simp, by simp, by simp, fun _ _ => rfl⟩
  obtain ⟨j1, j2, -, j4, -⟩ := washLosses_inv ls _ [] hnd' (by simp) i0
  set w1 := ls.foldl washLoss _
  have k0 : Inv2 ⟨w1.parts, w1.deferred, [], []⟩ :=
    ⟨fun L => by simp [counted, j1 L], fun p hp => (j2 p hp).1, by simp⟩
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := washSales_inv (sales.mergeSort fun a b => decide (a.date ≤ b.date)) _ k0
  refine ⟨k1, k3, fun p hp => (k2 p hp).1, fun l hl => ⟨?_, ?_⟩⟩
  · have e : w.deferred l.id = counted l.id w.later + waiting l.id w.parts := k1 l.id
    rw [e]
    refine add_nonneg (List.sum_nonneg fun x hx => ?_) (List.sum_nonneg fun x hx => ?_)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact k3 e (List.mem_filter.mp he).1
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact (k2 e (List.mem_filter.mp he).1).1
  · exact le_trans (k4 l.id) (j4 l (by simpa using hperm.mem_iff.mpr hl))

/-! ### The counts in cents (`releasedOf`): each on the running total, so they add up to the cent -/

/-- `releasedOf` for one loss: over its later counts in order, each year's count is `cents(after) − cents(before)`
of the running total, kept when above 0. -/
def countsFrom : ℚ → List Later → List (ℕ × ℚ)
  | _, [] => []
  | before, r :: rs =>
    if cents (before + r.amount) - cents before ≤ 0 then countsFrom (before + r.amount) rs
    else (r.year, cents (before + r.amount) - cents before) :: countsFrom (before + r.amount) rs

def releasedOf (L : ℕ) (later : List Later) : List (ℕ × ℚ) := countsFrom 0 (later.filter fun e => e.loss = L)

theorem countsFrom_sum (before : ℚ) (rs : List Later) (h : ∀ r ∈ rs, 0 ≤ r.amount) :
    ((countsFrom before rs).map Prod.snd).sum = cents (before + (rs.map Later.amount).sum) - cents before ∧
      ∀ x ∈ countsFrom before rs, 0 < x.2 ∧ IsCents x.2 := by
  induction rs generalizing before with
  | nil => simp [countsFrom]
  | cons r rs ih =>
    have h0 := h r (by simp)
    obtain ⟨a, b⟩ := ih (before + r.amount) (fun x hx => h x (by simp [hx]))
    have hm := cents_mono (show before ≤ before + r.amount by linarith)
    unfold countsFrom
    split_ifs with hv
    · refine ⟨?_, b⟩
      rw [a]; simp only [List.map_cons, List.sum_cons, add_assoc]; linarith
    · refine ⟨?_, fun x hx => ?_⟩
      · simp only [List.map_cons, List.sum_cons, a, add_assoc]; ring
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨not_le.mp hv, isCents_sub (isCents_cents _) (isCents_cents _)⟩
        · exact b x hx

/-- **ES-3** The counts of a loss in later years (each in the year its coins bought again were sold) are whole cents
above 0 and add up to the cents of everything counted later; once nothing waits, to the cents of the part put off, the
amount (`deferredOf`) left out of its own year's box 1808. -/
theorem released_counts (losses : List Loss) (buys : List Buy) (sales : List SaleOfLot)
    (hnd : (losses.map Loss.id).Nodup) (L : ℕ) :
    let w := wash losses buys sales
    (∀ x ∈ releasedOf L w.later, 0 < x.2 ∧ IsCents x.2) ∧
      ((releasedOf L w.later).map Prod.snd).sum = cents (counted L w.later) ∧
      (waiting L w.parts = 0 → ((releasedOf L w.later).map Prod.snd).sum = cents (w.deferred L)) := by
  intro w
  obtain ⟨h1, h2, -, -⟩ := wash_conserves losses buys sales hnd
  obtain ⟨a, b⟩ := countsFrom_sum 0 (w.later.filter fun e => e.loss = L)
    (fun r hr => h2 r (List.mem_filter.mp hr).1)
  have c0 : cents 0 = 0 := cents_of_isCents ⟨0, by simp⟩
  have hs : ((releasedOf L w.later).map Prod.snd).sum = cents (counted L w.later) := by
    unfold releasedOf; rw [a, c0]; simp [counted]
  exact ⟨b, hs, fun hz => by rw [hs, h1 L, hz, add_zero]⟩

/-! ### Where each part comes from, and the whole loss put off at the start -/

/-- The coins bought again that carry loss `L` (what `matchLoss` took for it). -/
def gotOf (L : ℕ) (ps : List Part) : ℚ := ((ps.filter fun p => p.loss = L).map Part.qty).sum

theorem matchLoss_from (l : Loss) (need : ℚ) (fs : List (Buy × ℚ)) :
    (∀ x ∈ (matchLoss l need fs).1, ∃ y ∈ fs, x.1 = y.1) ∧
      ∀ x ∈ (matchLoss l need fs).2, (∃ y ∈ fs, x.1 = y.1) ∧ eligible l x.1 = true := by
  induction fs generalizing need with
  | nil => simp [matchLoss]
  | cons bf rest ih =>
    obtain ⟨b, free⟩ := bf
    unfold matchLoss; split_ifs with h0 h1
    · exact ⟨fun x hx => ⟨x, hx, rfl⟩, by simp⟩
    · obtain ⟨i1, i2⟩ := ih (need - min free need)
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨(b, free), by simp, rfl⟩
        · obtain ⟨y, hy, e⟩ := i1 x hx; exact ⟨y, by simp [hy], e⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨⟨(b, free), by simp, rfl⟩, h1.1⟩
        · obtain ⟨⟨y, hy, e⟩, el⟩ := i2 x hx; exact ⟨⟨y, by simp [hy], e⟩, el⟩
    · obtain ⟨i1, i2⟩ := ih need
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨(b, free), by simp, rfl⟩
        · obtain ⟨y, hy, e⟩ := i1 x hx; exact ⟨y, by simp [hy], e⟩
      · obtain ⟨⟨y, hy, e⟩, el⟩ := i2 x hx; exact ⟨⟨y, by simp [hy], e⟩, el⟩

theorem gotOf_append (L : ℕ) (a b : List Part) : gotOf L (a ++ b) = gotOf L a + gotOf L b := by
  simp [gotOf, List.filter_append]

theorem gotOf_new (L L' y : ℕ) (xs : List (Buy × ℚ)) (off got : ℚ) :
    gotOf L (xs.map fun x => (⟨L', y, x.1.id, off * x.2 / got, off * x.2 / got, x.2, x.2⟩ : Part)) =
      if L = L' then (xs.map Prod.snd).sum else 0 := by
  induction xs with
  | nil => simp [gotOf]
  | cons x xs ih =>
    unfold gotOf at *
    simp only [List.map_cons, List.filter_cons]
    by_cases h : L' = L
    · subst h; simp at ih ⊢; rw [ih]
    · simp [h, Ne.symm h] at ih ⊢; exact ih

theorem gotOf_none (L : ℕ) (ps : List Part) (h : ∀ p ∈ ps, p.loss ≠ L) : gotOf L ps = 0 := by
  unfold gotOf; rw [List.filter_eq_nil_iff.mpr (fun p hp => by simpa using h p hp)]; simp

/-- The first loop, more: every free purchase and every part's purchase is one of `buys`; every part belongs to a loss
done, in that loss's year, on a purchase eligible for it; and each loss done has `loss × got ÷ qty` put off, `got`
being the coins its parts carry. -/
def Inv1b (buys : List Buy) (st : W1) (done : List Loss) : Prop :=
  (∀ x ∈ st.free, x.1 ∈ buys) ∧
    (∀ p ∈ st.parts, ∃ l ∈ done, p.loss = l.id ∧ p.year = yearOf l.date ∧
      ∃ b ∈ buys, b.id = p.buy ∧ eligible l b = true) ∧
    ∀ l ∈ done, st.deferred l.id = l.loss * gotOf l.id st.parts / l.qty

theorem washLoss_inv1b (buys : List Buy) (st : W1) (l : Loss) (todo done : List Loss)
    (hnd : l.id ∉ todo.map Loss.id) (hd : l.id ∉ done.map Loss.id) (h : Inv1 st (l :: todo) done)
    (hb : Inv1b buys st done) : Inv1b buys (washLoss st l) (l :: done) := by
  obtain ⟨-, -, h3, -, h5⟩ := h
  obtain ⟨b1, b2, b3⟩ := hb
  have hz : gotOf l.id st.parts = 0 := gotOf_none _ _ (fun p hp e => by have := h3 p hp; simp [e] at this)
  have hdz : st.deferred l.id = 0 := h5 _ hd
  have mf := matchLoss_from l l.qty st.free
  have keep : ∀ x ∈ done, x.id ≠ l.id := fun x hx e => hd (e ▸ List.mem_map_of_mem hx)
  unfold washLoss
  dsimp only
  split_ifs with ha hg
  · refine ⟨b1, fun p hp => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, r⟩ := b2 p hp; exact ⟨y, by simp [hy], r⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [hz, hdz]; simp
      · exact b3 x hx
  · refine ⟨fun x hx => ?_, fun p hp => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := mf.1 x hx; rw [e]; exact b1 y hy
    · obtain ⟨y, hy, r⟩ := b2 p hp; exact ⟨y, by simp [hy], r⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [hz, hdz]; simp
      · exact b3 x hx
  · refine ⟨fun x hx => ?_, fun p hp => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := mf.1 x hx; rw [e]; exact b1 y hy
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨y, hy, r⟩ := b2 p hp; exact ⟨y, by simp [hy], r⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨⟨y, hy, e⟩, el⟩ := mf.2 x hx
        exact ⟨l, by simp, rfl, rfl, x.1, by rw [e]; exact b1 y hy, rfl, el⟩
    · simp only [gotOf_append, gotOf_new]
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hz]
      · have hne := keep x hx
        rw [Function.update_of_ne hne, if_neg hne, add_zero]; exact b3 x hx

theorem washLosses_inv1b (buys : List Buy) (ls : List Loss) (st : W1) (done : List Loss)
    (hnd : (ls.map Loss.id).Nodup) (hdis : ∀ l ∈ ls, l.id ∉ done.map Loss.id) (h : Inv1 st ls done)
    (hb : Inv1b buys st done) : Inv1b buys (ls.foldl washLoss st) (ls.reverse ++ done) := by
  induction ls generalizing st done with
  | nil => simpa using hb
  | cons l ls ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    have hd' : ∀ x ∈ ls, x.id ∉ (l :: done).map Loss.id := fun x hx => by
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun e => hnd.1 (e ▸ List.mem_map_of_mem hx), hdis x (by simp [hx])⟩
    exact ih _ _ hnd.2 hd' (washLoss_inv st l ls done hnd.1 (hdis l (by simp)) h)
      (washLoss_inv1b buys st l ls done hnd.1 (hdis l (by simp)) h hb)

theorem release_from (lot : ℕ) (sold : ℚ) (ps : List Part) :
    (∀ p ∈ (release lot sold ps).1, ∃ q ∈ ps, p.loss = q.loss ∧ p.year = q.year ∧ p.buy = q.buy) ∧
      ∀ L, gotOf L (release lot sold ps).1 = gotOf L ps := by
  induction ps generalizing sold with
  | nil => simp [release]
  | cons p ps ih =>
    unfold release
    split_ifs with h1 h2 h3
    all_goals first
      | exact ⟨fun x hx => ⟨x, hx, rfl, rfl, rfl⟩, fun _ => rfl⟩
      | (obtain ⟨a, b⟩ := ih sold
         refine ⟨fun x hx => ?_, fun L => ?_⟩
         · rcases List.mem_cons.mp hx with rfl | hx
           · exact ⟨x, by simp, rfl, rfl, rfl⟩
           · obtain ⟨q, hq, r⟩ := a x hx; exact ⟨q, by simp [hq], r⟩
         · have := b L; unfold gotOf at *; by_cases e : p.loss = L <;> simp [e, this])
      | (obtain ⟨a, b⟩ := ih (sold - min sold p.qLeft)
         refine ⟨fun x hx => ?_, fun L => ?_⟩
         · rcases List.mem_cons.mp hx with rfl | hx
           · exact ⟨p, by simp, rfl, rfl, rfl⟩
           · obtain ⟨q, hq, r⟩ := a x hx; exact ⟨q, by simp [hq], r⟩
         · have := b L; unfold gotOf at *; by_cases e : p.loss = L <;> simp [e, this])

theorem count_deferred (y : ℕ) (evs : List (ℕ × ℕ × ℚ)) (st : (ℕ → ℚ) × List Later) (L : ℕ) :
    (evs.foldl (count y) st).1 L + counted L (sameList y evs) = st.1 L := by
  induction evs generalizing st with
  | nil => simp [sameList, counted]
  | cons ev evs ih =>
    simp only [List.foldl_cons]
    have := ih (count y st ev)
    unfold count at this ⊢; unfold sameList counted at *
    by_cases hy : y = ev.2.1
    · simp only [hy, if_true, List.filter_cons, decide_true, List.map_cons, List.filter_cons] at this ⊢
      by_cases e : ev.1 = L
      · subst e; simp at this ⊢; linarith
      · simp [e, Function.update_of_ne (Ne.symm e)] at this ⊢; linarith
    · simp [hy] at this ⊢; linarith

/-- The second loop keeps: the part put off at the start is what is put off now plus the counts in its own year. -/
theorem washSales_same (ss : List SaleOfLot) (st : W2) (L : ℕ) :
    (ss.foldl washSale st).deferred L + counted L (ss.foldl washSale st).same = st.deferred L + counted L st.same ∧
      gotOf L (ss.foldl washSale st).parts = gotOf L st.parts ∧
      ∀ p ∈ (ss.foldl washSale st).parts, ∃ q ∈ st.parts, p.loss = q.loss ∧ p.year = q.year ∧ p.buy = q.buy := by
  induction ss generalizing st with
  | nil => exact ⟨rfl, rfl, fun p hp => ⟨p, hp, rfl, rfl, rfl⟩⟩
  | cons s ss ih =>
    obtain ⟨i1, i2, i3⟩ := ih (washSale st s)
    obtain ⟨r1, r2⟩ := release_from s.lot s.qty st.parts
    have c := count_deferred (yearOf s.date) (release s.lot s.qty st.parts).2 (st.deferred, st.later) L
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, fun p hp => ?_⟩
    · rw [i1]; simp only [washSale, counted, List.filter_append, List.map_append, List.sum_append] at c ⊢
      linarith
    · rw [i2]; exact r2 L
    · obtain ⟨q, hq, e⟩ := i3 p hp
      obtain ⟨q', hq', e'⟩ := r1 q hq
      exact ⟨q', hq', e.1.trans e'.1, e.2.1.trans e'.2.1, e.2.2.trans e'.2.2⟩

/-- **ES-3** Art. 33.5.e in full, for sales at a loss with distinct ids. Every part of a loss put off sits on one of
the purchases, of the same coin, made from the sale's day to the same day a year later (`eligible`), and is in the
loss's own year. For every loss, what is put off at the start is `loss × got ÷ qty` (`got` the coins bought again
that carry it; the code's `off`, not rounded there) and it all ends up somewhere: counted in its own year (the coins
bought again sold that year) + counted in later years + still waiting. -/
theorem wash_split (losses : List Loss) (buys : List Buy) (sales : List SaleOfLot)
    (hnd : (losses.map Loss.id).Nodup) :
    let w := wash losses buys sales
    (∀ p ∈ w.parts, ∃ l ∈ losses, p.loss = l.id ∧ p.year = yearOf l.date ∧ ∃ b ∈ buys, b.id = p.buy ∧
        eligible l b = true ∧ b.asset = l.asset ∧ l.date ≤ b.date ∧ b.date ≤ yearAfter l.date) ∧
      ∀ l ∈ losses, l.loss * gotOf l.id w.parts / l.qty =
        counted l.id w.same + counted l.id w.later + waiting l.id w.parts := by
  intro w
  set ls := losses.mergeSort fun a b => decide (a.date ≤ b.date)
  have hperm : ls.Perm losses := List.mergeSort_perm _ _
  have hnd' : (ls.map Loss.id).Nodup := (hperm.map Loss.id).nodup_iff.mpr hnd
  set st0 : W1 := ⟨(buys.mergeSort fun a b => decide (a.date ≤ b.date)).map fun b => (b, b.qty), fun _ => 0, []⟩
  have i0 : Inv1 st0 ls [] := ⟨fun L => by simp [st0, waiting], by simp [st0], by simp [st0], by simp, fun _ _ => rfl⟩
  have b0 : Inv1b buys st0 [] := ⟨fun x hx => by
      simp only [st0, List.mem_map] at hx; obtain ⟨b, hb, rfl⟩ := hx
      exact (List.mergeSort_perm _ _).mem_iff.mp hb, by simp [st0], by simp⟩
  obtain ⟨j1, j2, -, -, -⟩ := washLosses_inv ls st0 [] hnd' (by simp) i0
  obtain ⟨-, m2, m3⟩ := washLosses_inv1b buys ls st0 [] hnd' (by simp) i0 b0
  set w1 := ls.foldl washLoss st0
  have k0 : Inv2 ⟨w1.parts, w1.deferred, [], []⟩ :=
    ⟨fun L => by simp [counted, j1 L], fun p hp => (j2 p hp).1, by simp⟩
  obtain ⟨⟨k1, -, -⟩, -⟩ := washSales_inv (sales.mergeSort fun a b => decide (a.date ≤ b.date)) _ k0
  have hmem : ∀ l, l ∈ ls.reverse ++ [] ↔ l ∈ losses := fun l => by simp [hperm.mem_iff]
  refine ⟨fun p hp => ?_, fun l hl => ?_⟩
  · obtain ⟨-, -, s3⟩ := washSales_same (sales.mergeSort fun a b => decide (a.date ≤ b.date))
      ⟨w1.parts, w1.deferred, [], []⟩ 0
    obtain ⟨q, hq, e1, e2, e3⟩ := s3 p hp
    obtain ⟨l, hl, f1, f2, b, hb, f3, f4⟩ := m2 q hq
    have el := f4
    simp only [eligible, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at el
    exact ⟨l, (hmem l).mp hl, e1.trans f1, e2.trans f2, b, hb, f3.trans e3.symm, f4, el.1.1.1, el.1.1.2,
      el.1.2⟩
  · obtain ⟨s1, s2, -⟩ := washSales_same (sales.mergeSort fun a b => decide (a.date ≤ b.date))
      ⟨w1.parts, w1.deferred, [], []⟩ l.id
    have e : w.deferred l.id = counted l.id w.later + waiting l.id w.parts := k1 l.id
    have d0 := m3 l ((hmem l).mpr hl)
    change w.deferred l.id + counted l.id w.same = w1.deferred l.id + counted l.id [] at s1
    change gotOf l.id w.parts = gotOf l.id w1.parts at s2
    rw [s2, ← d0]
    simp only [counted, List.filter_nil, List.map_nil, List.sum_nil, add_zero] at s1
    unfold counted at e ⊢
    linarith

/-! ## 5. Art. 49 LIRPF: the savings base's two saldos, their offsets and four-year carry (`esSavings`) -/

/-- Which saldo: `gp` gains and losses from transfers (saldo b), `rcm` capital income (saldo a). -/
inductive Kind | gp | rcm
  deriving DecidableEq

/-- A negative saldo still to be used: its year (`from` in the code), its kind, what is left of it. -/
structure Pending where
  yr : ℤ
  kind : Kind
  amount : ℚ

def psum (ps : List Pending) : ℚ := (ps.map Pending.amount).sum

/-- The year's working values: the two saldos, what earlier losses were used of each kind against their own saldo
(`own…`) and against the other (`cross…`: `crossRcm` is capital-income losses taken off gains), and the room left
in each 25% limit. -/
structure St where
  gp : ℚ
  rcm : ℚ
  ownGp : ℚ
  ownRcm : ℚ
  crossGp : ℚ
  crossRcm : ℚ
  roomGp : ℚ
  roomRcm : ℚ

def St.own (s : St) : Kind → ℚ
  | .gp => s.gp
  | .rcm => s.rcm

def St.used (s : St) : ℚ := s.ownGp + s.ownRcm + s.crossGp + s.crossRcm

def takeOwn (s : St) : Kind → ℚ → St
  | .gp, t => { s with gp := s.gp - t, ownGp := s.ownGp + t }
  | .rcm, t => { s with rcm := s.rcm - t, ownRcm := s.ownRcm + t }

/-- Fase 2, 1º, one loss: against its own kind's saldo, if above 0, as much as both allow. Returns what was taken. -/
def ownStep (s : St) (p : Pending) : St × ℚ :=
  if s.own p.kind ≤ 0 then (s, 0)
  else (takeOwn s p.kind (min (s.own p.kind) p.amount), min (s.own p.kind) p.amount)

def takeCrossRcm (s : St) (t : ℚ) : St :=
  { s with gp := s.gp - t, roomGp := s.roomGp - t, crossRcm := s.crossRcm + t }

def takeCrossGp (s : St) (t : ℚ) : St :=
  { s with rcm := s.rcm - t, roomRcm := s.roomRcm - t, crossGp := s.crossGp + t }

/-- Fase 2, 2º, one loss: what is left of it against the other kind's saldo, within the room left in that 25%. -/
def crossStep (s : St) (p : Pending) : St × ℚ :=
  if p.amount ≤ 0 then (s, 0)
  else if p.kind = .rcm ∧ 0 < s.gp ∧ 0 < s.roomGp then
    (takeCrossRcm s (min (min p.amount s.gp) s.roomGp), min (min p.amount s.gp) s.roomGp)
  else if p.kind = .gp ∧ 0 < s.rcm ∧ 0 < s.roomRcm then
    (takeCrossGp s (min (min p.amount s.rcm) s.roomRcm), min (min p.amount s.rcm) s.roomRcm)
  else (s, 0)

/-- One loop over the losses waiting, oldest first, each reduced by what its step took. -/
def pass (step : St → Pending → St × ℚ) : St → List Pending → St × List Pending
  | s, [] => (s, [])
  | s, p :: ps => ((pass step (step s p).1 ps).1,
      { p with amount := p.amount - (step s p).2 } :: (pass step (step s p).1 ps).2)

theorem pass_shape (step : St → Pending → St × ℚ) (s : St) (ps : List Pending) :
    (pass step s ps).2.map (fun q => (q.yr, q.kind)) = ps.map (fun p => (p.yr, p.kind)) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp [pass, ih]

theorem pass_length (step : St → Pending → St × ℚ) (s : St) (ps : List Pending) :
    (pass step s ps).2.length = ps.length := by
  simpa using congrArg List.length (pass_shape step s ps)

theorem pass_sum (step : St → Pending → St × ℚ) (hs : ∀ s p, (step s p).1.used = s.used + (step s p).2)
    (s : St) (ps : List Pending) : psum (pass step s ps).2 + (pass step s ps).1.used = psum ps + s.used := by
  induction ps generalizing s with
  | nil => simp [pass]
  | cons p ps ih =>
    have := ih (step s p).1; have := hs s p
    simp only [pass, psum, List.map_cons, List.sum_cons] at *; linarith

theorem pass_inv (step : St → Pending → St × ℚ) (P : St → Prop) (s : St) (ps : List Pending)
    (h : ∀ s, ∀ p ∈ ps, P s → P (step s p).1) (h0 : P s) : P (pass step s ps).1 := by
  induction ps generalizing s with
  | nil => exact h0
  | cons p ps ih => exact ih _ (fun s q hq => h s q (by simp [hq])) (h s p (by simp) h0)

/-- Each loss in, beside what is left of it. -/
theorem pass_bounds (step : St → Pending → St × ℚ)
    (hs : ∀ s p, 0 ≤ p.amount → 0 ≤ (step s p).2 ∧ (step s p).2 ≤ p.amount) (s : St) (ps : List Pending)
    (h : ∀ p ∈ ps, 0 ≤ p.amount) :
    ∀ x ∈ ps.zip (pass step s ps).2, 0 ≤ x.2.amount ∧ x.2.amount ≤ x.1.amount := by
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih =>
    intro x hx
    simp only [pass, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := hs s p (h p (by simp)); simp; constructor <;> linarith
    · exact ih _ (fun q hq => h q (by simp [hq])) x hx

theorem pass_nonneg (step : St → Pending → St × ℚ)
    (hs : ∀ s p, 0 ≤ p.amount → 0 ≤ (step s p).2 ∧ (step s p).2 ≤ p.amount) (s : St) (ps : List Pending)
    (h : ∀ p ∈ ps, 0 ≤ p.amount) : ∀ q ∈ (pass step s ps).2, 0 ≤ q.amount := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  have hl := pass_length step s ps
  have := pass_bounds step hs s ps h (ps[i]'(by omega), (pass step s ps).2[i]) (by
    rw [← List.getElem_zip (l := ps) (l' := (pass step s ps).2) (i := i) (h := by simp; omega)]
    exact List.getElem_mem _)
  exact this.1

/-- Oldest first, for any step that stops a kind once it is used up: a loss left over blocks every later loss of its
kind, which then stays as it was. -/
theorem pass_oldest (step : St → Pending → St × ℚ) (blocked : St → Kind → Prop)
    (h1 : ∀ s p, blocked s p.kind → (step s p).2 = 0)
    (h2 : ∀ s p k, blocked s k → blocked (step s p).1 k)
    (h3 : ∀ s p, 0 < p.amount - (step s p).2 → blocked (step s p).1 p.kind) (s : St) (ps : List Pending) :
    (ps.zip (pass step s ps).2).Pairwise
      (fun a b => a.1.kind = b.1.kind → 0 < a.2.amount → b.2.amount = b.1.amount) := by
  have hb : ∀ s k (ps : List Pending), blocked s k → ∀ x ∈ ps.zip (pass step s ps).2, x.1.kind = k → x.2.amount = x.1.amount := by
    intro s k ps hk
    induction ps generalizing s with
    | nil => simp
    | cons p ps ih =>
      intro x hx
      simp only [pass, List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · intro e; simp [h1 s p (e ▸ hk)]
      · exact ih _ (h2 s p k hk) x hx
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih =>
    simp only [pass, List.zip_cons_cons, List.pairwise_cons]
    refine ⟨fun x hx e hp => hb _ p.kind ps (h3 s p hp) x hx e.symm, ih _⟩

/-- The pair-wise statement as positions in the list. -/
theorem zip_pairwise_get {α β : Type} (R : α × β → α × β → Prop) (a : List α) (b : List β) (hl : b.length = a.length)
    (h : (a.zip b).Pairwise R) (i j : ℕ) (hi : i < a.length) (hj : j < a.length) (hij : i < j) :
    R (a[i], b[i]) (a[j], b[j]) := by
  rw [List.pairwise_iff_getElem] at h
  have := h i j (by simp; omega) (by simp; omega) hij
  simpa using this

theorem pass_get (step : St → Pending → St × ℚ) (s : St) (ps : List Pending) (i : ℕ) (hi : i < ps.length) :
    ((pass step s ps).2[i]'(by rw [pass_length]; exact hi)).yr = ps[i].yr ∧
      ((pass step s ps).2[i]'(by rw [pass_length]; exact hi)).kind = ps[i].kind := by
  induction ps generalizing s i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => simp [pass]
    | succ i => simpa [pass] using ih (step s p).1 i (by simpa using hi)

theorem pass_get_bounds (step : St → Pending → St × ℚ)
    (hs : ∀ s p, 0 ≤ p.amount → 0 ≤ (step s p).2 ∧ (step s p).2 ≤ p.amount) (s : St) (ps : List Pending)
    (h : ∀ p ∈ ps, 0 ≤ p.amount) (i : ℕ) (hi : i < ps.length) :
    0 ≤ ((pass step s ps).2[i]'(by rw [pass_length]; exact hi)).amount ∧
      ((pass step s ps).2[i]'(by rw [pass_length]; exact hi)).amount ≤ ps[i].amount := by
  induction ps generalizing s i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => have := hs s p (h p (by simp)); simp [pass]; constructor <;> linarith
    | succ i => simpa [pass] using ih (step s p).1 (fun q hq => h q (by simp [hq])) i (by simpa using hi)

theorem pass_mem (step : St → Pending → St × ℚ) (s : St) (ps : List Pending) (q : Pending)
    (hq : q ∈ (pass step s ps).2) : ∃ p ∈ ps, p.yr = q.yr ∧ p.kind = q.kind := by
  have := List.mem_map_of_mem (f := fun q : Pending => (q.yr, q.kind)) hq
  rw [pass_shape] at this
  obtain ⟨p, hp, e⟩ := List.mem_map.mp this
  exact ⟨p, hp, (Prod.ext_iff.mp e).1, (Prod.ext_iff.mp e).2⟩

theorem pass_yrs (step : St → Pending → St × ℚ) (s : St) (ps : List Pending) :
    (pass step s ps).2.map Pending.yr = ps.map Pending.yr := by
  have := congrArg (List.map Prod.fst) (pass_shape step s ps)
  simpa [Function.comp_def] using this

theorem ownStep_used (s : St) (p : Pending) : (ownStep s p).1.used = s.used + (ownStep s p).2 := by
  unfold ownStep; split_ifs
  · simp
  · cases h : p.kind <;> simp [takeOwn, St.used] <;> ring

theorem crossStep_used (s : St) (p : Pending) : (crossStep s p).1.used = s.used + (crossStep s p).2 := by
  unfold crossStep; split_ifs <;> simp [takeCrossRcm, takeCrossGp, St.used] <;> ring

theorem ownStep_bounds (s : St) (p : Pending) (h : 0 ≤ p.amount) :
    0 ≤ (ownStep s p).2 ∧ (ownStep s p).2 ≤ p.amount := by
  unfold ownStep; split_ifs with h0
  · simp [h]
  · push_neg at h0; exact ⟨le_min h0.le h, min_le_right _ _⟩

theorem crossStep_bounds (s : St) (p : Pending) (h : 0 ≤ p.amount) :
    0 ≤ (crossStep s p).2 ∧ (crossStep s p).2 ≤ p.amount := by
  unfold crossStep; split_ifs with h0 h1 h2
  · simp; linarith
  · push_neg at h0
    exact ⟨le_min (le_min h0.le h1.2.1.le) h1.2.2.le, le_trans (min_le_left _ _) (min_le_left _ _)⟩
  · push_neg at h0
    exact ⟨le_min (le_min h0.le h2.2.1.le) h2.2.2.le, le_trans (min_le_left _ _) (min_le_left _ _)⟩
  · simp; linarith

theorem ownStep_oldest :
    (∀ s p, s.own p.kind ≤ 0 → (ownStep s p).2 = 0) ∧
      (∀ s p k, s.own k ≤ 0 → (ownStep s p).1.own k ≤ 0) ∧
      (∀ s p, 0 < p.amount - (ownStep s p).2 → (ownStep s p).1.own p.kind ≤ 0) := by
  refine ⟨fun s p h => by simp [ownStep, h], fun s p k h => ?_, fun s p h => ?_⟩
  · unfold ownStep; split_ifs with h0
    · exact h
    · cases hk : p.kind <;> cases k <;> simp_all [takeOwn, St.own] <;> linarith
  · unfold ownStep at *; split_ifs at * with h0
    · exact h0
    · have : min (s.own p.kind) p.amount = s.own p.kind := min_eq_left (by
        by_contra hc; push_neg at hc; rw [min_eq_right hc.le] at h; simp at h)
      rw [this]; cases hk : p.kind <;> simp [takeOwn, St.own, hk] at *

/-- Fase 2, 2º, stops a kind when the other saldo or the room left in its limit is used up. -/
def crossBlocked (s : St) : Kind → Prop
  | .rcm => s.gp ≤ 0 ∨ s.roomGp ≤ 0
  | .gp => s.rcm ≤ 0 ∨ s.roomRcm ≤ 0

theorem crossStep_oldest :
    (∀ s p, crossBlocked s p.kind → (crossStep s p).2 = 0) ∧
      (∀ s p k, crossBlocked s k → crossBlocked (crossStep s p).1 k) ∧
      (∀ s p, 0 < p.amount - (crossStep s p).2 → crossBlocked (crossStep s p).1 p.kind) := by
  refine ⟨fun s p h => ?_, fun s p k h => ?_, fun s p h => ?_⟩
  · unfold crossStep; split_ifs with h0 h1 h2
    · rfl
    · exfalso; rw [h1.1] at h; simp [crossBlocked] at h
      rcases h with h | h <;> linarith [h1.2.1, h1.2.2]
    · exfalso; rw [h2.1] at h; simp [crossBlocked] at h
      rcases h with h | h <;> linarith [h2.2.1, h2.2.2]
    · rfl
  · unfold crossStep; split_ifs with h0 h1 h2
    · exact h
    · cases k
      · simpa [crossBlocked, takeCrossRcm] using h
      · exfalso; simp [crossBlocked] at h; rcases h with h | h <;> linarith [h1.2.1, h1.2.2]
    · cases k
      · exfalso; simp [crossBlocked] at h; rcases h with h | h <;> linarith [h2.2.1, h2.2.2]
      · simpa [crossBlocked, takeCrossGp] using h
    · exact h
  · unfold crossStep at *; split_ifs at * with h0 h1 h2
    · simp at h; linarith
    · rw [h1.1]; simp only [crossBlocked, takeCrossRcm]
      rcases min_choice (min p.amount s.gp) s.roomGp with e | e <;> rw [e] at h ⊢
      · rcases min_choice p.amount s.gp with e2 | e2 <;> rw [e2] at h ⊢
        · simp at h
        · left; simp
      · right; simp
    · rw [h2.1]; simp only [crossBlocked, takeCrossGp]
      rcases min_choice (min p.amount s.rcm) s.roomRcm with e | e <;> rw [e] at h ⊢
      · rcases min_choice p.amount s.rcm with e2 | e2 <;> rw [e2] at h ⊢
        · simp at h
        · left; simp
      · right; simp
    · cases hk : p.kind
      · simp only [crossBlocked]; by_contra hc; push_neg at hc; exact h2 ⟨hk, hc⟩
      · simp only [crossBlocked]; by_contra hc; push_neg at hc; exact h1 ⟨hk, hc⟩

/-- The steps never turn a saldo from at or below 0 to anything else, nor take a positive saldo below 0. -/
theorem steps_keep_sign (step : St → Pending → St × ℚ) (hstep : step = ownStep ∨ step = crossStep)
    (s : St) (p : Pending) :
    min (step s p).1.gp 0 = min s.gp 0 ∧ min (step s p).1.rcm 0 = min s.rcm 0 := by
  rcases hstep with rfl | rfl
  · unfold ownStep; split_ifs with h0
    · simp
    · push_neg at h0
      cases hk : p.kind
      · simp only [hk, St.own] at h0 ⊢
        simp only [takeOwn]
        refine ⟨?_, by simp⟩
        rw [min_eq_right (by linarith [min_le_left s.gp p.amount]), min_eq_right h0.le]
      · simp only [hk, St.own] at h0 ⊢
        simp only [takeOwn]
        refine ⟨by simp, ?_⟩
        rw [min_eq_right (by linarith [min_le_left s.rcm p.amount]), min_eq_right h0.le]
  · unfold crossStep; split_ifs with h0 h1 h2
    · simp
    · simp only [takeCrossRcm]; refine ⟨?_, by simp⟩
      rw [min_eq_right (by linarith [min_le_left (min p.amount s.gp) s.roomGp, min_le_right p.amount s.gp]),
        min_eq_right h1.2.1.le]
    · simp only [takeCrossGp]; refine ⟨by simp, ?_⟩
      rw [min_eq_right (by linarith [min_le_left (min p.amount s.rcm) s.roomRcm, min_le_right p.amount s.rcm]),
        min_eq_right h2.2.1.le]
    · simp

/-- Each limit's room plus what was taken out of it stays the same; the room never goes below 0. -/
theorem steps_room (step : St → Pending → St × ℚ) (hstep : step = ownStep ∨ step = crossStep) (s : St) (p : Pending) :
    (step s p).1.roomGp + (step s p).1.crossRcm = s.roomGp + s.crossRcm ∧
      (step s p).1.roomRcm + (step s p).1.crossGp = s.roomRcm + s.crossGp ∧
      (0 ≤ s.roomGp → 0 ≤ (step s p).1.roomGp) ∧ (0 ≤ s.roomRcm → 0 ≤ (step s p).1.roomRcm) := by
  rcases hstep with rfl | rfl
  · unfold ownStep; split_ifs
    · simp
    · cases p.kind <;> simp [takeOwn]
  · unfold crossStep; split_ifs with h0 h1 h2
    · simp
    · simp only [takeCrossRcm]
      refine ⟨by ring, by simp, fun _ => by linarith [min_le_right (min p.amount s.gp) s.roomGp], fun h => h⟩
    · simp only [takeCrossGp]
      refine ⟨by simp, by ring, fun h => h, fun _ => by linarith [min_le_right (min p.amount s.rcm) s.roomRcm]⟩
    · simp

theorem steps_cross_mono (step : St → Pending → St × ℚ) (hstep : step = ownStep ∨ step = crossStep) (s : St)
    (p : Pending) : s.crossRcm ≤ (step s p).1.crossRcm ∧ s.crossGp ≤ (step s p).1.crossGp := by
  rcases hstep with rfl | rfl
  · unfold ownStep; split_ifs
    · exact ⟨le_rfl, le_rfl⟩
    · cases p.kind <;> simp [takeOwn]
  · unfold crossStep; split_ifs with h0 h1 h2
    · exact ⟨le_rfl, le_rfl⟩
    · push_neg at h0; simp only [takeCrossRcm]
      exact ⟨by linarith [le_min (le_min h0.le h1.2.1.le) h1.2.2.le], le_rfl⟩
    · push_neg at h0; simp only [takeCrossGp]
      exact ⟨le_rfl, by linarith [le_min (le_min h0.le h2.2.1.le) h2.2.2.le]⟩
    · exact ⟨le_rfl, le_rfl⟩

/-- `limitGp` / `limitRcm`: the year's share of a saldo if above 0, else 0. -/
def limitOf (ρ x : ℚ) : ℚ := if 0 < x then x * ρ else 0

/-- Fase 1: this year's negative saldo of one kind off the other's positive saldo, within the limit. -/
structure Ph1 where
  gp : ℚ
  rcm : ℚ
  rcmOffGp : ℚ
  gpOffRcm : ℚ

def phase1 (ρ gp0 rcm0 : ℚ) : Ph1 :=
  let a := if rcm0 < 0 ∧ 0 < gp0 then min (-rcm0) (limitOf ρ gp0) else 0
  let b := if gp0 - a < 0 ∧ 0 < rcm0 + a then min (-(gp0 - a)) (limitOf ρ rcm0) else 0
  ⟨gp0 - a + b, rcm0 + a - b, a, b⟩

/-- Only negative saldos of the four years before can still be used. -/
def window (year : ℤ) (ps : List Pending) : List Pending :=
  ps.filter fun p => decide (year - 4 ≤ p.yr ∧ p.yr < year)

def start (ρ gp0 rcm0 : ℚ) : St :=
  ⟨(phase1 ρ gp0 rcm0).gp, (phase1 ρ gp0 rcm0).rcm, 0, 0, 0, 0,
    limitOf ρ gp0 - (phase1 ρ gp0 rcm0).rcmOffGp, limitOf ρ rcm0 - (phase1 ρ gp0 rcm0).gpOffRcm⟩

/-- After Fase 2, 1º and 2º. -/
def passes (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) : St × List Pending :=
  pass crossStep (pass ownStep (start ρ gp0 rcm0) (window year pend)).1
    (pass ownStep (start ρ gp0 rcm0) (window year pend)).2

def negPart (x : ℚ) : ℚ := if x < 0 then -x else 0

/-- What waits after the year, before taking out those whose time is up: what is left of earlier losses, then this
year's own negative saldos (gains first). -/
def newPending (year : ℤ) (c : St × List Pending) : List Pending :=
  c.2.filter (fun p => decide (0 < p.amount)) ++ (if c.1.gp < 0 then [⟨year, .gp, -c.1.gp⟩] else []) ++
    (if c.1.rcm < 0 then [⟨year, .rcm, -c.1.rcm⟩] else [])

structure YearOut where
  year : ℤ
  gp : ℚ
  rcm : ℚ
  rcmOffGp : ℚ
  gpOffRcm : ℚ
  usedGp : ℚ
  usedRcm : ℚ
  /-- Split of `usedGp` / `usedRcm`: earlier losses taken off the other kind's saldo (not a field of the code). -/
  crossGp : ℚ
  crossRcm : ℚ
  gpBase : ℚ
  rcmBase : ℚ
  base : ℚ
  pendingIn : ℚ
  pending : List Pending
  expired : ℚ
  /-- This year's own negative saldos left after this year's offsets (pushed onto `pending` in the code). -/
  made : ℚ

/-- One year of `esSavings` with a cross rate (2015 on). -/
def yearStep (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) : YearOut :=
  let c := passes ρ year gp0 rcm0 pend
  let n := newPending year c
  { year := year, gp := gp0, rcm := rcm0, rcmOffGp := (phase1 ρ gp0 rcm0).rcmOffGp,
    gpOffRcm := (phase1 ρ gp0 rcm0).gpOffRcm, usedGp := c.1.ownGp + c.1.crossGp,
    usedRcm := c.1.ownRcm + c.1.crossRcm, crossGp := c.1.crossGp, crossRcm := c.1.crossRcm,
    gpBase := max c.1.gp 0, rcmBase := max c.1.rcm 0, base := max c.1.gp 0 + max c.1.rcm 0,
    pendingIn := psum (window year pend), pending := n.filter (fun p => decide (year - 4 < p.yr)),
    expired := psum (n.filter (fun p => decide (p.yr ≤ year - 4))), made := negPart c.1.gp + negPart c.1.rcm }

theorem psum_append (a b : List Pending) : psum (a ++ b) = psum a + psum b := by simp [psum]

theorem psum_split (f : Pending → Bool) (l : List Pending) :
    psum (l.filter f) + psum (l.filter fun p => !f p) = psum l := by
  induction l with
  | nil => simp [psum]
  | cons p l ih => unfold psum at *; cases h : f p <;> simp [h] at ih ⊢ <;> linarith

theorem psum_pos (l : List Pending) (h : ∀ p ∈ l, 0 ≤ p.amount) :
    psum (l.filter fun p => decide (0 < p.amount)) = psum l := by
  induction l with
  | nil => simp [psum]
  | cons p l ih =>
    have ih := ih (fun q hq => h q (by simp [hq])); unfold psum at *
    by_cases hp : 0 < p.amount
    · simp [hp, ih]
    · have : p.amount = 0 := le_antisymm (not_lt.mp hp) (h p (by simp))
      simp [ih, this]

theorem window_nonneg (year : ℤ) (pend : List Pending) (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    ∀ p ∈ window year pend, 0 ≤ p.amount := fun p hp => h p (List.mem_filter.mp hp).1

theorem passes_nonneg (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    ∀ q ∈ (passes ρ year gp0 rcm0 pend).2, 0 ≤ q.amount :=
  pass_nonneg crossStep crossStep_bounds _ _
    (pass_nonneg ownStep ownStep_bounds _ _ (window_nonneg year pend h))

/-- **ES-5** Art. 49, one year: earlier losses waiting at the start (of the four years before) plus this year's own
negative saldos left after this year's offsets = losses used this year + losses whose four years ran out + losses still
waiting. -/
theorem year_conserves (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    let o := yearStep ρ year gp0 rcm0 pend
    o.pendingIn + o.made = o.usedGp + o.usedRcm + o.expired + psum o.pending := by
  intro o
  have key : psum (passes ρ year gp0 rcm0 pend).2 + (passes ρ year gp0 rcm0 pend).1.used = psum (window year pend) := by
    have e1 := pass_sum ownStep ownStep_used (start ρ gp0 rcm0) (window year pend)
    have e2 := pass_sum crossStep crossStep_used (pass ownStep (start ρ gp0 rcm0) (window year pend)).1
      (pass ownStep (start ρ gp0 rcm0) (window year pend)).2
    have : (start ρ gp0 rcm0).used = 0 := by simp [start, St.used]
    simp only [passes]; linarith
  have e3 := psum_pos _ (passes_nonneg ρ year gp0 rcm0 pend h)
  have e4 := psum_split (fun p => decide (p.yr ≤ year - 4)) (newPending year (passes ρ year gp0 rcm0 pend))
  have e5 : (fun p : Pending => !decide (p.yr ≤ year - 4)) = fun p => decide (year - 4 < p.yr) := by
    funext p; by_cases hp : p.yr ≤ year - 4 <;> simp [hp] <;> omega
  rw [e5] at e4
  simp only [o, yearStep]
  generalize passes ρ year gp0 rcm0 pend = c at key e3 e4 ⊢
  have e6 : psum (newPending year c) = psum c.2 + negPart c.1.gp + negPart c.1.rcm := by
    unfold newPending negPart; rw [psum_append, psum_append, e3]; split_ifs <;> simp [psum]
  unfold St.used at key; linarith

/-- **ES-5** Art. 49, the limit: this year's negative capital income taken off gains (art. 49.1.a) plus earlier
years' capital-income losses taken off gains (49.2, 2º) never exceed the year's share (25% from 2018) of the positive
gains saldo; the same the other way round. -/
theorem cross_within_limit (ρ : ℚ) (hρ : 0 ≤ ρ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) :
    let o := yearStep ρ year gp0 rcm0 pend
    0 ≤ o.crossRcm ∧ 0 ≤ o.crossGp ∧ o.rcmOffGp + o.crossRcm ≤ ρ * max gp0 0 ∧
      o.gpOffRcm + o.crossGp ≤ ρ * max rcm0 0 := by
  intro o
  have hl : ∀ x, limitOf ρ x = ρ * max x 0 := by
    intro x; unfold limitOf; split_ifs with hx
    · rw [max_eq_left hx.le]; ring
    · rw [max_eq_right (not_lt.mp hx)]; ring
  have hl0 : ∀ x, 0 ≤ limitOf ρ x := fun x => by rw [hl]; exact mul_nonneg hρ (le_max_right _ _)
  have ha : 0 ≤ limitOf ρ gp0 - (phase1 ρ gp0 rcm0).rcmOffGp := by
    simp only [phase1]; split_ifs
    · linarith [min_le_right (-rcm0) (limitOf ρ gp0)]
    · linarith [hl0 gp0]
  have hb : 0 ≤ limitOf ρ rcm0 - (phase1 ρ gp0 rcm0).gpOffRcm := by
    simp only [phase1]; split_ifs <;> first | exact sub_nonneg.mpr (min_le_right _ _) | linarith [hl0 rcm0]
  let P : St → Prop := fun s => s.roomGp + s.crossRcm = limitOf ρ gp0 - (phase1 ρ gp0 rcm0).rcmOffGp ∧
    s.roomRcm + s.crossGp = limitOf ρ rcm0 - (phase1 ρ gp0 rcm0).gpOffRcm ∧ 0 ≤ s.roomGp ∧ 0 ≤ s.roomRcm ∧
    s.roomGp ≤ limitOf ρ gp0 - (phase1 ρ gp0 rcm0).rcmOffGp ∧ s.roomRcm ≤ limitOf ρ rcm0 - (phase1 ρ gp0 rcm0).gpOffRcm
  have hP : ∀ step, (step = ownStep ∨ step = crossStep) → ∀ (ps : List Pending) s, P s → P (pass step s ps).1 :=
    fun step hs ps s h0 => pass_inv step P s ps (fun s p _ ⟨a, b, c, d, e, f⟩ => by
      obtain ⟨a', b', c', d'⟩ := steps_room step hs s p
      obtain ⟨hc, hd⟩ := steps_cross_mono step hs s p
      exact ⟨by linarith, by linarith, c' c, d' d, by linarith, by linarith⟩) h0
  have h0 : P (start ρ gp0 rcm0) := ⟨by simp [start], by simp [start], ha, hb, le_rfl, le_rfl⟩
  have hf := hP crossStep (Or.inr rfl) (pass ownStep (start ρ gp0 rcm0) (window year pend)).2 _
    (hP ownStep (Or.inl rfl) (window year pend) _ h0)
  obtain ⟨a, b, c, d, e, f⟩ := hf
  simp only [o, yearStep, passes] at *
  rw [← hl, ← hl]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **ES-5** Art. 49.2, oldest first: among the earlier losses that can be used this year (in the order kept, oldest
first), if one is left over after the year, no later one of the same kind was touched. -/
theorem oldest_first (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    ((window year pend).zip (passes ρ year gp0 rcm0 pend).2).Pairwise
      (fun a b => a.1.kind = b.1.kind → 0 < a.2.amount → b.2.amount = b.1.amount) := by
  set w := window year pend
  set s0 := start ρ gp0 rcm0
  have hw := window_nonneg year pend h
  have l1 : (pass ownStep s0 w).2.length = w.length := pass_length _ _ _
  have l2 : (passes ρ year gp0 rcm0 pend).2.length = (pass ownStep s0 w).2.length := pass_length _ _ _
  have A := pass_oldest ownStep (fun s k => s.own k ≤ 0) ownStep_oldest.1 ownStep_oldest.2.1 ownStep_oldest.2.2 s0 w
  have B := pass_oldest crossStep crossBlocked crossStep_oldest.1 crossStep_oldest.2.1 crossStep_oldest.2.2
    (pass ownStep s0 w).1 (pass ownStep s0 w).2
  have hn := pass_nonneg ownStep ownStep_bounds s0 w hw
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_zip] at hi hj
  have hi' : i < w.length := by omega
  have hj' : j < w.length := by omega
  simp only [List.getElem_zip]
  intro hk hpos
  have a1 := zip_pairwise_get _ w (pass ownStep s0 w).2 l1 A i j hi' hj' hij
  have b1 := zip_pairwise_get _ (pass ownStep s0 w).2 (passes ρ year gp0 rcm0 pend).2 l2 B i j (by omega) (by omega) hij
  have ki := (pass_get ownStep s0 w i hi').2
  have kj := (pass_get ownStep s0 w j hj').2
  have bi := pass_get_bounds crossStep crossStep_bounds (pass ownStep s0 w).1 (pass ownStep s0 w).2 hn i (by omega)
  simp only at a1 b1 bi
  have e1 := b1 (by rw [ki, kj]; exact hk) hpos
  have e2 := a1 hk (lt_of_lt_of_le hpos bi.2)
  simp only [passes] at e1 ⊢
  rw [e1, e2]

/-- Art. 49.1, the four years: the losses that can be used in a year are exactly those waiting from the four years
before it. -/
theorem window_mem (year : ℤ) (pend : List Pending) (p : Pending) :
    p ∈ window year pend ↔ p ∈ pend ∧ year - 4 ≤ p.yr ∧ p.yr < year := by
  simp [window]

/-- **ES-5** Art. 49.1, gone after four years: what waits after a year is from that year or the three before it (a
loss of year `Y` is used in `Y + 1 … Y + 4` at most and then goes into `expired`), each above 0. -/
theorem pending_window (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) :
    ∀ q ∈ (yearStep ρ year gp0 rcm0 pend).pending, year - 4 < q.yr ∧ q.yr ≤ year ∧ 0 < q.amount := by
  intro q hq
  simp only [yearStep, List.mem_filter, decide_eq_true_eq] at hq
  obtain ⟨hq, h4⟩ := hq
  refine ⟨h4, ?_⟩
  simp only [newPending, List.mem_append, List.mem_filter, decide_eq_true_eq] at hq
  rcases hq with (⟨hq, hpos⟩ | hq) | hq
  · obtain ⟨p1, hp1, e1, -⟩ := pass_mem _ _ _ q hq
    obtain ⟨p0, hp0, e0, -⟩ := pass_mem _ _ _ p1 hp1
    have := ((window_mem year pend p0).mp hp0).2.2
    exact ⟨by omega, hpos⟩
  · split_ifs at hq with hg
    · simp at hq; subst hq; exact ⟨le_rfl, by simp; linarith⟩
    · simp at hq
  · split_ifs at hq with hg
    · simp at hq; subst hq; exact ⟨le_rfl, by simp; linarith⟩
    · simp at hq

/-- The losses waiting stay in year order (the code sorts them once, then keeps the order and adds the year's own at
the end), so "oldest first" by place in the list is oldest first by year. -/
theorem pending_sorted (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending)
    (h : pend.Pairwise fun a b => a.yr ≤ b.yr) :
    (yearStep ρ year gp0 rcm0 pend).pending.Pairwise fun a b => a.yr ≤ b.yr := by
  have hw : (window year pend).Pairwise fun a b => a.yr ≤ b.yr := h.filter _
  have hy : ∀ step s (ps : List Pending), ps.Pairwise (fun a b => a.yr ≤ b.yr) →
      (pass step s ps).2.Pairwise fun a b => a.yr ≤ b.yr := by
    intro step s ps hp
    have := pass_yrs step s ps
    rw [← List.pairwise_map (R := fun a b : ℤ => a ≤ b)] at hp ⊢
    rwa [this]
  have hc := hy crossStep (pass ownStep (start ρ gp0 rcm0) (window year pend)).1
    (pass ownStep (start ρ gp0 rcm0) (window year pend)).2 (hy ownStep _ _ hw)
  simp only [yearStep]
  refine List.Pairwise.filter _ ?_
  simp only [newPending]
  refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hc.filter _, ?_, ?_⟩, ?_, ?_⟩
  · split_ifs <;> simp
  · intro a ha b hb
    split_ifs at hb
    · simp at hb; subst hb
      obtain ⟨p1, hp1, e1, -⟩ := pass_mem _ _ _ a (List.mem_filter.mp ha).1
      obtain ⟨p0, hp0, e0, -⟩ := pass_mem _ _ _ p1 hp1
      have := ((window_mem year pend p0).mp hp0).2.2
      simp; omega
    · simp at hb
  · split_ifs <;> simp
  · intro a ha b hb
    split_ifs at hb
    · simp at hb; subst hb
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p1, hp1, e1, -⟩ := pass_mem _ _ _ a (List.mem_filter.mp ha).1
        obtain ⟨p0, hp0, e0, -⟩ := pass_mem _ _ _ p1 hp1
        have := ((window_mem year pend p0).mp hp0).2.2
        simp; omega
      · split_ifs at ha
        · simp at ha; subst ha; simp
        · simp at ha
    · simp at hb

/-- `esCrossRate`: the share of the other saldo a negative saldo can come off; none before 2015. -/
def crossRate (y : ℤ) : Option ℚ :=
  if y < 2015 then none else if y = 2015 then some (1 / 10) else if y = 2016 then some (15 / 100)
  else if y = 2017 then some (1 / 5) else some (1 / 4)

/-- A year before 2015: the saldos above 0 go in, nothing is offset or carried (the losses waiting pass through).
Negative saldos of 2011-2014 (DT 7ª LIRPF) are then treated as ordinary losses waiting; their four-year carry ends by
2018, so this changes no later year. -/
def preYear (y : ℤ) (gp rcm : ℚ) : YearOut :=
  { year := y, gp := gp, rcm := rcm, rcmOffGp := 0, gpOffRcm := 0, usedGp := 0, usedRcm := 0, crossGp := 0,
    crossRcm := 0, gpBase := max gp 0, rcmBase := max rcm 0, base := max gp 0 + max rcm 0, pendingIn := 0,
    pending := [], expired := 0, made := 0 }

/-- `esSavings` over `n` years from `y`, `f` giving each year's two saldos (0 for a year not given). Returns the
years and what still waits after the last. -/
def run (f : ℤ → ℚ × ℚ) : ℤ → ℕ → List Pending → List YearOut × List Pending
  | _, 0, pend => ([], pend)
  | y, n + 1, pend =>
    match crossRate y with
    | none => (preYear y (f y).1 (f y).2 :: (run f (y + 1) n pend).1, (run f (y + 1) n pend).2)
    | some ρ => (yearStep ρ y (f y).1 (f y).2 pend :: (run f (y + 1) n (yearStep ρ y (f y).1 (f y).2 pend).pending).1,
        (run f (y + 1) n (yearStep ρ y (f y).1 (f y).2 pend).pending).2)

theorem window_all (year : ℤ) (pend : List Pending) (h : ∀ p ∈ pend, year - 4 ≤ p.yr ∧ p.yr < year) :
    window year pend = pend := List.filter_eq_self.mpr fun p hp => by simpa using h p hp

/-! ### Art. 49.2, "cuantía máxima": a loss still waits only when nothing more could be taken -/

theorem pass_carry (step : St → Pending → St × ℚ) (B : St → Kind → Prop)
    (h2 : ∀ s p k, B s k → B (step s p).1 k) (hs : ∀ s p, 0 ≤ p.amount → 0 ≤ (step s p).2) (s : St)
    (ps : List Pending) (hn : ∀ p ∈ ps, 0 ≤ p.amount) (hin : ∀ p ∈ ps, 0 < p.amount → B s p.kind) :
    ∀ q ∈ (pass step s ps).2, 0 < q.amount → B (pass step s ps).1 q.kind := by
  induction ps generalizing s with
  | nil => simp [pass]
  | cons p ps ih =>
    intro q hq hpos
    simp only [pass, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have h0 := hs s p (hn p (by simp))
      have hp : 0 < p.amount := by simp at hpos; linarith
      exact pass_inv step (fun t => B t p.kind) _ ps (fun t x _ hb => h2 t x _ hb) (h2 s p _ (hin p (by simp) hp))
    · exact ih (step s p).1 (fun x hx => hn x (by simp [hx]))
        (fun x hx hx' => h2 s p _ (hin x (by simp [hx]) hx')) q hq hpos

theorem pass_left (step : St → Pending → St × ℚ) (B : St → Kind → Prop)
    (h2 : ∀ s p k, B s k → B (step s p).1 k) (h3 : ∀ s p, 0 < p.amount - (step s p).2 → B (step s p).1 p.kind)
    (s : St) (ps : List Pending) : ∀ q ∈ (pass step s ps).2, 0 < q.amount → B (pass step s ps).1 q.kind := by
  induction ps generalizing s with
  | nil => simp [pass]
  | cons p ps ih =>
    intro q hq hpos
    simp only [pass, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact pass_inv step (fun t => B t p.kind) _ ps (fun t x _ hb => h2 t x _ hb) (h3 s p hpos)
    · exact ih _ q hq hpos

theorem crossStep_keeps_own (s : St) (p : Pending) (k : Kind) (h : s.own k ≤ 0) : (crossStep s p).1.own k ≤ 0 := by
  unfold crossStep; split_ifs with h0 h1 h2
  · exact h
  · push_neg at h0
    have : 0 ≤ min (min p.amount s.gp) s.roomGp := le_min (le_min h0.le h1.2.1.le) h1.2.2.le
    cases k <;> simp only [St.own, takeCrossRcm] at h ⊢ <;> linarith
  · push_neg at h0
    have : 0 ≤ min (min p.amount s.rcm) s.roomRcm := le_min (le_min h0.le h2.2.1.le) h2.2.2.le
    cases k <;> simp only [St.own, takeCrossGp] at h ⊢ <;> linarith
  · exact h

/-- **ES-5** Art. 49.2, each earlier loss used "up to the maximum amount" (cuantía máxima): after the year's two
passes, a loss of the four years before with something left has its own kind's saldo used up (not above 0), and its
use against the other saldo stopped because that saldo is not above 0 or the room left in that year's limit (25%; 10,
15, 20% in 2015-2017, net of what phase 1 already took) is used up. -/
theorem cuantia_maxima (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    let c := passes ρ year gp0 rcm0 pend
    ∀ q ∈ c.2, 0 < q.amount → c.1.own q.kind ≤ 0 ∧ crossBlocked c.1 q.kind := by
  intro c q hq hpos
  set w := window year pend
  set s0 := start ρ gp0 rcm0
  have hw := window_nonneg year pend h
  have hn := pass_nonneg ownStep ownStep_bounds s0 w hw
  have A := pass_left ownStep (fun s k => s.own k ≤ 0) ownStep_oldest.2.1 ownStep_oldest.2.2 s0 w
  refine ⟨?_, ?_⟩
  · exact pass_carry crossStep (fun s k => s.own k ≤ 0) (fun s p k hk => crossStep_keeps_own s p k hk)
      (fun s p hp => (crossStep_bounds s p hp).1) _ _ hn A q hq hpos
  · exact pass_left crossStep crossBlocked crossStep_oldest.2.1 crossStep_oldest.2.2 _ _ q hq hpos

/-- **ES-5** The same on the year's output: a loss still waiting after the year that is from an earlier year (not
this year's own negative saldo) means the saldo of its own kind ended not above 0, and the other saldo ended not above
0 or the room left in its limit is used up. -/
theorem cuantia_maxima_year (ρ : ℚ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending) (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    let c := passes ρ year gp0 rcm0 pend
    ∀ q ∈ (yearStep ρ year gp0 rcm0 pend).pending, q.yr < year →
      c.1.own q.kind ≤ 0 ∧ crossBlocked c.1 q.kind := by
  intro c q hq hy
  simp only [yearStep, List.mem_filter, decide_eq_true_eq] at hq
  obtain ⟨hq, -⟩ := hq
  simp only [newPending, List.mem_append, List.mem_filter, decide_eq_true_eq] at hq
  rcases hq with (⟨hq, hpos⟩ | hq) | hq
  · exact cuantia_maxima ρ year gp0 rcm0 pend h q hq hpos
  · split_ifs at hq <;> simp at hq; subst hq; simp at hy
  · split_ifs at hq <;> simp at hq; subst hq; simp at hy

/-- **ES-5** Art. 49 over the years (2015 on, starting with losses of the four years before, each not below 0):
losses waiting at the start plus every year's own losses = all used + all whose time ran out + what still waits. -/
theorem run_conserves (f : ℤ → ℚ × ℚ) (y : ℤ) (n : ℕ) (pend : List Pending) (hy : 2015 ≤ y)
    (hw : ∀ p ∈ pend, y - 4 ≤ p.yr ∧ p.yr < y) (h0 : ∀ p ∈ pend, 0 ≤ p.amount) :
    psum pend + ((run f y n pend).1.map YearOut.made).sum =
      ((run f y n pend).1.map fun o => o.usedGp + o.usedRcm + o.expired).sum + psum (run f y n pend).2 := by
  induction n generalizing y pend with
  | zero => simp [run]
  | succ n ih =>
    have hr : ∃ ρ, crossRate y = some ρ := by
      unfold crossRate; split_ifs <;> first | omega | exact ⟨_, rfl⟩
    obtain ⟨ρ, hρ⟩ := hr
    simp only [run, hρ, List.map_cons, List.sum_cons]
    have c : (yearStep ρ y (f y).1 (f y).2 pend).pendingIn + (yearStep ρ y (f y).1 (f y).2 pend).made =
        (yearStep ρ y (f y).1 (f y).2 pend).usedGp + (yearStep ρ y (f y).1 (f y).2 pend).usedRcm +
          (yearStep ρ y (f y).1 (f y).2 pend).expired + psum (yearStep ρ y (f y).1 (f y).2 pend).pending :=
      year_conserves ρ y (f y).1 (f y).2 pend h0
    have hin : (yearStep ρ y (f y).1 (f y).2 pend).pendingIn = psum pend := by
      simp only [yearStep]; rw [window_all y pend hw]
    have pw := pending_window ρ y (f y).1 (f y).2 pend
    have := ih (y + 1) _ (by omega) (fun p hp => by have := pw p hp; omega) (fun p hp => (pw p hp).2.2.le)
    linarith

/-- `esSavings`: the losses given at the start sorted by year (stable), then year by year. -/
def savings (f : ℤ → ℚ × ℚ) (y : ℤ) (n : ℕ) (pendIn : List Pending) : List YearOut × List Pending :=
  run f y n (pendIn.mergeSort fun a b => decide (a.yr ≤ b.yr))

/-! ## 6. The savings scale (arts. 66 and 76 LIRPF, state plus regional) and its tax (`esSavingsTax`) -/

/-- One band: up to `upTo` (none: no top), at `rate`. -/
structure Band where
  upTo : Option ℚ
  rate : ℚ

/-- `esScale`, combined state plus regional rates. -/
def scale (y : ℤ) : Option (List Band) :=
  if y < 2015 then none
  else if y = 2015 then some [⟨some 6000, 195 / 1000⟩, ⟨some 50000, 215 / 1000⟩, ⟨none, 235 / 1000⟩]
  else if y ≤ 2020 then some [⟨some 6000, 19 / 100⟩, ⟨some 50000, 21 / 100⟩, ⟨none, 23 / 100⟩]
  else if y ≤ 2022 then some [⟨some 6000, 19 / 100⟩, ⟨some 50000, 21 / 100⟩, ⟨some 200000, 23 / 100⟩, ⟨none, 26 / 100⟩]
  else if y ≤ 2024 then
    some [⟨some 6000, 19 / 100⟩, ⟨some 50000, 21 / 100⟩, ⟨some 200000, 23 / 100⟩, ⟨some 300000, 27 / 100⟩,
      ⟨none, 28 / 100⟩]
  else
    some [⟨some 6000, 19 / 100⟩, ⟨some 50000, 21 / 100⟩, ⟨some 200000, 23 / 100⟩, ⟨some 300000, 27 / 100⟩,
      ⟨none, 30 / 100⟩]

/-- The loop over the bands from `lo`: stop once the base is at or below the band's start; tax the part of the
base in the band. -/
def bandTax (base : ℚ) : ℚ → List Band → ℚ
  | _, [] => 0
  | lo, b :: bs =>
    if base ≤ lo then 0
    else match b.upTo with
      | none => (base - lo) * b.rate
      | some u => (min base u - lo) * b.rate + bandTax base u bs

/-- `centsUp`: up to the cent (ROUND_CEIL). -/
def centsUp (x : ℚ) : ℚ := (⌈x * 100⌉ : ℚ) / 100

/-- `esSavingsTax`: none before 2015. -/
def savingsTax (y : ℤ) (base : ℚ) : Option ℚ := (scale y).map fun bs => centsUp (bandTax base 0 bs)

/-- Rates not below 0 and each band's top not below its start. -/
def WF : ℚ → List Band → Prop
  | _, [] => True
  | lo, b :: bs => 0 ≤ b.rate ∧ match b.upTo with
    | none => True
    | some u => lo ≤ u ∧ WF u bs

theorem scale_wf (y : ℤ) (bs : List Band) (h : scale y = some bs) : WF 0 bs := by
  unfold scale at h
  split_ifs at h <;> (try cases h) <;> simp only [WF] <;> norm_num

theorem bandTax_nonneg (base lo : ℚ) (bs : List Band) (h : WF lo bs) : 0 ≤ bandTax base lo bs := by
  induction bs generalizing lo with
  | nil => simp [bandTax]
  | cons b bs ih =>
    unfold bandTax; split_ifs with hb
    · exact le_rfl
    · push_neg at hb
      obtain ⟨hr, hu⟩ := h
      cases hbu : b.upTo with
      | none => exact mul_nonneg (by linarith) hr
      | some u =>
        rw [hbu] at hu
        exact add_nonneg (mul_nonneg (by simp; exact ⟨hb.le, hu.1⟩) hr) (ih u hu.2)

theorem bandTax_mono (base base' lo : ℚ) (bs : List Band) (h : WF lo bs) (hb : base ≤ base') :
    bandTax base lo bs ≤ bandTax base' lo bs := by
  induction bs generalizing lo with
  | nil => simp [bandTax]
  | cons b bs ih =>
    have h0 := bandTax_nonneg base' lo (b :: bs) h
    unfold bandTax at h0 ⊢
    split_ifs at h0 ⊢ with h1 h2
    · exact le_rfl
    · exact h0
    · linarith
    · obtain ⟨hr, hu⟩ := h
      cases hbu : b.upTo with
      | none => exact mul_le_mul_of_nonneg_right (by linarith) hr
      | some u =>
        rw [hbu] at hu
        exact add_le_add (mul_le_mul_of_nonneg_right (by linarith [min_le_min_right u hb]) hr) (ih u hu.2)

theorem centsUp_mono {x y : ℚ} (h : x ≤ y) : centsUp x ≤ centsUp y := by
  unfold centsUp
  have : ⌈x * 100⌉ ≤ ⌈y * 100⌉ := Int.ceil_mono (by linarith)
  have : ((⌈x * 100⌉ : ℤ) : ℚ) ≤ ((⌈y * 100⌉ : ℤ) : ℚ) := by exact_mod_cast this
  linarith

theorem centsUp_nonneg {x : ℚ} (h : 0 ≤ x) : 0 ≤ centsUp x := by
  have := centsUp_mono h
  have e : centsUp 0 = 0 := by simp [centsUp]
  linarith

/-- **ES-6** Arts. 66 and 76: from 2015 the savings tax is not below 0 and never falls as the base rises. -/
theorem savingsTax_spec (y : ℤ) (hy : 2015 ≤ y) :
    ∃ t : ℚ → ℚ, (∀ b, savingsTax y b = some (t b)) ∧ (∀ b, 0 ≤ t b) ∧ ∀ b b', b ≤ b' → t b ≤ t b' := by
  obtain ⟨bs, hbs⟩ : ∃ bs, scale y = some bs := by
    unfold scale; split_ifs <;> first | omega | exact ⟨_, rfl⟩
  have hw := scale_wf y bs hbs
  refine ⟨fun b => centsUp (bandTax b 0 bs), fun b => by simp [savingsTax, hbs], fun b => ?_, fun b b' h => ?_⟩
  · exact centsUp_nonneg (bandTax_nonneg b 0 bs hw)
  · exact centsUp_mono (bandTax_mono b b' 0 bs hw h)

/-- **ES-6** The AEAT's own figures: base 2,800 → 532 and base 130,000 → 28,780 (Renta 2024); the band edges
in 2025 and the 2024/2025 top rates. -/
theorem savingsTax_aeat :
    savingsTax 2024 2800 = some 532 ∧ savingsTax 2024 130000 = some 28780 ∧
      savingsTax 2025 2800 = some 532 ∧ savingsTax 2025 130000 = some 28780 ∧
      savingsTax 2025 6000 = some 1140 ∧ savingsTax 2025 50000 = some 10380 ∧
      savingsTax 2025 200000 = some 44880 ∧ savingsTax 2025 300000 = some 71880 ∧
      savingsTax 2025 400000 = some 101880 ∧ savingsTax 2024 400000 = some 99880 ∧
      savingsTax 2014 1000 = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [savingsTax, scale, bandTax, centsUp]

/-! ## 7. The tax if sold today (`esYearTax`, `esTaxOnSale`) -/

/-- `esYearTax`: the year's savings tax under art. 49 with the losses carried in; 0 before 2015. -/
def yearTax (y : ℤ) (gp rcm : ℚ) (carried : List Pending) : ℚ :=
  (((savings (fun _ => (gp, rcm)) y 1 carried).1.head?).bind fun o => savingsTax y o.base).getD 0

/-- `esTaxOnSale`: the year's tax with one more gain less the tax without it, never below 0. -/
def taxOnSale (gain : ℚ) (y : ℤ) (gp rcm : ℚ) (carried : List Pending) : ℚ :=
  max (yearTax y (gp + gain) rcm carried - yearTax y gp rcm carried) 0

/-- **ES-7** The tax if sold today is not below 0, and is the year's tax with the sale less the tax without it
whenever that is not below 0 (see `taxOnSale_eq` for when it always is). -/
theorem taxOnSale_spec (gain : ℚ) (y : ℤ) (gp rcm : ℚ) (carried : List Pending) :
    0 ≤ taxOnSale gain y gp rcm carried ∧
      (yearTax y gp rcm carried ≤ yearTax y (gp + gain) rcm carried →
        taxOnSale gain y gp rcm carried = yearTax y (gp + gain) rcm carried - yearTax y gp rcm carried) :=
  ⟨le_max_right _ _, fun h => max_eq_left (by linarith)⟩

/-- **ES-5/ES-7** The AEAT Manual Renta 2024, ch. 12, Caso práctico (as in the app's tests): 2024 gains 4,000,
capital income −800, waiting gains losses of 700 (2020) and 2,100 (2021) and capital-income loss 500 (2020). The
−800 comes off the gains (800, within 25% of 4,000), the gains losses are used in full (2,800), 200 of the
capital-income loss within the 200 left of the 25%, base 200, the other 300 of it expires with 2024; nothing waits. -/
theorem aeat_ch12 :
    let o := yearStep (1 / 4) 2024 4000 (-800)
      ([⟨2020, .gp, 700⟩, ⟨2021, .gp, 2100⟩, ⟨2020, .rcm, 500⟩].mergeSort fun a b => decide (a.yr ≤ b.yr))
    o.rcmOffGp = 800 ∧ o.usedGp = 2800 ∧ o.usedRcm = 200 ∧ o.base = 200 ∧ o.expired = 300 ∧ o.pending = [] ∧
      savingsTax 2024 o.base = some 38 := by
  have hs : ([⟨2020, .gp, 700⟩, ⟨2021, .gp, 2100⟩, ⟨2020, .rcm, 500⟩] : List Pending).mergeSort
      (fun a b => decide (a.yr ≤ b.yr)) = [⟨2020, .gp, 700⟩, ⟨2020, .rcm, 500⟩, ⟨2021, .gp, 2100⟩] := by
    simp [List.mergeSort]
  intro o
  simp only [o, hs]
  norm_num [yearStep, passes, start, phase1, limitOf, window, pass, ownStep, crossStep, St.own, takeOwn,
    takeCrossRcm, takeCrossGp, newPending, negPart, psum, savingsTax, scale, bandTax, centsUp]

/-- **ES-7** The app's tests: 1,000 more gains on 5,500 in 2025 cost 200; with a 2023 loss of 600 carried and no
gains yet, 76; and a 2025 year with −1,000 gains and 1,000 capital income is taxed 142.50 (25% offset). -/
theorem taxOnSale_tests :
    taxOnSale 1000 2025 5500 0 [] = 200 ∧ taxOnSale 1000 2025 0 0 [⟨2023, .gp, 600⟩] = 76 ∧
      yearTax 2025 (-1000) 1000 [] = 285 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  norm_num [taxOnSale, yearTax, savings, run, crossRate, List.mergeSort, yearStep, passes, start, phase1, limitOf,
    window, pass, ownStep, crossStep, St.own, takeOwn, takeCrossRcm, takeCrossGp, newPending, negPart, psum,
    savingsTax, scale, bandTax, centsUp]

/-! ### The year's base never falls as gains rise -/

def kindSum (k : Kind) (ps : List Pending) : ℚ := ((ps.filter fun p => p.kind = k).map Pending.amount).sum

theorem kindSum_cons (k : Kind) (p : Pending) (ps : List Pending) :
    kindSum k (p :: ps) = (if p.kind = k then p.amount else 0) + kindSum k ps := by
  unfold kindSum; by_cases h : p.kind = k <;> simp [h]

theorem kindSum_nonneg (k : Kind) (ps : List Pending) (h : ∀ p ∈ ps, 0 ≤ p.amount) : 0 ≤ kindSum k ps :=
  List.sum_nonneg fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact h q (List.mem_filter.mp hq).1

theorem own_arith (g a P : ℚ) (hg : 0 < g) (ha : 0 ≤ a) (hP : 0 ≤ P) :
    g - min g a - min (max (g - min g a) 0) P = g - min (max g 0) (a + P) := by
  simp only [min_def, max_def]; split_ifs <;> linarith

theorem own_arith0 (g P : ℚ) (hg : g ≤ 0) (hP : 0 ≤ P) : g - min (max g 0) P = g := by
  simp only [min_def, max_def]; split_ifs <;> linarith

theorem cross_arith (g r a P : ℚ) (hg : 0 < g) (hr : 0 < r) (ha : 0 ≤ a) (hP : 0 ≤ P) :
    g - min (min a g) r - min (min P (max (g - min (min a g) r) 0)) (r - min (min a g) r) =
      g - min (min (a + P) (max g 0)) r := by
  simp only [min_def, max_def]; split_ifs <;> linarith

theorem cross_arith0 (g r P : ℚ) (h : g ≤ 0 ∨ r ≤ 0) (hr : 0 ≤ r) (hP : 0 ≤ P) :
    min (min P (max g 0)) r = 0 := by
  simp only [min_def, max_def]; split_ifs <;> rcases h with h | h <;> linarith

/-- Fase 2, 1º in closed form: each saldo above 0 loses as much of its own kind's losses as it can. -/
theorem own_agg (s : St) (ps : List Pending) (h : ∀ p ∈ ps, 0 ≤ p.amount) :
    (pass ownStep s ps).1.gp = s.gp - min (max s.gp 0) (kindSum .gp ps) ∧
      (pass ownStep s ps).1.rcm = s.rcm - min (max s.rcm 0) (kindSum .rcm ps) ∧
      kindSum .gp (pass ownStep s ps).2 = kindSum .gp ps - (s.gp - (pass ownStep s ps).1.gp) ∧
      kindSum .rcm (pass ownStep s ps).2 = kindSum .rcm ps - (s.rcm - (pass ownStep s ps).1.rcm) ∧
      (pass ownStep s ps).1.roomGp = s.roomGp ∧ (pass ownStep s ps).1.roomRcm = s.roomRcm := by
  induction ps generalizing s with
  | nil => simp [pass, kindSum]
  | cons p ps ih =>
    have hp := h p (by simp)
    have h' := fun q hq => h q (List.mem_cons_of_mem p hq)
    have n1 := kindSum_nonneg .gp ps h'
    have n2 := kindSum_nonneg .rcm ps h'
    cases hk : p.kind
    · by_cases hg : s.gp ≤ 0
      · have hs : ownStep s p = (s, 0) := by simp [ownStep, St.own, hk, hg]
        obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih s h'
        have e := own_arith0 _ _ hg n1
        have e' := own_arith0 _ _ hg (show 0 ≤ p.amount + kindSum .gp ps by linarith)
        simp only [pass, kindSum_cons, hs, hk, if_true, reduceCtorEq, if_false, zero_add, sub_zero] at *
        refine ⟨by linarith, by linarith, by linarith, by linarith, i5, i6⟩
      · push_neg at hg
        have hs : ownStep s p = (takeOwn s .gp (min s.gp p.amount), min s.gp p.amount) := by
          simp [ownStep, St.own, hk, not_le.mpr hg]
        obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (takeOwn s .gp (min s.gp p.amount)) h'
        have e := own_arith _ _ _ hg hp n1
        simp only [pass, kindSum_cons, hs, hk, if_true, reduceCtorEq, if_false, zero_add, takeOwn] at *
        refine ⟨by linarith, by linarith, by linarith, by linarith, i5, i6⟩
    · by_cases hg : s.rcm ≤ 0
      · have hs : ownStep s p = (s, 0) := by simp [ownStep, St.own, hk, hg]
        obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih s h'
        have e := own_arith0 _ _ hg n2
        have e' := own_arith0 _ _ hg (show 0 ≤ p.amount + kindSum .rcm ps by linarith)
        simp only [pass, kindSum_cons, hs, hk, if_true, reduceCtorEq, if_false, zero_add, sub_zero] at *
        refine ⟨by linarith, by linarith, by linarith, by linarith, i5, i6⟩
      · push_neg at hg
        have hs : ownStep s p = (takeOwn s .rcm (min s.rcm p.amount), min s.rcm p.amount) := by
          simp [ownStep, St.own, hk, not_le.mpr hg]
        obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (takeOwn s .rcm (min s.rcm p.amount)) h'
        have e := own_arith _ _ _ hg hp n2
        simp only [pass, kindSum_cons, hs, hk, if_true, reduceCtorEq, if_false, zero_add, takeOwn] at *
        refine ⟨by linarith, by linarith, by linarith, by linarith, i5, i6⟩

/-- Fase 2, 2º in closed form: each saldo above 0 loses as much of the other kind's losses left as it and the room
left in its limit allow. -/
theorem cross_agg (s : St) (ps : List Pending) (h : ∀ p ∈ ps, 0 ≤ p.amount) (hr1 : 0 ≤ s.roomGp)
    (hr2 : 0 ≤ s.roomRcm) :
    (pass crossStep s ps).1.gp = s.gp - min (min (kindSum .rcm ps) (max s.gp 0)) s.roomGp ∧
      (pass crossStep s ps).1.rcm = s.rcm - min (min (kindSum .gp ps) (max s.rcm 0)) s.roomRcm := by
  induction ps generalizing s with
  | nil => simp only [pass, kindSum, List.filter_nil, List.map_nil, List.sum_nil]; constructor <;>
      simp only [min_def, max_def] <;> split_ifs <;> linarith
  | cons p ps ih =>
    have hp := h p (by simp)
    have h' := fun q hq => h q (List.mem_cons_of_mem p hq)
    have n1 := kindSum_nonneg .gp ps h'
    have n2 := kindSum_nonneg .rcm ps h'
    by_cases h0 : p.amount ≤ 0
    · have ha : p.amount = 0 := le_antisymm h0 hp
      have hs : crossStep s p = (s, 0) := by simp [crossStep, h0]
      obtain ⟨i1, i2⟩ := ih s h' hr1 hr2
      simp only [pass, hs, kindSum_cons, ha, ite_self, zero_add]
      exact ⟨i1, i2⟩
    cases hk : p.kind
    · by_cases hc : 0 < s.rcm ∧ 0 < s.roomRcm
      · set m := min (min p.amount s.rcm) s.roomRcm
        have hs : crossStep s p = (takeCrossGp s m, m) := by simp [crossStep, h0, hk, hc, m]
        have hm : m ≤ s.roomRcm := min_le_right _ _
        obtain ⟨i1, i2⟩ := ih (takeCrossGp s m) h' (by simpa [takeCrossGp] using hr1)
          (by simp only [takeCrossGp]; linarith)
        have e := cross_arith _ _ _ _ hc.1 hc.2 hp n1
        simp only [pass, hs, kindSum_cons, hk, if_true, reduceCtorEq, if_false, zero_add, takeCrossGp] at *
        exact ⟨i1, by rw [i2]; exact e⟩
      · have hs : crossStep s p = (s, 0) := by simp [crossStep, h0, hk, hc]
        obtain ⟨i1, i2⟩ := ih s h' hr1 hr2
        have hc' : s.rcm ≤ 0 ∨ s.roomRcm ≤ 0 := by
          by_contra hh; push_neg at hh; exact hc hh
        have e := cross_arith0 _ _ _ hc' hr2 n1
        have e' := cross_arith0 _ _ _ hc' hr2 (show 0 ≤ p.amount + kindSum .gp ps by linarith)
        simp only [pass, hs, kindSum_cons, hk, if_true, reduceCtorEq, if_false, zero_add, sub_zero] at *
        exact ⟨i1, by rw [i2, e, e']⟩
    · by_cases hc : 0 < s.gp ∧ 0 < s.roomGp
      · set m := min (min p.amount s.gp) s.roomGp
        have hs : crossStep s p = (takeCrossRcm s m, m) := by simp [crossStep, h0, hk, hc, m]
        have hm : m ≤ s.roomGp := min_le_right _ _
        obtain ⟨i1, i2⟩ := ih (takeCrossRcm s m) h' (by simp only [takeCrossRcm]; linarith)
          (by simpa [takeCrossRcm] using hr2)
        have e := cross_arith _ _ _ _ hc.1 hc.2 hp n2
        simp only [pass, hs, kindSum_cons, hk, if_true, reduceCtorEq, if_false, zero_add, takeCrossRcm] at *
        exact ⟨by rw [i1]; exact e, i2⟩
      · have hs : crossStep s p = (s, 0) := by simp [crossStep, h0, hk, hc]
        obtain ⟨i1, i2⟩ := ih s h' hr1 hr2
        have hc' : s.gp ≤ 0 ∨ s.roomGp ≤ 0 := by
          by_contra hh; push_neg at hh; exact hc hh
        have e := cross_arith0 _ _ _ hc' hr1 n2
        have e' := cross_arith0 _ _ _ hc' hr1 (show 0 ≤ p.amount + kindSum .rcm ps by linarith)
        simp only [pass, hs, kindSum_cons, hk, if_true, reduceCtorEq, if_false, zero_add, sub_zero] at *
        exact ⟨by rw [i1, e, e'], i2⟩

theorem base_arith (G Pg P r : ℚ) (h1 : 0 ≤ Pg) (h2 : 0 ≤ P) (h3 : 0 ≤ r) :
    max (G - min (max G 0) Pg - min (min P (max (G - min (max G 0) Pg) 0)) r) 0 =
      max (max (G - Pg - P) (G - Pg - r)) 0 := by
  simp only [min_def, max_def]; split_ifs <;> linarith

theorem limitOf_eq (ρ x : ℚ) : limitOf ρ x = ρ * max x 0 := by
  unfold limitOf; split_ifs with hx
  · rw [max_eq_left hx.le]; ring
  · rw [max_eq_right (not_lt.mp hx)]; ring

/-- The year's base in closed form: what is left of each saldo above 0 after its own kind's losses and the other
kind's within the room left in its limit. -/
theorem base_formula (ρ : ℚ) (hρ : 0 ≤ ρ) (year : ℤ) (gp0 rcm0 : ℚ) (pend : List Pending)
    (h : ∀ p ∈ pend, 0 ≤ p.amount) :
    let Pg := kindSum .gp (window year pend)
    let Pr := kindSum .rcm (window year pend)
    let G := (phase1 ρ gp0 rcm0).gp
    let R := (phase1 ρ gp0 rcm0).rcm
    let rG := limitOf ρ gp0 - (phase1 ρ gp0 rcm0).rcmOffGp
    let rR := limitOf ρ rcm0 - (phase1 ρ gp0 rcm0).gpOffRcm
    (yearStep ρ year gp0 rcm0 pend).base =
      max (max (G - Pg - (Pr - min (max R 0) Pr)) (G - Pg - rG)) 0 +
        max (max (R - Pr - (Pg - min (max G 0) Pg)) (R - Pr - rR)) 0 := by
  intro Pg Pr G R rG rR
  have hw := window_nonneg year pend h
  have nPg : 0 ≤ Pg := kindSum_nonneg _ _ hw
  have nPr : 0 ≤ Pr := kindSum_nonneg _ _ hw
  have hl0 : ∀ x, 0 ≤ limitOf ρ x := fun x => by rw [limitOf_eq]; exact mul_nonneg hρ (le_max_right _ _)
  have ha : 0 ≤ rG := by
    simp only [rG, phase1]; split_ifs
    · exact sub_nonneg.mpr (min_le_right _ _)
    · linarith [hl0 gp0]
  have hb : 0 ≤ rR := by
    simp only [rR, phase1]; split_ifs <;> first | exact sub_nonneg.mpr (min_le_right _ _) | linarith [hl0 rcm0]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := own_agg (start ρ gp0 rcm0) (window year pend) hw
  have hn := pass_nonneg ownStep ownStep_bounds (start ρ gp0 rcm0) (window year pend) hw
  obtain ⟨c1, c2⟩ := cross_agg (pass ownStep (start ρ gp0 rcm0) (window year pend)).1
    (pass ownStep (start ρ gp0 rcm0) (window year pend)).2 hn (by rw [o5]; exact ha) (by rw [o6]; exact hb)
  have e1 := base_arith G Pg (Pr - min (max R 0) Pr) rG nPg (sub_nonneg.mpr (min_le_right _ _)) ha
  have e2 := base_arith R Pr (Pg - min (max G 0) Pg) rR nPr (sub_nonneg.mpr (min_le_right _ _)) hb
  rw [← e1, ← e2]
  show max (passes ρ year gp0 rcm0 pend).1.gp 0 + max (passes ρ year gp0 rcm0 pend).1.rcm 0 = _
  simp only [passes]
  rw [c1, c2, o3, o4, o5, o6, o1, o2]
  simp only [sub_sub_cancel]
  rfl

theorem terms_mono (Pg Pr G G' R R' rG rG' rR rR' : ℚ) (hG : G ≤ G') (hR : R ≤ R') (h1 : G - rG ≤ G' - rG')
    (h2 : R - rR ≤ R' - rR') :
    max (max (G - Pg - (Pr - min (max R 0) Pr)) (G - Pg - rG)) 0 +
        max (max (R - Pr - (Pg - min (max G 0) Pg)) (R - Pr - rR)) 0 ≤
      max (max (G' - Pg - (Pr - min (max R' 0) Pr)) (G' - Pg - rG')) 0 +
        max (max (R' - Pr - (Pg - min (max G' 0) Pg)) (R' - Pr - rR')) 0 := by
  have a := min_le_min_right Pr (max_le_max_right 0 hR)
  have b := min_le_min_right Pg (max_le_max_right 0 hG)
  exact add_le_add (max_le_max_right 0 (max_le_max (by linarith) (by linarith)))
    (max_le_max_right 0 (max_le_max (by linarith) (by linarith)))

theorem phase1_neg (ρ : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (gp0 rcm0 : ℚ) (hr : rcm0 < 0) :
    phase1 ρ gp0 rcm0 = ⟨gp0 - (if 0 < gp0 then min (-rcm0) (ρ * gp0) else 0),
      rcm0 + (if 0 < gp0 then min (-rcm0) (ρ * gp0) else 0),
      (if 0 < gp0 then min (-rcm0) (ρ * gp0) else 0), 0⟩ := by
  unfold phase1 limitOf
  dsimp only
  by_cases hg : 0 < gp0
  · have hm : min (-rcm0) (ρ * gp0) ≤ gp0 := (min_le_right _ _).trans (by nlinarith)
    simp only [hr, hg, and_self, if_true, mul_comm gp0 ρ]
    rw [if_neg (by intro hh; linarith [hh.1])]
    simp
  · simp only [hr, hg, and_false, if_false, sub_zero, add_zero]
    rw [if_neg (by intro hh; linarith [hh.2])]
    simp

theorem phase1_pos (ρ : ℚ) (gp0 rcm0 : ℚ) (hr : 0 ≤ rcm0) :
    phase1 ρ gp0 rcm0 = ⟨gp0 + (if gp0 < 0 ∧ 0 < rcm0 then min (-gp0) (ρ * rcm0) else 0),
      rcm0 - (if gp0 < 0 ∧ 0 < rcm0 then min (-gp0) (ρ * rcm0) else 0), 0,
      (if gp0 < 0 ∧ 0 < rcm0 then min (-gp0) (ρ * rcm0) else 0)⟩ := by
  unfold phase1 limitOf
  dsimp only
  rw [if_neg (by intro hh; linarith [hh.1])]
  simp only [sub_zero, add_zero]
  by_cases hc : gp0 < 0 ∧ 0 < rcm0
  · rw [if_pos hc, if_pos hc, if_pos hc.2, mul_comm]
  · rw [if_neg hc, if_neg hc]

/-- Phase 1 moves each figure the same way as the gains saldo, and never lets the room left fall faster. -/
theorem phase1_mono (ρ : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (gp0 gp0' rcm0 : ℚ) (hle : gp0 ≤ gp0') :
    (phase1 ρ gp0 rcm0).gp ≤ (phase1 ρ gp0' rcm0).gp ∧ (phase1 ρ gp0 rcm0).rcm ≤ (phase1 ρ gp0' rcm0).rcm ∧
      (phase1 ρ gp0 rcm0).gp - (limitOf ρ gp0 - (phase1 ρ gp0 rcm0).rcmOffGp) ≤
        (phase1 ρ gp0' rcm0).gp - (limitOf ρ gp0' - (phase1 ρ gp0' rcm0).rcmOffGp) ∧
      (phase1 ρ gp0 rcm0).rcm - (limitOf ρ rcm0 - (phase1 ρ gp0 rcm0).gpOffRcm) ≤
        (phase1 ρ gp0' rcm0).rcm - (limitOf ρ rcm0 - (phase1 ρ gp0' rcm0).gpOffRcm) := by
  have p3 : ρ * gp0 ≤ ρ * gp0' := mul_le_mul_of_nonneg_left hle hρ0
  have p4 : ρ * gp0' - ρ * gp0 ≤ gp0' - gp0 := by nlinarith
  by_cases hr : rcm0 < 0
  · rw [phase1_neg ρ hρ0 hρ1 gp0 rcm0 hr, phase1_neg ρ hρ0 hρ1 gp0' rcm0 hr]
    simp only [limitOf]
    rw [if_neg (not_lt.mpr hr.le)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> (try simp only [min_def]) <;> (try split_ifs) <;> nlinarith
  · push_neg at hr
    rw [phase1_pos ρ gp0 rcm0 hr, phase1_pos ρ gp0' rcm0 hr]
    simp only [limitOf]
    by_cases h0 : 0 < rcm0
    swap
    · simp only [h0, and_false, if_false]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> nlinarith
    simp only [h0, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> (try simp only [min_def]) <;> (try split_ifs) <;> nlinarith

/-- **ES-7** Art. 49 never makes more gains cost less: with a cross rate between 0 and 1 and the losses waiting not
below 0, the year's savings base never falls as the gains saldo rises. -/
theorem base_mono (ρ : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (year : ℤ) (gp0 gp0' rcm0 : ℚ) (pend : List Pending)
    (h : ∀ p ∈ pend, 0 ≤ p.amount) (hle : gp0 ≤ gp0') :
    (yearStep ρ year gp0 rcm0 pend).base ≤ (yearStep ρ year gp0' rcm0 pend).base := by
  rw [base_formula ρ hρ0 year gp0 rcm0 pend h, base_formula ρ hρ0 year gp0' rcm0 pend h]
  obtain ⟨q1, q2, q3, q4⟩ := phase1_mono ρ hρ0 hρ1 gp0 gp0' rcm0 hle
  exact terms_mono _ _ _ _ _ _ _ _ _ _ q1 q2 q3 q4

theorem crossRate_bounds (y : ℤ) (hy : 2015 ≤ y) : ∃ ρ, crossRate y = some ρ ∧ 0 ≤ ρ ∧ ρ ≤ 1 := by
  unfold crossRate
  split_ifs <;> first | omega | exact ⟨_, rfl, by norm_num, by norm_num⟩

theorem yearTax_eq (y : ℤ) (ρ : ℚ) (hρ : crossRate y = some ρ) (gp rcm : ℚ) (carried : List Pending) :
    ∃ t, savingsTax y (yearStep ρ y gp rcm (carried.mergeSort fun a b => decide (a.yr ≤ b.yr))).base = some t ∧
      yearTax y gp rcm carried = t := by
  have hy : 2015 ≤ y := by
    unfold crossRate at hρ; split_ifs at hρ with h <;> (try cases hρ) <;> omega
  obtain ⟨t, ht, -, -⟩ := savingsTax_spec y hy
  refine ⟨_, ht _, ?_⟩
  simp [yearTax, savings, run, hρ, ht]

/-- **ES-7** In full: from 2015, with the losses waiting not below 0 and a gain not below 0, the tax if sold today
is exactly the year's tax with the sale less the tax without it (the `max … 0` in the code never bites). -/
theorem taxOnSale_eq (gain : ℚ) (hg : 0 ≤ gain) (y : ℤ) (hy : 2015 ≤ y) (gp rcm : ℚ) (carried : List Pending)
    (h : ∀ p ∈ carried, 0 ≤ p.amount) :
    taxOnSale gain y gp rcm carried = yearTax y (gp + gain) rcm carried - yearTax y gp rcm carried := by
  obtain ⟨ρ, hρ, h0, h1⟩ := crossRate_bounds y hy
  obtain ⟨t, ht, -, hmono⟩ := savingsTax_spec y hy
  obtain ⟨a, ha, ea⟩ := yearTax_eq y ρ hρ (gp + gain) rcm carried
  obtain ⟨b, hb, eb⟩ := yearTax_eq y ρ hρ gp rcm carried
  have hs : ∀ p ∈ carried.mergeSort (fun a b => decide (a.yr ≤ b.yr)), 0 ≤ p.amount :=
    fun p hp => h p ((List.mem_mergeSort).mp hp)
  have hm := base_mono ρ h0 h1 y gp (gp + gain) rcm _ hs (by linarith)
  rw [ht] at ha hb
  cases ha; cases hb
  have := hmono _ _ hm
  unfold taxOnSale
  rw [ea, eb]
  exact max_eq_left (by linarith)

end Kanon.Spain
