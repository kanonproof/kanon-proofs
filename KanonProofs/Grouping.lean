/-!
# Grouping never creates or loses coins (#27)

An exchange file or a wallet history is a list of movements: which transaction it belongs to, which
wallet, which coin, and a signed amount (in the coin's smallest unit). KANON groups movements that share a
transaction into one happening (a trade, a move between your own wallets, a fee). Grouping only sorts
movements into piles: for every wallet and every coin, the balance worked out from the piles equals the
balance worked out from the file. The app's own grouping is tested against the same property
(`src/lib/money-map/conservation.test.ts`).
-/

namespace Kanon.Grouping

structure Mv where
  tx : Nat
  wallet : Nat
  coin : Nat
  amount : Int
deriving DecidableEq, Repr

/-- The balance of one coin in one wallet: the sum of its movements. -/
def balance (w c : Nat) : List Mv → Int
  | [] => 0
  | m :: ms => (if m.wallet = w ∧ m.coin = c then m.amount else 0) + balance w c ms

/-- Put one movement on the pile for its transaction, starting a new pile if there isn't one. -/
def insert (m : Mv) : List (Nat × List Mv) → List (Nat × List Mv)
  | [] => [(m.tx, [m])]
  | (k, ms) :: rest => if k = m.tx then (k, m :: ms) :: rest else (k, ms) :: insert m rest

/-- Group a whole list, one movement at a time. -/
def group : List Mv → List (Nat × List Mv)
  | [] => []
  | m :: ms => insert m (group ms)

/-- Every movement in every pile, pile by pile. -/
def flatten : List (Nat × List Mv) → List Mv
  | [] => []
  | (_, ms) :: rest => ms ++ flatten rest

theorem balance_append (w c : Nat) (a b : List Mv) : balance w c (a ++ b) = balance w c a + balance w c b := by
  induction a with
  | nil => simp [balance]
  | cons m ms ih => simp only [List.cons_append, balance, ih]; omega

theorem length_flatten_insert (m : Mv) (g : List (Nat × List Mv)) : (flatten (insert m g)).length = (flatten g).length + 1 := by
  induction g with
  | nil => simp [insert, flatten]
  | cons p rest ih =>
    obtain ⟨k, ms⟩ := p
    unfold insert
    split
    · simp [flatten]
    · simp [flatten, ih]; omega

theorem balance_flatten_insert (w c : Nat) (m : Mv) (g : List (Nat × List Mv)) :
    balance w c (flatten (insert m g)) = balance w c [m] + balance w c (flatten g) := by
  induction g with
  | nil => simp [insert, flatten, balance]
  | cons p rest ih =>
    obtain ⟨k, ms⟩ := p
    unfold insert
    split
    · simp only [flatten, List.cons_append, balance, balance_append]; omega
    · simp only [flatten, balance_append, ih]; omega

/-- **#27** Grouping never creates or loses coins: for every wallet and coin, the piles hold the same balance as the file. -/
theorem group_keeps_balance (w c : Nat) (ms : List Mv) : balance w c (flatten (group ms)) = balance w c ms := by
  induction ms with
  | nil => simp [group, flatten, balance]
  | cons m ms ih =>
    simp only [group, balance_flatten_insert, ih, balance]; omega

/-- **#27** No movement is dropped or duplicated: the piles hold exactly as many movements as the file. -/
theorem group_keeps_count (ms : List Mv) : (flatten (group ms)).length = ms.length := by
  induction ms with
  | nil => simp [group, flatten]
  | cons m ms ih => simp [group, length_flatten_insert, ih]

/-- **#27** Each pile holds only movements of its own transaction. -/
theorem piles_are_one_tx (ms : List Mv) : ∀ p ∈ group ms, ∀ m ∈ p.2, m.tx = p.1 := by
  induction ms with
  | nil => simp [group]
  | cons x xs ih =>
    simp only [group]
    generalize group xs = g at ih
    induction g with
    | nil => simp [insert]
    | cons q rest ih2 =>
      obtain ⟨k, qs⟩ := q
      intro p hp m hm
      unfold insert at hp
      split at hp
      · rename_i hk
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact hk.symm
          · exact ih (k, qs) (by simp) m hm
        · exact ih p (by simp [hp]) m hm
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ih (k, qs) (by simp) m hm
        · exact ih2 (fun p' hp' => ih p' (by simp [hp'])) p hp m hm

end Kanon.Grouping
