/-!
# Splitting a sale across pools (#13)

When a token is held in amounts its deepest pool can't absorb, My money compares selling everything into each one
of its deepest pools with a split across them in proportion to each pool's coins, and shows the one that loses
least. The app does this in `splitSale()` (`src/lib/liquidity/impact.ts`). Shown here, for any way of measuring the
loss (exact numbers, compared as naturals):
* the split's parts add up to exactly the amount sold (the last pool takes what's left after the others),
* the result is one of the candidates, and it never loses more than selling everything into any one pool.
-/

namespace Kanon.Split

/-- The proportional split: each pool but the last gets `sell · coins / total`, the last gets what's left.
`given` is what earlier pools already took. A pool is its number of coins; a part is (pool, amount sold into it). -/
def prorata (sell total : Int) : List Int → Int → List (Int × Int)
  | [], _ => []
  | [b], given => [(b, sell - given)]
  | b :: c :: rest, given => (b, sell * b / total) :: prorata sell total (c :: rest) (given + sell * b / total)

/-- Total amount sold across a list of parts. -/
def sold (parts : List (Int × Int)) : Int := (parts.map Prod.snd).foldr (· + ·) 0

/-- **#13** With at least one pool, the parts plus what was already given add up to exactly the amount sold. -/
theorem prorata_adds_up (sell total : Int) : ∀ (pools : List Int) (given : Int), pools ≠ [] →
    sold (prorata sell total pools given) + given = sell
  | [], _, h => absurd rfl h
  | [b], given, _ => by simp [prorata, sold]
  | b :: c :: rest, given, _ => by
      have ih := prorata_adds_up sell total (c :: rest) (given + sell * b / total) (by simp)
      simp only [prorata, sold, List.map, List.foldr] at ih ⊢
      omega

/-- **#13** Starting from nothing given, the split sells exactly the amount asked for. -/
theorem prorata_exact (sell total : Int) (pools : List Int) (h : pools ≠ []) :
    sold (prorata sell total pools 0) = sell := by
  have := prorata_adds_up sell total pools 0 h
  omega

/-- Keep the candidate that loses least; on a tie, keep the earlier one (fewer pools come first). -/
def pick {α : Type} (loss : α → Nat) : α → List α → α
  | best, [] => best
  | best, c :: cs => pick loss (if loss c < loss best then c else best) cs

/-- **#13** The kept candidate loses no more than any candidate considered. -/
theorem pick_le {α : Type} (loss : α → Nat) : ∀ (best : α) (cs : List α) (x : α), x ∈ best :: cs →
    loss (pick loss best cs) ≤ loss x
  | best, [], x, hx => by
      have : x = best := by simpa using hx
      subst this; simp [pick]
  | best, c :: cs, x, hx => by
      by_cases hlt : loss c < loss best
      · have step := pick_le loss c cs
        simp only [pick, hlt, if_true]
        rcases List.mem_cons.mp hx with rfl | hx'
        · have := step c (List.mem_cons_self ..); omega
        · exact step x hx'
      · have step := pick_le loss best cs
        simp only [pick, hlt, if_false]
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact step x (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · have := step best (List.mem_cons_self ..); omega
          · exact step x (List.mem_cons_of_mem _ hx'')

/-- **#13** The kept candidate is one of the candidates: nothing is invented. -/
theorem pick_mem {α : Type} (loss : α → Nat) : ∀ (best : α) (cs : List α), pick loss best cs ∈ best :: cs
  | best, [] => by simp [pick]
  | best, c :: cs => by
      by_cases hlt : loss c < loss best
      · simp only [pick, hlt, if_true]
        exact List.mem_cons_of_mem _ (pick_mem loss c cs)
      · simp only [pick, hlt, if_false]
        rcases List.mem_cons.mp (pick_mem loss best cs) with h | h
        · rw [h]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- The candidates the app compares: everything into each pool, then the proportional split. -/
def candidates (sell total : Int) (pools : List Int) : List (List (Int × Int)) :=
  pools.map (fun b => [(b, sell)]) ++ [prorata sell total pools 0]

/-- The split shown: the candidate that loses least, starting from everything into the deepest pool. -/
def shown (loss : List (Int × Int) → Nat) (sell total deepest : Int) (rest : List Int) : List (Int × Int) :=
  match candidates sell total (deepest :: rest) with
  | [] => []
  | c :: cs => pick loss c cs

/-- **#13** What's shown never loses more than selling everything into any one of the pools. -/
theorem never_worse_than_one_pool (loss : List (Int × Int) → Nat) (sell total deepest : Int) (rest : List Int)
    (b : Int) (hb : b ∈ deepest :: rest) : loss (shown loss sell total deepest rest) ≤ loss [(b, sell)] := by
  unfold shown
  have hmem : [(b, sell)] ∈ candidates sell total (deepest :: rest) := by
    unfold candidates
    exact List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  generalize hc : candidates sell total (deepest :: rest) = cs at hmem
  cases cs with
  | nil => simp at hmem
  | cons c cs => exact pick_le loss c cs _ hmem

/-- **#13** What's shown sells exactly the amount asked for. -/
theorem shown_exact (loss : List (Int × Int) → Nat) (sell total deepest : Int) (rest : List Int) :
    sold (shown loss sell total deepest rest) = sell := by
  unfold shown
  have all : ∀ p ∈ candidates sell total (deepest :: rest), sold p = sell := by
    intro p hp
    unfold candidates at hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
      simp [sold]
    · simp at h; subst h; exact prorata_exact sell total _ (by simp)
  generalize hc : candidates sell total (deepest :: rest) = cs at all
  cases cs with
  | nil => unfold candidates at hc; simp at hc
  | cons c cs => exact all _ (pick_mem loss c cs)

end Kanon.Split
