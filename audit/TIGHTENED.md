# Tightening the KANON proof bank

All new results are in `KanonProofs/Tightened.lean`, in namespace `Kanon.Tightened`. The root file `KanonProofs.lean`
gained one line at the end, `import KanonProofs.Tightened`. No other existing `.lean` file was changed, no existing
definition or theorem statement was changed, and `Reference.lean` was not touched. `lake build` succeeds. The new file
has no `sorry`, no `native_decide` and no new axioms: every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`, checked with `#print axioms`.

**Import note.** You asked for a file that imports `KanonProofs` and is also imported by `KanonProofs.lean`. Lean
does not allow that, because the two files would import each other. So `Tightened.lean` imports the same 25
modules that `KanonProofs.lean` imports, one line each. It sees exactly the same definitions.

## A. Gap-closing theorems from the audit (all proved against the current files)

- **#15**: for a non-empty window, the best price is one of the prices seen: `peak_attained_nonempty` (helper `foldl_max_ge`).
- **#27**: the piles are a permutation of the file's movements: `group_perm` (helper `flatten_insert_perm`).
- **#31**: no new-cost part is larger than the price: `new_cost_part_at_most_price`.
- **#12**: a pool holding coins and cash is never drained by one sale: `payout_lt_reserve`.
- **#6**: spot checks of half-up and round-up: `rounding_spot_checks`.
- **#21**: the UK tax year is right for every month and day: `uk_tax_year_all_days`.

## B. Findings

- **F1 (planner).** New planner `safePlan`. It picks the cheapest of the candidates that pass `admissible`, starting from `fifoPlan`. A candidate is admissible if it is valid (checked by `validB`, and `validB_iff` proves this check is exactly `Valid`) and sells exactly `q` coins. Proved: the chosen plan is always `Valid` (`safePlan_valid`); it sells exactly `q` whenever `q ≤ totalQty lots` (`safePlan_qty`); its tax is at most the oldest-first default's (`safePlan_le_default`) and at most any admissible candidate's (`safePlan_le_admissible`); it is always the default or an admissible candidate (`safePlan_mem`). The audit's two counterexamples are now refused (`safePlan_refuses_audit_examples`).
- **F5 (average cost).** New capped sale `avgQtySafe` / `avgTakeSafe` / `avgSellSafe`, which sells `min q qty`. For every `q`, with no `q ≤ qty` hypothesis: coins taken ≤ coins held (`avgSafe_qty_le`); cost taken ≤ cost held (`avgSafe_cost_le`); coins are conserved (`avgSafe_qty_conserves`); cost is conserved (`avgSafe_cost_conserves`); the average price is kept (`avgSafe_kept`). It equals the old sale when `q ≤ qty` (`avgSafe_eq_old`). The audit's example now takes 10 coins and a cost of 1,000 (`avgSafe_audit_example`).
- **F6 (oldest first by date).** Both options are done.
  - On the old `sell`, assuming the lots are sorted by date (`SortedByDate`): every lot left untouched was acquired no earlier than every lot used (`sell_untouched_not_older`).
  - New `sellByDate` sorts by acquisition date first and has the same property with no hypothesis (`sellByDate_untouched_not_older`, using `byDate_sorted`). It still conserves coins and cost (`sellByDate_conserves`).
  - "Used" means the first `usedLen` lots. `sell_used_untouched` proves that the lots after them are kept unchanged, that those first lots supply every coin sold, and that at most one of them survives, cut down, with its date unchanged.
  - The audit's example now sells the day-1 lot (`sellByDate_audit_example`).
- **F8 (UK sequence).** New `ukStep` and `ukRun`. Each sale returns the window purchases left (with their cost) and the pool (coins and cost), and the next sale starts from them.
  - On quantities, each step is exactly the bank's `matchSale` (`ukStep_is_matchSale`, `takeC_qty`).
  - Proved over the whole sequence: for each purchase in the window, what all the sales took from it plus what is left of it equals what was bought (`ukRun_each_buy_once`).
  - The same-day matches never exceed the same-day purchases (`ukRun_sameDay_le`).
  - Coins are conserved: everything matched, plus what is left in the window and the pool, equals the starting window and pool plus all purchases (`ukRun_qty_conserved`).
  - Total cost is conserved exactly (`ukRun_cost_conserved`).
  - Every sale's parts add up to what it sold (`ukStep_parts`, `ukRun_parts`).
  - The audit's double use is gone: 10 coins are matched, not 20 (`ukRun_audit_example`).
- **F9 (pro-rata split).** Proved about the old `prorata`, with `total` set to the pools' sum `sumI pools` (`prorata_parts_bounded`), and through the wrapper `prorataPools`. Assuming the amount sold and every pool are non-negative, every part is ≥ 0 and ≤ the amount sold (`prorataPools_bounded`), and the parts add up exactly (`prorataPools_exact`). The same holds for what is shown when the total comes from the pools (`shownPools_bounded`). The audit's example now splits 50/50 (`prorataPools_audit_example`).
- **F12 (freshness).** New `staleT` / `displayT` / `forAgentT`, where a date later than today counts as stale.
  - A future-dated number is always labelled (`future_is_labelled`) and never given to the agent (`future_never_for_agent`).
  - Existing guarantees kept: `old_is_labelledT`, `undated_is_labelledT`, `label_keeps_valueT`, and `agent_never_gets_staleT`, which now also says the date is not after today.
  - Relation to the old rule: the new rule labels everything the old one did (`stale_implies_staleT`), and the two agree for numbers not dated in the future (`staleT_eq_stale`).
  - The audit's example is fixed (`staleT_audit_example`).
- **F3 (holding period on calendar dates).** New `Date`, `anniversary` (a 29 February purchase has its anniversary on 28 February) and `heldOverYear`, which means "sold after the anniversary".
  - The two leap-year cases from the audit are separated (`heldOverYear_leap_cases`).
  - 29 February purchases are handled (`heldOverYear_feb29`).
  - The test is monotone in the sale date (`heldOverYear_mono`).
  - For contrast, the old day-count test gives both cases the same answer for every threshold (`day_count_cannot_separate`).
- **F2 (guard).** New `TAnswer`, in which each number carries a `Kind`: `money`, `percent` or `bare`. A number passes as a count or year only if it is `bare` (`freeT`, `checkT`, `respondT`).
  - Whatever is shown passes the checker (`shownT_passes`).
  - Every money-flagged number shown is within tolerance of an engine number (`shownT_money_close`). The same holds for any number not written bare, percentages included (`shownT_money_sourced`).
  - Every number shown is either a bare count or year, or close to an engine number (`shownT_numbers_sourced`).
  - No banned word is shown (`shownT_no_banned`).
  - The audit's invented "$2,000.00" and "$31.00" are now refused (`checkT_audit_example`).

## What could not be proved, and limits of what was proved

- **F12: `stale_stays_stale` cannot hold in its old form.** No rule that labels future dates as stale can satisfy it. A number dated day 150 is stale on day 100, because its date is in the future, and fresh on day 150 (`staleT_future_then_fresh`). It is proved instead under the extra hypothesis that the number was not future-dated on the earlier day (`staleT_stays_stale`).
- **F1:** when `q` is more than the coins held, `safePlan_qty` does not apply. The chosen plan is then the oldest-first plan or a valid candidate that sells exactly `q` (`safePlan_mem`). I did not prove the separate fact that no valid plan can sell more than the coins held.
- **F9:** the bounds assume `0 ≤ sell` and that every pool is `≥ 0`. A negative pool count would make negative parts unavoidable.
- **F8:** this is still a model, with these limits:
  - The 30-day window is the list of purchases given at the start, carried from sale to sale.
  - Purchases in the window never move into the section 104 pool.
  - What is left of a same-day purchase joins the pool.
  - Whether this is the right reading of HMRC's rules is not checked.
- **F3:** dates are not checked for validity (for example, month 13). The 28 February anniversary rule was used as you specified; I have not checked it against German or US law. The new test is a separate definition: the bank's `sellSplit` still uses day counts.
- **F2:** the proof assumes each number's `Kind` flag is correct. It cannot detect money that is wrongly flagged as a bare number.
