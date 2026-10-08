> Audit by Aristotle (Harmonic's prover, used as a tool; no affiliation), 8 Oct 2026, of the bank as it stood at commit 1f082ba. Since then: F4 (Thailand) is corrected in `Reference.lean`; the stronger models are in `KanonProofs/Tightened.lean` (see `TIGHTENED.md`). The theorem names below refer to the audit's own working file, which is not kept in the build because its counterexamples describe the old models.

# Audit of the KANON proof bank

All results are in `KanonProofs/Audit.lean` (namespace `Kanon.Audit`). It imports `KanonProofs`, builds with
`lake build KanonProofs.Audit`, and has no `sorry`, no `native_decide` and no new axioms. No existing file was
changed. Every counterexample below is a Lean theorem checked by `decide` or by direct computation on
explicit numbers.

Short version: **every theorem in the bank is true, and every hypothesis can hold in a realistic case.** The
problems are in what the theorems leave out. Some README claims are about a different object than the one
the theorem covers (#10/#11, #17). Some models give answers a user or a tax authority would call wrong on
ordinary inputs (#5, #9, #13, #21, #23, #28).

---

## Findings, most serious first

| # | Row | Finding | Theorem(s) in `Audit.lean` |
|---|---|---|---|
| F1 | 10, 11 | **The plan the planner chooses is never proved valid.** #10 (lots exist, no lot twice, within holdings, cash raised) is proved only for `fifoPlan`. #11 is proved for `cheapest`, which can return any candidate. If tax grows with coins sold, the "cheapest" plan sells **nothing**: tax 0 beats the default's tax, and none of the 50 coins asked for are sold. If the tax function rates it lower, a plan selling 50 coins from **a lot that does not exist** is chosen and fails `Valid`. #11 is true as stated, but together with #10 it suggests "the plan shown is valid and cheapest", and nothing proves that. | `chosen_plan_sells_nothing`, `chosen_plan_can_be_invalid` |
| F2 | 17 | **The guardrail lets made-up money amounts through.** Money is in cents, so a "small count" (`n ≤ 3100`) is any amount up to $31.00, and a "year" (`199000..210000`) is any amount from $1,990.00 to $2,100.00. With engine data `[$50.00]`, an answer showing "$2,000.00" and "$31.00" passes, though neither is close to $50. With no engine numbers at all, any amount in those ranges passes. The theorem matches the README's words, but the words do not deliver the promise that "the agent only explains; the engines do every number". | `guard_passes_invented_money`, `guard_passes_without_data` |
| F3 | 5 | **The holding period (Germany's one-year rule, US long/short) is a day count, which is wrong across leap years.** "More than one year" is a calendar rule. Day 0 is 1 Jan 2023. Bought 1 Jan 2024 and sold 1 Jan 2025 is exactly one year, so taxable in Germany and short-term in the US. Bought 1 Jan 2023 and sold 2 Jan 2024 is more than a year. Both pairs are 366 days apart. For **every** threshold `days`, the model gives both the same answer, so one of them is always on the wrong side. With `days = 365`, the exactly-one-year sale is counted tax-free. | `holding_period_leap_year` (all thresholds), `holding_period_wrong_either_way` |
| F4 | 9 | **Thailand's top band starts at 4,000,000 baht instead of 5,000,000.** `thBrackets` has 30% for 2M–4M and 35% above 4M. The published schedule is 30% for 2M–5M and 35% above 5M. On 5,000,000 baht of net income the model charges 1,315,000 baht instead of 1,265,000, which is 50,000 baht too much. (The README says the proofs do not cover how the law was read. This is still a wrong number, and `th_mono_net` proves monotonicity of the wrong schedule.) | `thailand_top_band_starts_too_low` |
| F5 | 5 | **The average-cost pool accepts a sale of more coins than it holds and creates cost.** `avg_conserves` and `avg_kept` assume `q ≤ qty`, but `avgSell` and `avgTake` do not enforce it. Selling 20 coins from a pool of 10 coins costing 1,000 takes a cost of 2,000, twice the pool's cost. The pool then shows 0 coins and 0 cost. | `avg_oversell_takes_more_cost_than_held` |
| F6 | 5 | **"Oldest first" means first in the list.** `sell` does not sort the lots by `acquired`, and neither `sell` nor `fifo_newest_left` assumes they are sorted. With lots `[day 30, day 1]`, a sale of 5 takes the day-30 lot and leaves the oldest lot untouched. `fifo_newest_left` still holds, because it only talks about list positions. | `fifo_follows_list_order_not_dates` |
| F7 | 9 | **Brazil: splitting a gain into several sales lowers the tax.** `gainsTax` puts each sale's gain through the 15/17.5/20/22.5% bands separately. The same R$10m gain in one month costs R$1,625,000 as one sale and R$1,500,000 as two sales of R$5m. Brazilian law adds together gains from selling parts of the same asset (Lei 8.981 art. 21 §3, as amended), which the model does not do. Please confirm this against the law. The arithmetic is proved. | `brazil_split_sale_pays_less` |
| F8 | 5 | **UK: "no purchase is used twice" holds only within one sale.** `matchSale` returns neither the updated 30-day window nor the updated pool, so nothing links consecutive sales. Two sales of 10 that are both given the same 5-coin buy and the same 5-coin pool together take 20 coins' worth of matches from 10 coins of purchases. `window_once` and `within_limits` still hold for each sale. (`Reference.ukMatch` does the sequencing, but no theorem covers it.) | `uk_two_sales_same_buy` |
| F9 | 13 | **A split can sell a negative amount into a pool.** `prorata` takes `total` as a separate argument, and nothing ties it to the pools' coins. With pools 10 and 10 and `total = 5`, a sale of 100 is split as +200 into one pool and −100 into the other. It still "adds up to exactly the amount sold" (`shown_exact`), and `shown` returns it if the loss function rates it best. | `split_negative_part`, `split_negative_part_shown` |
| F10 | 6, 7 | **Bracket tax rounds down, but #6 says KANON's tax estimates round up.** `Brackets.tax` takes `taxBp … / 10000`, which is the floor. At 20% of 1,234 the exact tax is 246.8, and the schedule gives 246, which is less than the exact tax. `Rounding.up` exists but the tax schedule never uses it. | `bracket_tax_rounds_down` |
| F11 | 23 | **The "7-day average" divides by the number of samples present, not by 168.** One hour holding 1,000 gives an average of 1,000. The same hour inside a full week of samples gives 5. Unless the app always passes exactly 168 samples, a fresh wallet passes the hold check at once. Also, `dedup_once` is not connected to `twa`, so no theorem says the summed samples come from de-duplicated wallets. | `twa_not_seven_days` |
| F12 | 28 | **A number dated in the future is never stale.** `today - d` is truncated to 0. A rate whose date was mistyped as day 10,000 (when today is day 100) is shown without a label and given to the agent. It is still "fresh" on day 9,000. "A number with no readable date is always stale" holds, but a misread date counts as readable. | `future_dated_never_stale` |
| F13 | 21 | **A 100% ladder does not sell everything.** Each step is rounded down from the starting position, and the remainder is never sold. Steps of 33.33% + 33.33% + 33.34% on 999 units sell 997 and leave 2. That is safe (never oversells), but a "sell it all" plan leaves units behind. | `ladder_full_exit_leaves_units` |
| F14 | 10 | **`fifoPlan_cash` cannot be applied to major coins.** Its price is a whole number of cents per smallest unit, and it must be at least 1. Bitcoin at $60,000 is 0.06 cents per satoshi, which is 0 in whole cents. If the app rounded the price up to 1 cent, a $100 target would sell 10,000 sats, worth $6. The hypothesis can hold, but only for coins whose smallest unit is worth at least a cent. | `cash_target_price_unit` |
| F15 | 7 | **Tax above the income, or above the gain, is allowed by the schedule's conditions.** `WellFormed` asks only `lo ≤ hi`, so two overlapping 60% bands tax 1,000 at 1,200. `TaxableMono` allows an allowance that disappears all at once, so a gain of 1 on income 999 costs 200 of tax. Monotonicity (#7) is unaffected. The finding is that the conditions do not rule out these schedules. | `wellformed_tax_above_income`, `stacked_tax_above_gain` |
| F16 | 18 | **"The swap's minimum-out bounds the price paid" is just `a ≤ b → n·a ≤ n·b`.** It never mentions the swap. With `minOut = 0`, meaning no slippage protection, it holds for every outcome, including receiving nothing. | `minOut_zero_bounds_nothing` |
| F17 | 29 | **When the multiplier falls, `added` reports 0 although the value fell** (truncated subtraction). Also, "the token count never moves" is not a theorem: it holds only because the token count is a fixed input. `shares_grow_with_multiplier`, which the README cites, is about shares. | `multiplier_fall_reports_zero` |
| F18 | 3 | Rounding edge cases in the lot ledger (cost is still conserved). Selling 1 unit of a 1,000-unit lot costing 999 records a cost of 0. A lot holding 0 coins but 500 of cost passes all 500 to the next sale. Both move cost from one sale to another rather than losing it. Low impact. | `lots_rounding_edges` |
| F19 | 22 | An empty history scores **100% complete**. That is consistent with the docstring, but such a history passes the "100% complete" requirement for a "skipped" grade (#25). Informational. | `empty_history_complete` |

## Claims the bank's words make, proved here (gaps closed)

| Row | What was missing | Theorem |
|---|---|---|
| 15 | `peak_attained` allows "or 0" even for a non-empty window. Proved here: for any non-empty window, the best price **is** one of the prices seen. | `peak_attained_nonempty` |
| 27 | "drops or duplicates nothing" was backed only by equal **length** plus equal balances. Proved here: the piles are a **permutation** of the file's movements. | `group_perm` (with `flatten_insert_perm`) |
| 31 | "no part exceeds the whole" was stated only for the sale side. Proved here for the new-cost side too. | `new_cost_part_at_most_price` |
| 12 | Extra check: a pool holding coins and cash is never drained completely by one sale. | `payout_lt_reserve` |
| 6 | Spot checks: exactly half a cent rounds up, just under half rounds down, and an exact amount is not rounded up. | `rounding_spot_checks` |
| 21 | The UK tax year is right for every month and day, not only 5 and 6 April. | `uk_tax_year_all_days` |

---

## 1. Empty promises: can the hypotheses hold?

Every theorem with hypotheses is applied in Part 1 of `Audit.lean` to concrete, non-degenerate values
(non-zero amounts, non-empty lists), so all its hypotheses hold at once. **No theorem's hypotheses hold only
in a degenerate case, and none are contradictory.** Covered (one `example` each, unless noted):

- **Brackets:** `slice_mono`, `taxBp_mono`, `tax_mono`, `stacked_nonneg` (two-band schedule `demoSchedule`, with `demoSchedule_wf`).
- **Rounding:** `halfUp_close`, `up_never_under`, `halfUp_le_up` (`s = 100`).
- **Lots:** `sliceCost_le`, `sell_exact`, `matchOnce_nodup`.
- **Matching:** `all_long`, `avg_conserves`, `avg_kept`.
- **UkMatch:** `pool_cost_le`.
- **Years:** `past_unchanged`, `only_through_carry`, `past_events_unchanged` (toy step `demoStep`).
- **CashOut:** `fifoPlan_hits`, `fifoPlan_cash`. The hypotheses hold, but `0 < price` in whole cents per smallest unit fails for BTC and ETH at real prices (F14).
- **Split:** `prorata_adds_up`, `prorata_exact`, `pick_le`, `never_worse_than_one_pool`.
- **Ladder:** `never_oversells`, `step_within`.
- **FeeSplit / ReserveCap:** `supply_exact`, `minOut_bounds_price` (true even with `minOut = 0`, F16), `reserve_never_over_cap`, `full_reserve_burns_the_rest`.
- **LookAhead:** `peak_no_lookahead`, `reached_no_lookahead`, `foldl_congr`, `foldl_attained`.
- **Guard:** `fallback_ok`, `shown_passes`, `shown_numbers_sourced`, `shown_no_banned`.
- **Completeness:** `fix_never_lowers`.
- **HoldCheck:** `atLeast_len`, `atLeast_sum`, `more_never_less`, `twa_le_max`, `enough_gives_access` (with `demo_atLeast`).
- **Payments:** `conserved`, `costs_bounded`.
- **Grade:** `never_skipped_incomplete`, `skipped_means`. The second is applied to a real "skipped" grade: 100% complete, read after, covered, earlier sales only.
- **Fresh:** `old_is_labelled`, `undated_is_labelled`, `stale_stays_stale`.
- **Rotation:** `sum_parts`, `sold_for_what_came_in`, `new_cost_is_value_received`, `sale_equals_new_cost`.
- **Spread:** `chunks_sum`, `chunks_within`, `chunks_length`, `plan_sum`, `first_within`, `plan_within`, `fewest_months`, `finishes_soonest` (R$35,000 limit, R$10,000 already sold, R$90,000 to sell).
- **StockToken:** `rise_adds_exactly`, `rise_adds_something`, `shares_grow_with_multiplier`.
- **Ranking:** `never_below_dearer`.
- **Reference:** `br_exempt`, `bandBp_mono`, `band_first`, `th_mono_net`, `th_at_least_half_percent`, `ng_mono`.

Theorems without hypotheses need no example. These are `sell_qty`, `sell_cost`, `sell_le`, `move_keeps_lots`, `move_dest`,
`fifo_newest_left`, `split_total`, the `take_*`/`parts_sum`/`within_limits`/`window_once` lemmas, `kept_falls`,
`kept_le_fee`, `k_never_falls`, `pick_mem`, `shown_exact`, `sold_le`, `uk_boundary`, the FeeSplit/ReserveCap
equalities, `peak_attained`, `score_le_100`, `shares_exact`, `dedup_once`, `mem_dedup`, `followed_iff`,
`label_keeps_value`, `agent_never_gets_stale`, the Grouping theorems, `part_at_most_price`, `value_by_feed`,
`no_change_nothing_added`, `cheaper_first`, `same_routes`, `za_no_flip`, `za_one_or_other`, `us_le_regular`,
`darf_conserves`, `darf_min`, `cheapest_le_start`, `chosen_le_default`, `fixed_allowance_mono` and
`taper_allowance_mono`.

## 2. README rows against the theorems

| Row | Verdict |
|---|---|
| 1, 2, 20 | Scripts and lock files, not Lean. Outside this audit. |
| 3 Lot conservation | Matches. Only rounding edge cases remain (F18). |
| 4 Own-wallet moves | Matches. `move` relabels the wallet only, so the result is true by construction. Nothing wrong. |
| 5 Which coins count as sold | **Says more than proved, and models are wrong on ordinary inputs:** UK one sale only (F8), FIFO order not checked (F6), holding period on the wrong side of the anniversary (F3), average cost allows overselling (F5). The parts-add-up and conservation claims themselves are proved. |
| 6 Rounding | The `Rounding` file is right (nothing wrong; see `rounding_spot_checks`). The tax schedule does not use the round-up rule (F10). |
| 7 Tax never falls | Monotonicity is proved. The schedule conditions still allow tax above the income or the gain (F15). |
| 8 Tax-year isolation | Matches. **Nothing wrong.** |
| 9 Reference models | Thailand's bands are wrong (F4). Brazil's per-sale banding lets a split sale pay less (F7). `us_le_regular` holds by construction (`min`), so it does not check the worksheet's arithmetic. Brazil's exemption and DARF, South Africa and Nigeria: nothing wrong found (the Nigerian bands match the bands stated in the file). |
| 10 Cash-out plans valid | Proved for the oldest-first plan only, not for the plan chosen (F1). The cash target applies only to coarse units (F14). |
| 11 Chosen ≤ default | True as stated. The chosen plan can still sell nothing or name a lot that does not exist (F1). |
| 12 Price impact | Matches. **Nothing wrong** (`payout_lt_reserve` added). |
| 13 Split across pools | Parts can be negative because `total` is unchecked (F9). Otherwise matches. |
| 15 No look-ahead | Matches. Strengthened by `peak_attained_nonempty`. |
| 17 Guardrail | The words match the theorems, but the "count or year" escape lets invented money through (F2). |
| 18 Creator fees | The split, dust and burn claims match. The minimum-out claim is trivial (F16). |
| 33 Reserve ceiling | Matches. **Nothing wrong.** |
| 21 Exit ladder | Never oversells, as claimed. A full exit leaves units unsold (F13). The UK boundary is right (`uk_tax_year_all_days`). |
| 22 Data complete score | Matches. An empty history scores 100% (F19, informational). |
| 23 Hold check | The average does not cover a fixed 7 days, and wallet de-duplication is not linked to the average (F11). |
| 24 Payments | Matches. **Nothing wrong.** |
| 25 Exit-card grade | Matches. **Nothing wrong.** |
| 27 Grouping | Matches. Strengthened to a permutation (`group_perm`). |
| 28 Freshness | Future-dated numbers are never stale (F12). |
| 29 Stock Token | The value equations match. "Token count never moves" is not a theorem, and a falling multiplier reports 0 added (F17). |
| 30 Ranking | Matches. **Nothing wrong.** |
| 31 Swap | Matches. The new-cost side's "no part exceeds the whole" is added (`new_cost_part_at_most_price`). |
| 32 Brazil monthly planner | Matches. **Nothing wrong.** |

## 3. Rounding and edge cases, per requested file

- **Brackets:** F10 (rounds down), F15 (tax above the income or the gain).
- **Rounding:** nothing wrong.
- **Lots:** F18 (minor). Conservation and no overselling hold.
- **Matching:** F3 (anniversary boundary), F5 (oversell creates cost), F6 (list order rather than date order).
- **UkMatch:** F8 (no link between sales). The pool never gives out more than it holds (proved).
- **Years:** nothing wrong.
- **CashOut:** F1, F14.
- **PriceImpact:** nothing wrong.
- **Split:** F9.
- **Ladder:** F13. The UK date boundary is correct.
- **FeeSplit / ReserveCap:** split, dust, cap and burn are all correct. Only F16 (trivial minimum-out claim).
