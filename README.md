# KANON proof bank

The rules behind **KANON, the agent for your crypto gains**, machine-checked in Lean.
Anyone can re-check every proof for free:

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake build && python3 scripts/proofs.py gate && python3 scripts/proofs.py lock
```

**What a proof here means:** the maths in KANON's engines follows the rule as written below.
It does **not** mean the rule was read correctly from the law; that's what each country's
"Matches N official examples" badge and its worked examples are for. Each engine has a reference model
here; the production code (TypeScript) is tested against the same cases.

## Status: 29 of the 33 planned checks done

| # | What is proven, in plain words | File |
|---|---|---|
| 1 | **Axiom gate:** the build fails if any proof skips a step (`sorry`), uses `native_decide`, or adds its own axiom. Only Lean's three standard axioms are allowed. | `scripts/proofs.py gate` |
| 2 | **Statement lock:** every theorem's statement is fingerprinted. Changing one fails the build until a reviewer checks it against the official source and re-locks. | `statements.lock.json` |
| 3 | **Lot conservation:** coins sold + coins left = coins before; cost of coins sold + cost still held = cost before. A sale never sells more than is held. | `KanonProofs/Lots.lean` |
| 4 | **Moving coins between your own wallets** is never a sale: every lot keeps its date, amount and cost. Each arrival matches at most one departure. | `KanonProofs/Lots.lean` |
| 5 | **Which coins count as sold, per country.** UK: each sale's same-day, 30-day, pool and unknown parts add up exactly to what was sold, no purchase is used twice, the pool never gives out more cost than it holds. Oldest first: only the oldest lots are used and every newer lot is untouched. Holding period (Germany's one-year rule, US long/short term): every coin sold is counted once as held-long or held-short. Average cost (Brazil, Japan, South Africa): cost taken + cost left = cost, and what's left keeps the average to within one unit. | `KanonProofs/UkMatch.lean`, `KanonProofs/Matching.lean` |
| 6 | **Rounding:** a shown amount is rounded half up, so it's never more than half a cent from the exact figure; KANON's own tax estimates are rounded up, so they never understate the tax and are less than a cent above it. (Where a tax office prescribes its rounding, like Brazil's DARF, the engine follows the office.) | `KanonProofs/Rounding.lean` |
| 7 | **Tax never falls as income rises:** bracket schedules after an allowance (fixed, or shrinking like the UK taper) and less a rebate are monotone, so the extra tax on a stacked gain is never negative. | `KanonProofs/Brackets.lean` |
| 8 | **Tax-year isolation:** changing one year's rules or events never changes an earlier year; a later year changes only through what's carried forward. | `KanonProofs/Years.lean` |
| 9 | **Reference models:** every tax engine (US worksheet with Tax Table rounding, Brazil month, UK same-day/30-day/pool, South Africa year, Japan total and moving average, Thailand with its 0.5% minimum, Nigeria's dollar gain at the sale-day rate and its bands) and the lot ledger has a small executable model here. `scripts/Vectors.lean` runs them on 2,160 generated cases (`vectors/reference.json`); CI regenerates the file, and the app's engines must give the same answers (exact, or within a penny per matched part where the model rounds down). Proven about the models: Brazil's exemption and monotone bands, Brazil's R$10 DARF minimum (nothing paid under R$10, and every centavo is paid or still carried), the US worksheet never above ordinary tax, South Africa's exclusion never flipping sign, Thailand's tax never falling as income rises and never below 0.5% of other income once that minimum applies (over 5,000 baht), Nigeria's tax never falling as income rises. | `KanonProofs/Reference.lean`, `scripts/Vectors.lean` |
| 10 | **Cash-out plans** sell only lots that exist, never the same lot twice, never more than a lot holds, and raise the cash asked for when the coins are there. | `KanonProofs/CashOut.lean` |
| 11 | **The chosen plan's tax is never higher than the country's default method's.** | `KanonProofs/CashOut.lean` |
| 15 | **No look-ahead:** the "missed sale" finding (best price since purchase) and the Watcher's check at a day use only prices up to that day: histories that agree up to then give the same answer, and the best price is always one actually seen in the window. Covers those two; the Options cards have no scores over time yet. | `KanonProofs/LookAhead.lean` |
| 17 | **Agent guardrail:** whatever the agent shows has passed the checker: every number is a small count or year, or within 50 cents / 0.5% of a number the engines produced (the app also accepts the same number written as a percent), and no banned word (advice, promises, jargon) appears. If no try passes, the fixed "can't answer" reply is shown, and it passes too. | `KanonProofs/Guard.lean` |
| 12 | **Price impact** (constant-product pools): the share of today's value you keep falls as you sell more, never exceeds what the fee allows, and the payout (rounded down) never breaks the pool's x·y = k. Concentrated-liquidity pools are shown as "about" in the app and not claimed here. | `KanonProofs/PriceImpact.lean` |
| 18 | **Creator fees:** the split (50% buy and burn, 30% running costs and team, 20% reserve) adds up exactly; rounding dust goes to the reserve (under 2 units); burns only lower supply; the swap's minimum-out bounds the price paid. | `KanonProofs/FeeSplit.lean` |
| 33 | **The reserve's ceiling:** the reserve takes its 20% only until it holds its ceiling (six months of running costs); what it can't take is burned. With the ceiling every unit of a fee still goes somewhere, the reserve never goes over it, the burn is never less than its 50%, a full reserve means everything except running costs is burned, and the burn is half the fee, short by at most one unit of rounding. These five proofs were found by Aristotle (Harmonic's prover, used as a tool; no affiliation) and are checked by Lean in this build like every other. | `KanonProofs/ReserveCap.lean` |
| 20 | **Proof-carrying reports:** every report can name this repo's commit and proof-bank hash; `manifest` prints them. | `scripts/proofs.py manifest` |
| 21 | **Exit ladder:** steps adding up to 100% or less never sell more than is held; each step sells no more than is left; UK tax-year boundary (5 / 6 April). | `KanonProofs/Ladder.lean` |
| 22 | **"Data complete" score** stays between 0 and 100, and explaining a transfer never lowers it. | `KanonProofs/Completeness.lean` |
| 23 | **Hold check:** holding more at every hour never lowers the 7-day average; the average never exceeds the highest balance; each wallet counted once; enough tokens always give access. | `KanonProofs/HoldCheck.lean` |
| 24 | **Payments:** every USDC paid in = burned + costs + pending, exactly; costs never exceed what's owed or dip into the burn. | `KanonProofs/Payments.lean` |
| 25 | **Exit-card grade:** after a take-profit step is reached, "followed" exactly when there's a recorded sale of that exact coin on a later day; "skipped" only from a 100% complete history, read after the step was reached, that includes the coin, with no sale since; never "skipped" while data is incomplete. | `KanonProofs/Grade.lean` |
| 27 | **Grouping never creates or loses coins:** sorting a file's movements into one pile per transaction keeps every wallet's balance of every coin, drops or duplicates nothing, and each pile holds only its own transaction. The app's grouping is tested against the same property on random histories. | `KanonProofs/Grouping.lean` |
| 28 | **Freshness:** a hand-checked number (rate, fee, tax rule) older than its limit is never shown without a "stale" label; a number with no readable date is always stale; the label never changes the number; the agent is only given numbers within their limit; once stale, a number stays stale until re-checked. | `KanonProofs/Fresh.lean` |
| 31 | **A swap is a sale, and the new coins cost what came in:** the old coins' sale price and the new coins' cost both add up exactly to the value received, split by value with the last coin taking what's left, so nothing is lost or invented between the old cost and the new one; no part exceeds the whole. | `KanonProofs/Rotation.lean` |
| 32 | **Brazil's monthly planner:** spreading a sale over months, this month only up to what's left of the R$35,000 limit after what's already been sold, then up to the limit each month: the months add up to exactly the amount, every month stays within the limit (this month counting what was already sold), no month sells nothing, and no plan within the limit finishes sooner (whatever it sells this month, it needs at least as many later months). | `KanonProofs/Spread.lean` |
| 29 | **Stock Token value:** a balance valued at the token's own price equals tokens × share price × shares per token; when a dividend raises the shares per token, the value added is exactly the extra shares at the share price, nothing when it doesn't change, and the token count never moves. | `KanonProofs/StockToken.lean` |
| 13 | **Splitting a sale across pools:** the app compares selling everything into each of a token's deepest pools with a split in proportion to each pool's coins, and shows the one that loses least. The split's parts add up to exactly the amount sold (the last pool takes what's left), what's shown is one of the candidates, and it never loses more than selling everything into any one of the pools. | `KanonProofs/Split.lean` |
| 30 | **Cash-out ranking:** routes are ranked by what they cost on your amount; a route that costs less is never ranked below one that costs more, and the ranking holds the same routes, each once (nothing dropped or added). | `KanonProofs/Ranking.lean` |

Planned next (not proven yet, so not claimed): simulator error bounds (14), alert timing (16),
cohort privacy (19) and fixed definitions in the take-profit report (26).

## Audited by Aristotle

On 8 October 2026 the whole bank was given to Aristotle (Harmonic's prover, used as a tool; no affiliation) with one
job: find where a theorem says less than the words next to it. Every theorem was true and none was an empty promise,
but it found 19 gaps, three of them real mistakes in the app (Thailand's top band, made-up amounts passing the
agent's checker, future-dated numbers never going stale). Those are fixed. The stronger statements it then proved
are in `KanonProofs/Tightened.lean`: a planner whose chosen plan is always valid, UK matching across a run of sales,
oldest-first by date, a one-year rule on calendar dates, and more. The full audit and what could not be proved are in
[`audit/AUDIT.md`](audit/AUDIT.md) and [`audit/TIGHTENED.md`](audit/TIGHTENED.md). Every proof it returned is
rebuilt and gated here like any other.

**Statement review:** the statements are locked but still waiting for a named human reviewer
(see `reviewedBy` in `statements.lock.json`).

## Models use whole units
Coins in their smallest unit (satoshis, wei) and money in cents, so every equation is exact.
Where something is rounded, the rule says which way and where the remainder goes.
