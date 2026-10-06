# KANON proof bank

The rules behind **KANON, the agent for your crypto gains**, machine-checked in Lean.
Anyone can re-check every proof for free:

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake build && python3 scripts/proofs.py gate && python3 scripts/proofs.py lock
```

**What a proof here means:** the maths in KANON's engines follows the rule as written below.
It does **not** mean the rule was read correctly from the law; that's what each country's
"Official-source tested" badge and its worked examples are for. Each engine has a reference model
here; the production code (TypeScript) is tested against the same cases.

## Status: 16 of the 31 planned checks done

| # | What is proven, in plain words | File |
|---|---|---|
| 1 | **Axiom gate:** the build fails if any proof skips a step (`sorry`), uses `native_decide`, or adds its own axiom. Only Lean's three standard axioms are allowed. | `scripts/proofs.py gate` |
| 2 | **Statement lock:** every theorem's statement is fingerprinted. Changing one fails the build until a reviewer checks it against the official source and re-locks. | `statements.lock.json` |
| 3 | **Lot conservation:** coins sold + coins left = coins before; cost of coins sold + cost still held = cost before. A sale never sells more than is held. | `KanonProofs/Lots.lean` |
| 4 | **Moving coins between your own wallets** is never a sale: every lot keeps its date, amount and cost. Each arrival matches at most one departure. | `KanonProofs/Lots.lean` |
| 5 | **Which coins count as sold, per country.** UK: each sale's same-day, 30-day, pool and unknown parts add up exactly to what was sold, no purchase is used twice, the pool never gives out more cost than it holds. Oldest first: only the oldest lots are used and every newer lot is untouched. Holding period (Germany's one-year rule, US long/short term): every coin sold is counted once as held-long or held-short. Average cost (Brazil, Japan, South Africa): cost taken + cost left = cost, and what's left keeps the average to within one unit. | `KanonProofs/UkMatch.lean`, `KanonProofs/Matching.lean` |
| 7 | **Tax never falls as income rises:** bracket schedules after an allowance (fixed, or shrinking like the UK taper) and less a rebate are monotone, so the extra tax on a stacked gain is never negative. | `KanonProofs/Brackets.lean` |
| 8 | **Tax-year isolation:** changing one year's rules or events never changes an earlier year; a later year changes only through what's carried forward. | `KanonProofs/Years.lean` |
| 10 | **Cash-out plans** sell only lots that exist, never the same lot twice, never more than a lot holds, and raise the cash asked for when the coins are there. | `KanonProofs/CashOut.lean` |
| 11 | **The chosen plan's tax is never higher than the country's default method's.** | `KanonProofs/CashOut.lean` |
| 17 | **Agent guardrail:** whatever the agent shows has passed the checker: every number is a small count or year, or within 50 cents / 0.5% of a number the engines produced (the app also accepts the same number written as a percent), and no banned word (advice, promises, jargon) appears. If no try passes, the fixed "can't answer" reply is shown, and it passes too. | `KanonProofs/Guard.lean` |
| 18 | **Creator fees:** the 50/30/20 split adds up exactly; rounding dust goes to the reserve (under 2 units); burns only lower supply; the swap's minimum-out bounds the price paid. | `KanonProofs/FeeSplit.lean` |
| 20 | **Proof-carrying reports:** every report can name this repo's commit and proof-bank hash; `manifest` prints them. | `scripts/proofs.py manifest` |
| 21 | **Exit ladder:** steps adding up to 100% or less never sell more than is held; each step sells no more than is left; UK tax-year boundary (5 / 6 April). | `KanonProofs/Ladder.lean` |
| 22 | **"Data complete" score** stays between 0 and 100, and explaining a transfer never lowers it. | `KanonProofs/Completeness.lean` |
| 23 | **Hold check:** holding more at every hour never lowers the 7-day average; the average never exceeds the highest balance; each wallet counted once; enough tokens always give access. | `KanonProofs/HoldCheck.lean` |
| 24 | **Payments:** every USDC paid in = burned + costs + pending, exactly; costs never exceed what's owed or dip into the burn. | `KanonProofs/Payments.lean` |

Started, not counted until every engine has one: reference models (9). Brazil, South Africa and the lot ledger have
executable models in `KanonProofs/Reference.lean`; `scripts/Vectors.lean` writes 720 cases to `vectors/reference.json`,
CI regenerates them, and the app's engines must match them exactly. US, UK and Japan still to do.

Planned next (not proven yet, so not claimed): rounding (6), price impact (12, 13),
simulator error bounds (14), no look-ahead (15), alert timing (16),
cohort privacy (19), and 25–31.

**Statement review:** the statements are locked but still waiting for a named human reviewer
(see `reviewedBy` in `statements.lock.json`).

## Models use whole units
Coins in their smallest unit (satoshis, wei) and money in cents, so every equation is exact.
Where something is rounded, the rule says which way and where the remainder goes.
