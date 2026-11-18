# Statement review, 15 November 2026: Italy (quadro RT/RW, IVCA, deadlines)

Reviewer: an independent AI reviewer (a fresh agent, read-only), given KanonProofs/Italy.lean (d3286f9, 171 new statements, 0 changed, 0 removed) and kanon-app 7583be0 (src/lib/engine/it.ts, src/lib/report/it.ts, the IVCA note in ReportPdf.tsx). It checked each statement against its name, its docstring, the app code and the law: L. 199/2025 c.28 and L. 207/2024 c.24-25, read on normattiva. For RT57, Circolare 30/E and the Fascicolo 1 rounding rule it used the app's quoted wording, because the Agenzia delle Entrate pages could not be fetched.

Result: OK to lock, no blocking problems. The model matches the app on LIFO take and the run order; swap classification and the part swap (Cases A and B); the euro EMT rule by statement day; the €2,000 threshold to 2024 and four-year losses; the 2026 split (cents-up tax, whole-euro form); the readings (common start, pick, now); IVCA, the instalments and the deadlines for 2023-2100. None of the monotonicity theorems has an unsatisfiable hypothesis.

Wording notes, fixed in the docstrings before locking:

- case_b said vg > 0 where the hypothesis is vg ≠ 0.
- same_kind_untaxed and nft_rules now say that grouping by kind is KANON's reading of Circolare 30/E.
- instalments uses €52 for the law's "over €51.65", the same for whole-euro amounts.

The holiday list has no Easter Monday, which cannot affect the modelled dates.
