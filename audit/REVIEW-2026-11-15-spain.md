# Statement review, 15 November 2026: Spain (LIRPF, Modelo 100 boxes 1800-1814)

Reviewer: an independent AI reviewer (a fresh agent, read-only, given `KanonProofs/Spain.lean` and kanon-app
`src/lib/engine/lots.ts` and the Spanish engine), checking each statement against the primary sources: LIRPF arts.
33.5.e, 37.2, 46, 49, 66 and 76, DT 7ª; AEAT Manual Renta 2024, ch. 11-12. 3 rounds.

Round 1: not lockable. The art. 33.5.e wording was corrected (the loss is put off when the same coin is bought again
within the year after the sale, and counted when those coins are sold). Found in the app: `Book.add` put a lot moved
between the person's own wallets after the other lots bought that day, so a later FIFO sale took a different lot
(fixed in kanon-app 268c7fa: each lot carries its arrival order). Modelled as `seq`, with `transfer_same_sale` proved
from any pool the ledger can reach (`Reach`), and the cases `same_day_move` and `two_moves`.

Round 2: not lockable. Found in the app: a wrap (a move with `toAsset`, scaled by `toQty`) kept the source's rank, so
two wraps of one lot at different rates left two slices of one place at different costs per coin, and a later move
changed a later sale (2 coins for 200, wrapped 1 → 1 and 1 → 1/2: a sale after a move cost 150, not 100). A first fix
(a new rank per wrapped slice) broke acquisition order on a round trip (ETH → WETH → ETH put lot A behind lot B of the
same day). Fixed in kanon-app a4a0731 (live as bb181d6, engine code identical): a rank is a root and a step, ordered
by day, root, step; a wrapped slice keeps its root and takes a new step. Modelled as `seq : ℕ × ℕ`, `Reach.sent` and
`Reach.wrapped`, with `good_of_reach` extended, and the cases `wrap_then_move` (100) and `round_trip` (A stays first).
Also done: `sell_oldest` restated in the pool's order (`before p.lot x`); the header's departures name crumbs,
`toQty` scaling, the slices' new ids and the shared rank counter.

Round 3 (on 189aeb7): OK to lock, no problems. One docstring wording fixed before locking: `transfer_same_sale`
names wraps among the steps that reach a pool.
