# Statement review, 15 November 2026: #57 France, NFTs (art. 150 VH bis as amended by loi 2026-534 art. 91)

Reviewer: an independent AI reviewer (a fresh agent, read-only, given `KanonProofs/France.lean` and kanon-app
`src/lib/engine/fr.ts`, `src/lib/report/fr.ts` at claude/fr-nft-fix 5e702d5), checking each new statement against
CGI art. 150 VH bis and 150 VH ter and loi n° 2026-534 art. 91 (Légifrance JORFARTI000054310089: NFTs leave
150 VH bis for cessions from 1 January 2026; no transitional rule for line 220, so KANON's cut is a policy choice
that can only raise tax). 2 rounds.

Round 1 (at e51253e): not lockable. Blocking: `nft_pass_unknown_cut` and `nft_move_mixed_cut` covered only a cut
straight after the pass or move. Recommended: tie the parts' bounds to the start of a run; widen
`nft_given_no_line` / `nft_given_l51` to swaps that cross from 2026; state the kept-at-cost NFT-for-receipt case.

Round 2 (at 54d9364): OK to lock. `nft_unknown_persists` keeps an unknown part unknown through any operations short
of the cut or all of that NFT leaving (matching the app: only a leave with share ≥ 1 sets the part to zero), and
both cut theorems are restated over `… ++ mid ++ [off]`; the hypothesis is reachable (a pass with an unknown share,
or an NFT fee of unknown value) and admits ordinary purchases and cessions. `nft_parts_run` and
`nft_cut_no_loss_run` hold from `nstart`. `bookSwapN_kept` and `nft_kept_nft_receipt` match the app (move/pass
flows only, nothing listed).

Accepted as stated: an unknown cut gives no 2026+ figure rather than an upper bound (policy, put to Matt); before
2026 the model follows the chain's `nft` flag where the app uses `nftLike` for a receipt standing for an NFT
(documented modelling gap).
