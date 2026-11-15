import KanonProofs.Spain

namespace Kanon.Spain

/-! ## 5. Wraps and art. 33.5.e: coins bought again counted in the purchase's own coins (kanon-app bf3c84f) -/

/-- A lot with how many coins of its acquisition it stands for (the code's `origin`, lots.ts:147-148): `none` for a lot
in its acquisition's own coins, which is every lot until a wrap with a `toQty` gives it other amounts. -/
abbrev OLot := Lot × Option ℚ

/-- A slice a sale or a move takes, with the acquisition's coins it stands for (`Disposal.originQty`, lots.ts:124),
`none` when they are its own. -/
abbrev OPick := Pick × Option ℚ

/-- The acquisition's coins a lot stands for: its `origin`, else its own coins. -/
def orig (x : OLot) : ℚ := x.2.getD x.1.qty

/-- What `src/lib/report/es.ts` passes to `esWash` for a slice sold (`d.originQty ?? d.qty`, line 120). -/
def originQty (p : OPick) : ℚ := p.2.getD p.1.take

/-- `sell` with each lot's `origin` (lots.ts:250-251, 259): a slice of part of a lot stands for `origin × take ÷ qty`
of its coins and the rest of the lot for what is left; a slice of all of it takes all of its `origin`. -/
def osell : List OLot → ℚ → List OPick × List OLot
  | [], _ => ([], [])
  | (l, o) :: ls, q =>
    if q ≤ 0 then ([], (l, o) :: ls)
    else if q < l.qty then
      ([(⟨l, q, l.cost * q / l.qty⟩, o.map fun o => o * q / l.qty)],
        ({ l with qty := l.qty - q, cost := l.cost - l.cost * q / l.qty }, o.map fun o => o - o * q / l.qty) :: ls)
    else
      ((⟨l, l.qty, l.cost * l.qty / l.qty⟩, o) :: (osell ls (q - l.qty)).1, (osell ls (q - l.qty)).2)

/-- `add` with each lot's `origin`, which it keeps. -/
def oadd (x : OLot) : List OLot → List OLot
  | [] => [x]
  | y :: ys => if before y.1 x.1 then y :: oadd x ys else x :: y :: ys

/-- `sale` with `origin`: the lot at cost 0 for coins missing has none (`unknownLot`). -/
def osale (ls : List OLot) (q : ℚ) (id wallet date seq : ℕ) : List OPick × List OLot :=
  if held (ls.map Prod.fst) < q then osell (oadd (⟨id, wallet, date, q - held (ls.map Prod.fst), 0, (seq, 0)⟩, none) ls) q
  else osell ls q

/-- `transfer` with `origin` (lots.ts:192-194): each slice moved stands for `origin × take ÷ qty` of its lot's coins,
all that is left when the lot moves whole. -/
def otransfer (ls : List OLot) (q : ℚ) (dest : ℕ) : List OLot :=
  (osell ls q).1.foldl (fun b p => oadd ({ p.1.lot with wallet := dest, qty := p.1.take, cost := p.1.basis }, p.2) b)
    (osell ls q).2

/-- `move` with `origin`: the slice for coins missing has none. -/
def omove (ls : List OLot) (q : ℚ) (id dest date seq : ℕ) : List OLot :=
  if held (ls.map Prod.fst) < q then oadd (⟨id, dest, date, q - held (ls.map Prod.fst), 0, (seq, 0)⟩, none) (otransfer ls q dest)
  else otransfer ls q dest

/-- A wrapped slice's `origin` (lots.ts:213-215): with a `toQty`, a slice that had none gets the coins it was taken as,
before they are scaled, and one that had one keeps it (so wraps one after another multiply); with no `toQty` the coins
are not scaled and the slice keeps what it had. -/
def wrapOrigin (tq : Option ℚ) (p : OPick) : Option ℚ :=
  match tq with
  | none => p.2
  | some _ => some (originQty p)

/-- `wrapSlices` with `origin`. -/
def owrapSlices : List OPick → ℕ → Option ℚ → ℚ → ℕ → List OLot
  | [], _, _, _, _ => []
  | p :: ps, dest, tq, all, c =>
    ({ p.1.lot with wallet := dest, qty := scaled tq all p.1.take, cost := p.1.basis, seq := (p.1.lot.seq.1, c) },
      wrapOrigin tq p) :: owrapSlices ps dest tq all (c + 1)

/-- `wrapIn` with `origin`: the slices of the pool's lots, then the unknown-cost slice, which has none. -/
def owrapIn (T L : List OLot) (q : ℚ) (id w date s dest : ℕ) (tq : Option ℚ) (c0 : ℕ) : List OLot :=
  (owrapSlices (osell L q).1 dest tq ((wrapPicks (L.map Prod.fst) q id w date s).map Pick.take).sum c0 ++
      (if held (L.map Prod.fst) < q then
        [((⟨id, dest, date, scaled tq ((wrapPicks (L.map Prod.fst) q id w date s).map Pick.take).sum
          (q - held (L.map Prod.fst)), 0, (s, 0)⟩ : Lot), none)]
      else [])).foldl (fun b l => oadd l b) T

/-! ### The lots are the ledger's: `origin` only rides along -/

theorem oadd_fst (x : OLot) (L : List OLot) : (oadd x L).map Prod.fst = add x.1 (L.map Prod.fst) := by
  induction L with
  | nil => simp [oadd, add]
  | cons y ys ih => simp only [oadd, add, List.map_cons]; split_ifs <;> simp [ih]

theorem osell_fst (L : List OLot) (q : ℚ) :
    (osell L q).1.map Prod.fst = (sell (L.map Prod.fst) q).1 ∧
      (osell L q).2.map Prod.fst = (sell (L.map Prod.fst) q).2 := by
  induction L generalizing q with
  | nil => simp [osell, sell]
  | cons x ls ih =>
    obtain ⟨l, o⟩ := x
    simp only [osell, sell, List.map_cons]
    split_ifs <;> simp [ih]

theorem foldl_oadd_fst (xs : List OLot) (T : List OLot) :
    (xs.foldl (fun b l => oadd l b) T).map Prod.fst = (xs.map Prod.fst).foldl (fun b l => add l b) (T.map Prod.fst) := by
  induction xs generalizing T with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, oadd_fst]

theorem owrapSlices_fst (ps : List OPick) (dest : ℕ) (tq : Option ℚ) (all : ℚ) (c : ℕ) :
    (owrapSlices ps dest tq all c).map Prod.fst = wrapSlices (ps.map Prod.fst) dest tq all c := by
  induction ps generalizing c with
  | nil => simp [owrapSlices, wrapSlices]
  | cons p ps ih => simp [owrapSlices, wrapSlices, ih]

/-- **ES-8** The ledger with `origin` runs the ledger: its lots, picks and pools are `sale`'s, `move`'s and `wrapIn`'s. -/
theorem origin_rides_along (L T : List OLot) (q : ℚ) (id w date seq dest s : ℕ) (tq : Option ℚ) (c0 : ℕ) :
    ((osale L q id w date seq).1.map Prod.fst = (sale (L.map Prod.fst) q id w date seq).1 ∧
      (osale L q id w date seq).2.map Prod.fst = (sale (L.map Prod.fst) q id w date seq).2) ∧
    (omove L q id dest date seq).map Prod.fst = move (L.map Prod.fst) q id dest date seq ∧
    (osell L q).2.map Prod.fst = (sell (L.map Prod.fst) q).2 ∧
    (owrapIn T L q id w date s dest tq c0).map Prod.fst =
      wrapIn (T.map Prod.fst) (L.map Prod.fst) q id w date s dest tq c0 := by
  refine ⟨?_, ?_, (osell_fst L q).2, ?_⟩
  · unfold osale sale; split_ifs
    · have := osell_fst (oadd (⟨id, w, date, q - held (L.map Prod.fst), 0, (seq, 0)⟩, none) L) q
      rw [oadd_fst] at this; exact this
    · exact osell_fst L q
  · have ht : (otransfer L q dest).map Prod.fst = transfer (L.map Prod.fst) q dest := by
      unfold otransfer transfer
      rw [← (osell_fst L q).1, ← (osell_fst L q).2]
      generalize (osell L q).2 = R
      induction (osell L q).1 generalizing R with
      | nil => simp
      | cons p ps ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, oadd_fst]
    unfold omove move; split_ifs
    · rw [oadd_fst, ht]
    · exact ht
  · unfold owrapIn wrapIn
    rw [foldl_oadd_fst, List.map_append, owrapSlices_fst, (osell_fst L q).1]
    split_ifs <;> simp

/-! ### The acquisition's coins are kept: held plus sold is what was acquired -/

/-- The coins of acquisition `i` a pool stands for. -/
def originAt (i : ℕ) (P : List OLot) : ℚ := ((P.filter fun x => x.1.id = i).map orig).sum

/-- The coins of acquisition `i` some slices stand for. -/
def pickedOf (i : ℕ) (ps : List OPick) : ℚ := ((ps.filter fun p => p.1.lot.id = i).map originQty).sum

/-- The sales `src/lib/report/es.ts` passes to `esWash` for the slices of one sale (line 120): the lot's id (the code
cuts a slice's `~n`, which the model never adds), the day and `originQty ?? qty`. -/
def saleRows (date : ℕ) (ps : List OPick) : List SaleOfLot := ps.map fun p => ⟨p.1.lot.id, date, originQty p⟩

/-- The coins of lot `i` the sales name. -/
def soldOf (i : ℕ) (ss : List SaleOfLot) : ℚ := ((ss.filter fun s => s.lot = i).map SaleOfLot.qty).sum

theorem originAt_append (i : ℕ) (a b : List OLot) : originAt i (a ++ b) = originAt i a + originAt i b := by
  simp [originAt, List.filter_append]

theorem soldOf_append (i : ℕ) (a b : List SaleOfLot) : soldOf i (a ++ b) = soldOf i a + soldOf i b := by
  simp [soldOf, List.filter_append]

theorem soldOf_rows (i date : ℕ) (ps : List OPick) : soldOf i (saleRows date ps) = pickedOf i ps := by
  induction ps with
  | nil => simp [soldOf, saleRows, pickedOf]
  | cons p ps ih =>
    unfold soldOf saleRows pickedOf at *
    by_cases h : p.1.lot.id = i <;> simp [h, List.filter_cons] at ih ⊢ <;> rw [ih]

theorem oadd_origin (i : ℕ) (x : OLot) (P : List OLot) :
    originAt i (oadd x P) = originAt i P + originAt i [x] := by
  induction P with
  | nil => simp [oadd, originAt]
  | cons y ys ih =>
    unfold oadd; split_ifs
    · have : originAt i (y :: oadd x ys) = originAt i [y] + originAt i (oadd x ys) := by
        rw [← originAt_append]; rfl
      rw [this, ih, show y :: ys = [y] ++ ys from rfl, originAt_append]; ring
    · rw [show x :: y :: ys = [x] ++ (y :: ys) from rfl, originAt_append]; ring

theorem osell_origin (i : ℕ) (L : List OLot) (q : ℚ) :
    originAt i (osell L q).2 + pickedOf i (osell L q).1 = originAt i L := by
  induction L generalizing q with
  | nil => simp [osell, originAt, pickedOf]
  | cons x ls ih =>
    obtain ⟨l, o⟩ := x
    simp only [osell]
    split_ifs with h1 h2
    · simp [pickedOf]
    · by_cases e : l.id = i
      · cases o <;> simp [originAt, pickedOf, orig, originQty, List.filter_cons, e] <;> ring
      · simp [originAt, pickedOf, List.filter_cons, e]
    · have := ih (q - l.qty)
      by_cases e : l.id = i
      · simp only [originAt, pickedOf, List.filter_cons, e, decide_true, if_true, List.map_cons,
          List.sum_cons] at this ⊢
        simp only [orig, originQty]; linarith
      · simp only [originAt, pickedOf, List.filter_cons, e, decide_false, Bool.false_eq_true, if_false] at this ⊢
        exact this

theorem foldl_oadd_origin (i : ℕ) (xs T : List OLot) :
    originAt i (xs.foldl (fun b l => oadd l b) T) = originAt i T + originAt i xs := by
  induction xs generalizing T with
  | nil => simp [originAt]
  | cons x xs ih =>
    simp only [List.foldl_cons]; rw [ih, oadd_origin, show x :: xs = [x] ++ xs from rfl, originAt_append]; ring

theorem otransfer_origin (i : ℕ) (L : List OLot) (q : ℚ) (dest : ℕ) :
    originAt i (otransfer L q dest) = originAt i L := by
  unfold otransfer
  rw [← osell_origin i L q]
  generalize (osell L q).2 = R
  induction (osell L q).1 generalizing R with
  | nil => simp [pickedOf]
  | cons p ps ih =>
    simp only [List.foldl_cons]; rw [ih, oadd_origin]
    by_cases e : p.1.lot.id = i <;> simp [pickedOf, originAt, orig, originQty, e, List.filter_cons] <;> ring

theorem owrapSlices_origin (i : ℕ) (ps : List OPick) (dest : ℕ) (tq : Option ℚ) (all : ℚ) (c : ℕ) :
    originAt i (owrapSlices ps dest tq all c) = pickedOf i ps := by
  induction ps generalizing c with
  | nil => simp [owrapSlices, originAt, pickedOf]
  | cons p ps ih =>
    have := ih (c + 1)
    unfold owrapSlices
    by_cases e : p.1.lot.id = i
    · cases tq <;> simp [originAt, pickedOf, List.filter_cons, e, orig, wrapOrigin, originQty, scaled] at this ⊢ <;>
        rw [this]
    · simp only [originAt, pickedOf, List.filter_cons, e, decide_false, Bool.false_eq_true, if_false] at this ⊢
      exact this

/-! ### Many pools: one per coin -/

theorem sum_step (i : ℕ) (W : ℕ → List OLot) (C : Finset ℕ) (hW : ∀ x ∉ C, W x = []) (a : ℕ) (P : List OLot) :
    ∑ x ∈ insert a C, originAt i (Function.update W a P x) = ∑ x ∈ C, originAt i (W x) - originAt i (W a) + originAt i P := by
  have hins : ∑ x ∈ insert a C, originAt i (W x) = ∑ x ∈ C, originAt i (W x) := by
    by_cases ha : a ∈ C
    · rw [Finset.insert_eq_of_mem ha]
    · rw [Finset.sum_insert ha, hW a ha]; simp [originAt]
  have hm : a ∈ insert a C := Finset.mem_insert_self a C
  rw [← hins, ← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm, Function.update_self,
    Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])]
  ring

theorem step_support (W : ℕ → List OLot) (C : Finset ℕ) (hW : ∀ x ∉ C, W x = []) (a : ℕ) (P : List OLot) :
    ∀ x ∉ insert a C, Function.update W a P x = [] := by
  intro x hx
  rw [Finset.mem_insert, not_or] at hx
  rw [Function.update_of_ne hx.1]; exact hW x hx.2

/-- The ledger with `origin`, coin by coin (`W a` is coin `a`'s pool, `C` the coins it has touched), with the sales it
passes to `esWash` (`ss`) and the coins each acquisition brought (`B`): a purchase; a sale (with the lot at cost 0
for coins missing, its own acquisition); a move between own wallets; a wrap from coin `a` to coin `a'`, the same coin
too (its unknown-cost slice an acquisition of the coins that arrive). Nothing is asked of the lots' places, so this
covers every pool the ledger reaches and more. -/
inductive OReach : (ℕ → List OLot) → Finset ℕ → List SaleOfLot → (ℕ → ℚ) → Prop
  | empty : OReach (fun _ => []) ∅ [] (fun _ => 0)
  | bought (W C ss B) (a : ℕ) (l : Lot) : OReach W C ss B →
      OReach (Function.update W a (oadd (l, none) (W a))) (insert a C) ss (Function.update B l.id (B l.id + l.qty))
  | sold (W C ss B) (a : ℕ) (q : ℚ) (id w date seq : ℕ) : OReach W C ss B →
      OReach (Function.update W a (osale (W a) q id w date seq).2) (insert a C)
        (ss ++ saleRows date (osale (W a) q id w date seq).1)
        (if held ((W a).map Prod.fst) < q then Function.update B id (B id + (q - held ((W a).map Prod.fst))) else B)
  | moved (W C ss B) (a : ℕ) (q : ℚ) (id dest date seq : ℕ) : OReach W C ss B →
      OReach (Function.update W a (omove (W a) q id dest date seq)) (insert a C) ss
        (if held ((W a).map Prod.fst) < q then Function.update B id (B id + (q - held ((W a).map Prod.fst))) else B)
  | wrapped (W C ss B) (a a' : ℕ) (q : ℚ) (id w date s dest : ℕ) (tq : Option ℚ) (c0 : ℕ) : OReach W C ss B →
      OReach (Function.update (Function.update W a (osell (W a) q).2) a'
          (owrapIn (Function.update W a (osell (W a) q).2 a') (W a) q id w date s dest tq c0))
        (insert a' (insert a C)) ss
        (if held ((W a).map Prod.fst) < q then
          Function.update B id (B id + scaled tq (((wrapPicks ((W a).map Prod.fst) q id w date s).map Pick.take).sum)
            (q - held ((W a).map Prod.fst)))
        else B)

theorem update_add (B : ℕ → ℚ) (id i : ℕ) (d : ℚ) :
    Function.update B id (B id + d) i = B i + (if id = i then d else 0) := by
  by_cases e : id = i
  · subst e; simp
  · rw [Function.update_of_ne (Ne.symm e), if_neg e, add_zero]

/-- **ES-8a** The coins of an acquisition are kept through sales, moves and wraps at any rates: for each acquisition
`i`, the coins of it still held, in every coin's pool, plus the coins of it in the sales passed to `esWash`, are the
coins it brought; and the pools of coins never touched are empty. -/
theorem origin_conserved {W : ℕ → List OLot} {C : Finset ℕ} {ss : List SaleOfLot} {B : ℕ → ℚ}
    (h : OReach W C ss B) :
    (∀ a ∉ C, W a = []) ∧ ∀ i, ∑ a ∈ C, originAt i (W a) + soldOf i ss = B i := by
  induction h with
  | empty => exact ⟨fun _ _ => rfl, fun i => by simp [soldOf]⟩
  | bought W C ss B a l _ ih =>
    refine ⟨step_support W C ih.1 a _, fun i => ?_⟩
    rw [sum_step i W C ih.1, oadd_origin, update_add, ← ih.2 i]
    by_cases e : l.id = i <;> simp [originAt, orig, e]; ring
  | sold W C ss B a q id w date seq _ ih =>
    refine ⟨step_support W C ih.1 a _, fun i => ?_⟩
    rw [sum_step i W C ih.1, soldOf_append, soldOf_rows]
    have e1 := osell_origin i
    unfold osale; split_ifs with hs
    · rw [update_add, ← ih.2 i]
      have := e1 (oadd (⟨id, w, date, q - held ((W a).map Prod.fst), 0, (seq, 0)⟩, none) (W a)) q
      rw [oadd_origin] at this
      by_cases e : id = i <;> simp [originAt, orig, e] at this ⊢ <;> linarith
    · rw [← ih.2 i]; have := e1 (W a) q; linarith
  | moved W C ss B a q id dest date seq _ ih =>
    refine ⟨step_support W C ih.1 a _, fun i => ?_⟩
    rw [sum_step i W C ih.1]
    unfold omove; split_ifs with hs
    · rw [update_add, ← ih.2 i, oadd_origin, otransfer_origin]
      by_cases e : id = i <;> simp [originAt, orig, e]; ring
    · rw [← ih.2 i, otransfer_origin]; ring
  | wrapped W C ss B a a' q id w date s dest tq c0 _ ih =>
    have s1 := step_support W C ih.1 a (osell (W a) q).2
    refine ⟨fun x hx => ?_, fun i => ?_⟩
    · exact step_support _ _ s1 a' _ x hx
    · rw [sum_step i _ _ s1, sum_step i W C ih.1]
      unfold owrapIn
      rw [foldl_oadd_origin, originAt_append, owrapSlices_origin]
      have e1 := osell_origin i (W a) q
      split_ifs with hs
      · rw [update_add, ← ih.2 i]
        by_cases e : id = i <;> simp [originAt, orig, e] at e1 ⊢ <;> linarith
      · rw [← ih.2 i]; simp [originAt] at e1 ⊢; linarith

/-! ### Art. 33.5.e: a sale of all the coins bought again counts all the loss put off on them -/

/-- The coins of purchase `i` (as `esWash` takes them), still free in the first loop, and carrying parts not yet sold. -/
def boughtOf (i : ℕ) (buys : List Buy) : ℚ := ((buys.filter fun b => b.id = i).map Buy.qty).sum
def freeOf (i : ℕ) (fs : List (Buy × ℚ)) : ℚ := ((fs.filter fun x => x.1.id = i).map Prod.snd).sum
def onBuy (i : ℕ) (ps : List Part) : ℚ := ((ps.filter fun p => p.buy = i).map Part.qLeft).sum

theorem matchLoss_split (l : Loss) (need : ℚ) (fs : List (Buy × ℚ)) (i : ℕ) :
    freeOf i (matchLoss l need fs).1 + freeOf i (matchLoss l need fs).2 = freeOf i fs ∧
      ∀ x ∈ (matchLoss l need fs).1, ∃ y ∈ fs, x.1 = y.1 ∧ (x.2 = y.2 ∨ 0 ≤ x.2) := by
  induction fs generalizing need with
  | nil => simp [matchLoss, freeOf]
  | cons bf rest ih =>
    obtain ⟨b, free⟩ := bf
    unfold matchLoss; split_ifs with h0 h1
    · exact ⟨by simp [freeOf], fun x hx => ⟨x, hx, rfl, Or.inl rfl⟩⟩
    · obtain ⟨a1, a2⟩ := ih (need - min free need)
      refine ⟨?_, fun x hx => ?_⟩
      · unfold freeOf at *
        by_cases e : b.id = i <;> simp [e, List.filter_cons] at a1 ⊢ <;> linarith
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨(b, free), by simp, rfl, Or.inr (by simp)⟩
        · obtain ⟨y, hy, r⟩ := a2 x hx; exact ⟨y, by simp [hy], r⟩
    · obtain ⟨a1, a2⟩ := ih need
      refine ⟨?_, fun x hx => ?_⟩
      · unfold freeOf at *
        by_cases e : b.id = i <;> simp [e, List.filter_cons] at a1 ⊢ <;> linarith
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨(b, free), by simp, rfl, Or.inl rfl⟩
        · obtain ⟨y, hy, r⟩ := a2 x hx; exact ⟨y, by simp [hy], r⟩

theorem freeOf_nonneg (i : ℕ) (fs : List (Buy × ℚ)) (h : ∀ x ∈ fs, 0 < x.2) : 0 ≤ freeOf i fs := by
  unfold freeOf
  exact List.sum_nonneg (fun a ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; exact (h x (List.mem_filter.mp hx).1).le)

theorem onBuy_new (i L y : ℕ) (xs : List (Buy × ℚ)) (off got : ℚ) :
    onBuy i (xs.map fun x => (⟨L, y, x.1.id, off * x.2 / got, off * x.2 / got, x.2, x.2⟩ : Part)) = freeOf i xs := by
  induction xs with
  | nil => simp [onBuy, freeOf]
  | cons x xs ih =>
    unfold onBuy freeOf at *
    by_cases e : x.1.id = i <;> simp [e, List.filter_cons] at ih ⊢ <;> rw [ih]

theorem onBuy_append (i : ℕ) (a b : List Part) : onBuy i (a ++ b) = onBuy i a + onBuy i b := by
  simp [onBuy, List.filter_append]

/-- The first loop: free coins plus coins carrying parts are at most the coins bought; a free purchase is one of the
purchases, with its coins free not below 0 unless untouched; every part's coins are above 0. -/
def J (buys : List Buy) (st : W1) : Prop :=
  (∀ i, freeOf i st.free + onBuy i st.parts ≤ boughtOf i buys) ∧
    (∀ x ∈ st.free, x.1 ∈ buys ∧ (x.2 = x.1.qty ∨ 0 ≤ x.2)) ∧ ∀ p ∈ st.parts, 0 < p.qLeft

theorem washLoss_J (buys : List Buy) (st : W1) (l : Loss) (h : J buys st) : J buys (washLoss st l) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold washLoss
  dsimp only
  split_ifs with ha hg
  · exact ⟨h1, h2, h3⟩
  · push_neg at ha
    have pos := (matchLoss_sum l l.qty st.free ha.2.le).2
    refine ⟨fun i => ?_, fun x hx => ?_, h3⟩
    · have := (matchLoss_split l l.qty st.free i).1
      have := freeOf_nonneg i _ pos
      have := h1 i; linarith
    · obtain ⟨y, hy, e, r⟩ := (matchLoss_split l l.qty st.free 0).2 x hx
      obtain ⟨b1, b2⟩ := h2 y hy
      refine ⟨e ▸ b1, ?_⟩
      rcases r with r | r
      · rcases b2 with b2 | b2
        · left; rw [r, e, b2]
        · right; rw [r]; exact b2
      · right; exact r
  · push_neg at ha
    have pos := (matchLoss_sum l l.qty st.free ha.2.le).2
    refine ⟨fun i => ?_, fun x hx => ?_, fun p hp => ?_⟩
    · have := (matchLoss_split l l.qty st.free i).1
      have := h1 i
      rw [onBuy_append, onBuy_new]; linarith
    · obtain ⟨y, hy, e, r⟩ := (matchLoss_split l l.qty st.free 0).2 x hx
      obtain ⟨b1, b2⟩ := h2 y hy
      refine ⟨e ▸ b1, ?_⟩
      rcases r with r | r
      · rcases b2 with b2 | b2
        · left; rw [r, e, b2]
        · right; rw [r]; exact b2
      · right; exact r
    · rcases List.mem_append.mp hp with hp | hp
      · exact h3 p hp
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact pos x hx

theorem washLosses_J (buys : List Buy) (ls : List Loss) (st : W1) (h : J buys st) : J buys (ls.foldl washLoss st) := by
  induction ls generalizing st with
  | nil => exact h
  | cons l ls ih => exact ih _ (washLoss_J buys st l h)

/-- A part as the second loop keeps it: its coins not yet sold not below 0, and none of it waiting once they are 0. -/
def Q (p : Part) : Prop := 0 ≤ p.qLeft ∧ (p.qLeft ≤ 0 → p.left = 0)

theorem onBuy_nonneg (i : ℕ) (ps : List Part) (h : ∀ p ∈ ps, Q p) : 0 ≤ onBuy i ps := by
  unfold onBuy
  exact List.sum_nonneg (fun a ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; exact (h x (List.mem_filter.mp hx).1).1)

theorem arith_take (ql A R sold : ℚ) (h2 : 0 < sold) (hn : 0 ≤ R)
    (h : A ≤ max (R - max (sold - min sold ql) 0) 0) : ql - min sold ql + A ≤ max (ql + R - max sold 0) 0 := by
  rw [max_eq_left h2.le]
  rcases min_cases sold ql with ⟨m1, m2⟩ | ⟨m1, m2⟩ <;> rw [m1] at h ⊢
  · rw [sub_self, max_self, sub_zero, max_eq_left hn] at h; exact le_max_of_le_left (by linarith)
  · rw [max_eq_left (by linarith : (0 : ℚ) ≤ sold - ql)] at h
    calc ql - ql + A = A := by ring
      _ ≤ _ := h
      _ = _ := by congr 1; ring

theorem release_Q (lot i : ℕ) (sold : ℚ) (ps : List Part) (h : ∀ p ∈ ps, Q p) :
    (∀ p ∈ (release lot sold ps).1, Q p) ∧
      (lot = i → onBuy i (release lot sold ps).1 ≤ max (onBuy i ps - max sold 0) 0) ∧
      (lot ≠ i → onBuy i (release lot sold ps).1 = onBuy i ps) := by
  induction ps generalizing sold with
  | nil => simp [release, onBuy]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ih' := fun s => ih s (fun x hx => h x (by simp [hx]))
    have hn := onBuy_nonneg i ps (fun x hx => h x (by simp [hx]))
    unfold release
    split_ifs with h1 h2 h3
    · obtain ⟨a, b, c⟩ := ih' sold
      refine ⟨fun x hx => ?_, fun e => ?_, fun e => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx; exact hp; exact a x hx
      · have := b e; subst e
        simp only [onBuy, List.filter_cons, show ¬ p.buy = lot from h1, decide_false, Bool.false_eq_true,
          if_false] at this ⊢
        exact this
      · have := c e
        unfold onBuy at this ⊢
        by_cases e2 : p.buy = i <;> simp [e2, List.filter_cons] at this ⊢ <;> linarith
    · refine ⟨h, fun e => ?_, fun e => rfl⟩
      have := onBuy_nonneg i (p :: ps) h
      rw [max_eq_right (show sold ≤ 0 by linarith), sub_zero, max_eq_left this]
    · obtain ⟨a, b, c⟩ := ih' sold
      have hz : p.qLeft = 0 := le_antisymm h3 hp.1
      refine ⟨fun x hx => ?_, fun e => ?_, fun e => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx; exact hp; exact a x hx
      · have := b e; subst e
        have hb : p.buy = lot := not_not.mp h1
        simp only [onBuy, List.filter_cons, hb, decide_true, if_true, List.map_cons, List.sum_cons, hz,
          zero_add] at this ⊢
        exact this
      · have := c e
        unfold onBuy at this ⊢
        by_cases e2 : p.buy = i <;> simp [e2, List.filter_cons] at this ⊢ <;> linarith
    · push_neg at h2 h3
      obtain ⟨a, b, c⟩ := ih' (sold - min sold p.qLeft)
      refine ⟨fun x hx => ?_, fun e => ?_, fun e => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · refine ⟨by have := min_le_right sold p.qLeft; dsimp only; linarith, fun hq => ?_⟩
          dsimp only at hq ⊢; rw [if_pos hq]; ring
        · exact a x hx
      · have := b e; subst e
        have hb : p.buy = lot := not_not.mp h1
        simp only [onBuy, List.filter_cons, hb, decide_true, if_true, List.map_cons, List.sum_cons] at this hn ⊢
        exact arith_take _ _ _ _ h2 hn this
      · have := c e
        have e2 : ¬ p.buy = i := by rw [not_not.mp h1]; exact e
        unfold onBuy at this ⊢
        simp [e2, List.filter_cons] at this ⊢; exact this

/-- The coins of lot `i` the sales name, a sale below 0 counting as none. -/
def posSold (i : ℕ) (ss : List SaleOfLot) : ℚ := ((ss.filter fun s => s.lot = i).map fun s => max s.qty 0).sum

theorem posSold_nonneg (i : ℕ) (ss : List SaleOfLot) : 0 ≤ posSold i ss :=
  List.sum_nonneg (fun a ha => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; exact le_max_right _ _)

theorem soldOf_le_posSold (i : ℕ) (ss : List SaleOfLot) : soldOf i ss ≤ posSold i ss := by
  induction ss with
  | nil => simp [soldOf, posSold]
  | cons s ss ih =>
    unfold soldOf posSold at *
    by_cases e : s.lot = i <;> simp [e, List.filter_cons] at ih ⊢
    · linarith [le_max_left s.qty 0]
    · exact ih

theorem arith_fold (x y q a c : ℚ) (h1 : x ≤ max (y - c) 0) (h2 : y ≤ max (q - a) 0) (hc : 0 ≤ c) :
    x ≤ max (q - (a + c)) 0 := by
  rcases le_total 0 (q - a) with h | h
  · rw [max_eq_left h] at h2; exact h1.trans (max_le_max (by linarith) le_rfl)
  · rw [max_eq_right h] at h2
    exact h1.trans (by rw [max_eq_right (by linarith : y - c ≤ 0)]; exact le_max_right _ _)

theorem washSales_Q (i : ℕ) (ss : List SaleOfLot) (st : W2) (h : ∀ p ∈ st.parts, Q p) :
    (∀ p ∈ (ss.foldl washSale st).parts, Q p) ∧
      onBuy i (ss.foldl washSale st).parts ≤ max (onBuy i st.parts - posSold i ss) 0 := by
  induction ss generalizing st with
  | nil => exact ⟨h, by simp [posSold, onBuy_nonneg i _ h]⟩
  | cons s ss ih =>
    obtain ⟨r1, r2, r3⟩ := release_Q s.lot i s.qty st.parts h
    obtain ⟨i1, i2⟩ := ih (washSale st s) r1
    refine ⟨i1, ?_⟩
    simp only [List.foldl_cons]
    have hp : (washSale st s).parts = (release s.lot s.qty st.parts).1 := rfl
    rw [hp] at i2
    by_cases e : s.lot = i
    · have : posSold i (s :: ss) = max s.qty 0 + posSold i ss := by simp [posSold, e, List.filter_cons]
      rw [this]; exact arith_fold _ _ _ _ _ i2 (r2 e) (posSold_nonneg i ss)
    · have : posSold i (s :: ss) = posSold i ss := by simp [posSold, e, List.filter_cons]
      rw [this, ← r3 e]; exact i2

theorem freeOf_init (i : ℕ) (bs : List Buy) : freeOf i (bs.map fun b => (b, b.qty)) = boughtOf i bs := by
  induction bs with
  | nil => simp [freeOf, boughtOf]
  | cons b bs ih =>
    unfold freeOf boughtOf at *
    by_cases e : b.id = i <;> simp [e, List.filter_cons] at ih ⊢ <;> rw [ih]

/-- **ES-8b** Art. 33.5.e, `esWash`: when the later sales of purchase `i` name at least the coins bought (the purchases
with id `i`, their coins not below 0), no part of any loss put off on those coins still waits: all of it has been
counted. -/
theorem wash_release_all (losses : List Loss) (buys : List Buy) (sales : List SaleOfLot) (i : ℕ)
    (hq : ∀ b ∈ buys, b.id = i → 0 ≤ b.qty) (hs : boughtOf i buys ≤ soldOf i sales) :
    ∀ p ∈ (wash losses buys sales).parts, p.buy = i → p.left = 0 := by
  intro p hp hb
  have hperm := List.mergeSort_perm buys (fun a b => decide (a.date ≤ b.date))
  set st0 : W1 := ⟨(buys.mergeSort fun a b => decide (a.date ≤ b.date)).map fun b => (b, b.qty), fun _ => 0, []⟩
  have j0 : J buys st0 := by
    refine ⟨fun k => ?_, fun x hx => ?_, by simp [st0]⟩
    · simp only [st0, freeOf_init]
      have : boughtOf k (buys.mergeSort fun a b => decide (a.date ≤ b.date)) = boughtOf k buys :=
        ((hperm.filter _).map _).sum_eq
      rw [this]; simp [onBuy]
    · simp only [st0, List.mem_map] at hx; obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨hperm.mem_iff.mp hb, Or.inl rfl⟩
  set w1 := (losses.mergeSort fun a b => decide (a.date ≤ b.date)).foldl washLoss st0
  obtain ⟨j1, j2, j3⟩ := washLosses_J buys _ st0 j0
  have q0 : ∀ p ∈ (⟨w1.parts, w1.deferred, [], []⟩ : W2).parts, Q p :=
    fun p hp => ⟨(j3 p hp).le, fun h => absurd h (not_le.mpr (j3 p hp))⟩
  set sorted := sales.mergeSort fun a b => decide (a.date ≤ b.date)
  obtain ⟨k1, k2⟩ := washSales_Q i sorted ⟨w1.parts, w1.deferred, [], []⟩ q0
  have hw : (wash losses buys sales).parts = (sorted.foldl washSale ⟨w1.parts, w1.deferred, [], []⟩).parts := rfl
  rw [hw] at hp
  have hfree : 0 ≤ freeOf i w1.free := by
    unfold freeOf
    refine List.sum_nonneg (fun a ha => ?_)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hx, e⟩ := List.mem_filter.mp hx
    obtain ⟨b1, b2⟩ := j2 x hx
    have := hq x.1 b1 (by simpa using e)
    rcases b2 with b2 | b2
    · rw [b2]; exact this
    · exact b2
  have hpos : posSold i sorted = posSold i sales := ((List.mergeSort_perm _ _).filter _ |>.map _).sum_eq
  have hsold := soldOf_le_posSold i sales
  have h0 : onBuy i (sorted.foldl washSale ⟨w1.parts, w1.deferred, [], []⟩).parts ≤ 0 := by
    have := j1 i
    refine k2.trans (le_of_eq (max_eq_right ?_))
    simp only at this ⊢; linarith
  have hle : p.qLeft ≤ onBuy i (sorted.foldl washSale ⟨w1.parts, w1.deferred, [], []⟩).parts := by
    unfold onBuy
    exact List.single_le_sum (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; exact (k1 x (List.mem_filter.mp hx).1).1) _
      (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hb⟩, rfl⟩)
  exact (k1 p hp).2 (hle.trans h0)

/-- **ES-8** Art. 33.5.e after wraps: a purchase `i` bought again after a loss, then moved, wrapped any number of times
at any rates (`toQty`) and sold, coin by coin as the ledger runs it; once none of its coins is held in any pool, the
sales passed to `esWash` (`originQty ?? qty`, in the purchase's own coins) count all of every loss put off on it,
whatever the rates. -/
theorem wrap_release {W : ℕ → List OLot} {C : Finset ℕ} {ss : List SaleOfLot} {B : ℕ → ℚ} (h : OReach W C ss B)
    (losses : List Loss) (buys : List Buy) (i : ℕ) (hq : ∀ b ∈ buys, b.id = i → 0 ≤ b.qty)
    (hB : boughtOf i buys = B i) (hgone : ∀ a ∈ C, ∀ x ∈ W a, x.1.id ≠ i) :
    ∀ p ∈ (wash losses buys ss).parts, p.buy = i → p.left = 0 := by
  obtain ⟨-, h2⟩ := origin_conserved h
  have hz : ∀ a ∈ C, originAt i (W a) = 0 := fun a ha => by
    unfold originAt
    rw [List.filter_eq_nil_iff.mpr (fun x hx => by simpa using hgone a ha x hx)]; simp
  have := h2 i
  rw [Finset.sum_eq_zero hz, zero_add] at this
  exact wash_release_all losses buys ss i hq (by rw [hB, this])

/-- **ES-8** The case found in review: a loss of 100 on 1 coin (15 January 2025), 1 coin bought again (1 February), wrapped
into 0.85 of another coin (1 March) and the 0.85 sold (1 April 2026). The sale passed to `esWash` is 1 coin of the
purchase and the loss is counted in full; the slice's own 0.85 coins, as the code passed them before, left 15
waiting. -/
theorem wrap_release_085 :
    let P : List OLot := [(⟨1, 0, 20250201, 1, 2000, (2, 0)⟩, none)]
    let T := owrapIn [] P 1 9 0 20250301 0 0 (some (17 / 20)) 3
    let ls : List Loss := [⟨5, 0, 20250115, 1, 100, none⟩]
    let bs : List Buy := [⟨1, 0, 20250201, 1, none⟩]
    (osale T (17 / 20) 10 0 20260401 4).1.map (fun p => p.1.take) = [17 / 20] ∧
      saleRows 20260401 (osale T (17 / 20) 10 0 20260401 4).1 = [⟨1, 20260401, 1⟩] ∧
      waiting 5 (wash ls bs [⟨1, 20260401, 1⟩]).parts = 0 ∧
      waiting 5 (wash ls bs [⟨1, 20260401, 17 / 20⟩]).parts = 15 := by
  norm_num (config := { decide := true }) [owrapIn, owrapSlices, wrapOrigin, wrapPicks, scaled, osell, sell, held,
    oadd, osale, saleRows, originQty, wash, washLoss, matchLoss, eligible, yearAfter, earlier, washSale, release,
    count, sameList, waiting]

/-- **ES-8** Two wraps one after the other: 2 coins bought again after a loss of 200 on 2 coins, wrapped at 0.85 (1.7
coins) and the 1.7 wrapped at 2 (3.4 coins); a sale of half, 1.7, passes 1 coin of the purchase and counts half the
loss, 100 still waiting. -/
theorem wrap_twice_half :
    let P : List OLot := [(⟨1, 0, 20250201, 2, 4000, (2, 0)⟩, none)]
    let T1 := owrapIn [] P 2 9 0 20250301 0 0 (some (17 / 10)) 3
    let T2 := owrapIn [] T1 (17 / 10) 9 0 20250302 0 0 (some (17 / 5)) 4
    saleRows 20260401 (osale T2 (17 / 10) 10 0 20260401 5).1 = [⟨1, 20260401, 1⟩] ∧
      waiting 5 (wash [⟨5, 0, 20250115, 2, 200, none⟩] [⟨1, 0, 20250201, 2, none⟩] [⟨1, 20260401, 1⟩]).parts = 100 := by
  norm_num (config := { decide := true }) [owrapIn, owrapSlices, wrapOrigin, wrapPicks, scaled, osell, sell, held,
    oadd, osale, saleRows, originQty, wash, washLoss, matchLoss, eligible, yearAfter, earlier, washSale, release,
    count, sameList, waiting]

end Kanon.Spain
