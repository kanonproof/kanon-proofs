import Mathlib.Tactic

/-!
# Brazil: one asset sold in parts across years (#42)

Lei 8.981 art. 21 § 3: from the second sale of the same asset on, a sale made by the end of the calendar year after the
first one's adds its gain to the earlier ones for the tax bands. KANON keeps a run of sales per asset, begun by its
first sale (taxed or not), open to the end of the next year (`src/lib/engine/br.ts`, `runOf` and `monthTax`). Proved:

* **A sale joins the run open for it.** A sale in year `y` joins the run its asset began in `y - 1` when there is one,
  else the one begun in `y` (begun by this sale if it is the first). So it never joins a run begun before the year
  before: no run reaches past the end of the year after its first sale.
* **One run at a time.** With sales taken in date order, an asset never has runs begun in two years in a row, so a sale
  never has two runs it could join.
* **Adding gains one sale after another gives the band tax on the total.** The band tax charged on each sale, on top of
  the run's gains before it, adds up to the band tax on all of the run's gains less the tax on those before it, for any
  band schedule. (So the app may add a month's gains of one asset first and tax them once.)
-/

namespace Kanon.BrRuns

variable {α : Type} [DecidableEq α]

/-- The run (by the year it began) a sale of asset `a` in year `y` joins, and the runs begun after it. -/
def runOf (a : α) (y : ℤ) (S : Finset (α × ℤ)) : ℤ × Finset (α × ℤ) :=
  if (a, y - 1) ∈ S then (y - 1, S) else (y, insert (a, y) S)

/-- **#42** A sale joins the run begun the year before, if there is one. -/
theorem joins_open (a : α) (y : ℤ) (S : Finset (α × ℤ)) (h : (a, y - 1) ∈ S) : (runOf a y S).1 = y - 1 := by
  simp [runOf, h]

/-- **#42** A sale joins a run begun this year or the year before, never earlier, and that run is kept. -/
theorem joins_window (a : α) (y : ℤ) (S : Finset (α × ℤ)) :
    ((runOf a y S).1 = y - 1 ∨ (runOf a y S).1 = y) ∧ (a, (runOf a y S).1) ∈ (runOf a y S).2 := by
  unfold runOf; split_ifs with h <;> simp [h]

/-- The runs begun after a list of sales (asset, year), taken in order. -/
def runs : Finset (α × ℤ) → List (α × ℤ) → Finset (α × ℤ)
  | S, [] => S
  | S, (a, y) :: rest => runs (runOf a y S).2 rest

/-- No asset has runs begun in two years in a row. -/
def OneAtATime (S : Finset (α × ℤ)) : Prop := ∀ a y, ¬ ((a, y) ∈ S ∧ (a, y + 1) ∈ S)

/-- **#42** Sales taken in date order, starting from runs that are all no later than the sales and one at a time,
leave runs that are one at a time. -/
theorem one_at_a_time (sales : List (α × ℤ)) (S : Finset (α × ℤ))
    (hsorted : sales.Pairwise (fun p q => p.2 ≤ q.2))
    (hbefore : ∀ p ∈ S, ∀ q ∈ sales, p.2 ≤ q.2) (h : OneAtATime S) : OneAtATime (runs S sales) := by
  induction sales generalizing S with
  | nil => simpa [runs] using h
  | cons s rest ih =>
    obtain ⟨a, y⟩ := s
    have hs := List.pairwise_cons.mp hsorted
    simp only [runs]
    apply ih _ hs.2
    · intro p hp q hq
      unfold runOf at hp; split_ifs at hp with hx
      · exact hbefore p hp q (by simp [hq])
      · rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hs.1 q hq
        · exact hbefore p hp q (by simp [hq])
    · unfold runOf; split_ifs with hx
      · exact h
      · intro b z ⟨h1, h2⟩
        dsimp only at h1 h2
        rcases Finset.mem_insert.mp h1 with e1 | h1 <;> rcases Finset.mem_insert.mp h2 with e2 | h2
        · simp [Prod.ext_iff] at e1 e2; omega
        · -- the new run is (a, y) = (b, z), and (b, z + 1) was already begun: later than this sale
          simp [Prod.ext_iff] at e1
          have := hbefore _ h2 (a, y) (by simp); simp at this; omega
        · -- the new run is (a, y) = (b, z + 1), and (b, z) = (a, y - 1) was already begun: then it was joined
          simp [Prod.ext_iff] at e2
          obtain ⟨rfl, hz⟩ := e2
          exact hx (by have : z = y - 1 := by omega
                       rw [this] at h1; exact Finset.mem_of_mem_insert_of_ne h1 (by simp))
        · exact h b z ⟨h1, h2⟩

/-- **#42** Started with no runs, sales in date order never leave an asset with runs begun in two years in a row. -/
theorem one_at_a_time_from_start (sales : List (α × ℤ)) (hsorted : sales.Pairwise (fun p q => p.2 ≤ q.2)) :
    OneAtATime (runs ∅ sales) :=
  one_at_a_time sales ∅ hsorted (by simp) (by simp [OneAtATime])

/-- The band tax charged sale by sale: each sale's on top of the run's gains `p` before it. -/
def stepTax (band : ℚ → ℚ) (p : ℚ) : List ℚ → ℚ
  | [] => 0
  | g :: gs => (band (p + g) - band p) + stepTax band (p + g) gs

/-- **#42** Charged sale by sale, the band tax adds up to the band tax on all the run's gains less that on the gains
before them, whatever the bands. -/
theorem step_is_total (band : ℚ → ℚ) (p : ℚ) (gs : List ℚ) :
    stepTax band p gs = band (p + gs.sum) - band p := by
  induction gs generalizing p with
  | nil => simp [stepTax]
  | cons g gs ih => simp only [stepTax, ih, List.sum_cons]; ring_nf

end Kanon.BrRuns
