import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Simulator odds: within ±1 point at 95% confidence (#14)

The future simulator (`simulate()` and `odds()` in `src/lib/sim/sim.ts`) builds 20,000 paths and shows, for a goal,
the share of paths that reach it. Each path draws its own blocks of past months, so, with ideal random draws, the
paths are independent and each reaches the goal with the same chance `p` (the model's true odds). Whether a path
reaches the goal is 0 or 1.

Shown here (Hoeffding's inequality, from Mathlib): the chance that the share shown is 1 point (0.01) or more away from
`p` is at most `2·e^(−2·n·0.01²)`, and with the simulator's 20,000 paths that is under 5%. So each chance computed
is within ±1 percentage point of the model's own at 95% confidence: each number on its own (not all of a screen's
numbers at once), and before it is rounded to the whole percent shown (within 1.5 points as shown).

Not covered: the app's draws come from a pseudo-random generator with a fixed seed (the same inputs always give the
same odds), not ideal randomness; and whether the past is a good model of the future (model risk, shown apart).
-/

namespace Kanon.Simulator

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- One side of the bound: the paths' total is `t` or more above `n·p` with chance at most `e^(−2t²/n)`. -/
theorem one_side {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) (hm : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, (X i ω - μ[X i])} ≤ exp (-2 * t ^ 2 / n) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hY : iIndepFun (fun i ω => X i ω - μ[X i]) μ := by
    have := h_indep.comp (fun (i : ℕ) (x : ℝ) => x - μ[X i]) (fun i => measurable_id.sub_const _)
    simpa [Function.comp_def] using this
  have hsub : ∀ i < n, HasSubgaussianMGF (fun ω => X i ω - μ[X i]) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ :=
    fun i _ => hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
  refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hY hsub ht).trans_eq ?_
  congr 1
  have h1 : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : ℝ) := by
    simp only [sub_zero, nnnorm_one]; push_cast; norm_num
  rw [h1]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- **#14** The share of `n` paths reaching the goal is `ε` or more away from the true odds `p` with chance at most
`2·e^(−2·n·ε²)` (Hoeffding). -/
theorem share_close {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) (hm : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hp : ∀ i, μ[X i] = p)
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ Finset.range n, X i ω) / n - p|} ≤ 2 * exp (-2 * n * ε ^ 2) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  -- The other side: the same bound for 1 − X (also independent, also in [0, 1]).
  have hneg : iIndepFun (fun i ω => 1 - X i ω) μ := h_indep.comp (fun _ (x : ℝ) => 1 - x) (fun _ => measurable_const.sub measurable_id)
  have hm' : ∀ i, AEMeasurable (fun ω => 1 - X i ω) μ := fun i => aemeasurable_const.sub (hm i)
  have hb' : ∀ i, ∀ᵐ ω ∂μ, (fun ω => 1 - X i ω) ω ∈ Set.Icc (0 : ℝ) 1 := fun i => by
    filter_upwards [hb i] with ω ⟨h0, h1⟩
    exact ⟨by simp; linarith, by simp; linarith⟩
  have hint : ∀ i, Integrable (X i) μ := fun i => Integrable.of_mem_Icc 0 1 (hm i) (hb i)
  have up := one_side h_indep hm hb n hn (t := n * ε) (by positivity)
  have dn := one_side hneg hm' hb' n hn (t := n * ε) (by positivity)
  have hexp : exp (-2 * (n * ε) ^ 2 / n) = exp (-2 * n * ε ^ 2) := by congr 1; field_simp
  rw [hexp] at up dn
  have hsum : ∀ ω, ∑ i ∈ Finset.range n, (X i ω - μ[X i]) = (∑ i ∈ Finset.range n, X i ω) - n * p := by
    intro ω; simp [Finset.sum_sub_distrib, hp]
  have hsum' : ∀ ω, ∑ i ∈ Finset.range n, ((1 - X i ω) - μ[fun ω => 1 - X i ω]) = n * p - (∑ i ∈ Finset.range n, X i ω) := by
    intro ω
    have : ∀ i, μ[fun ω => 1 - X i ω] = 1 - p := fun i => by
      rw [integral_sub (integrable_const _) (hint i), hp i]; simp
    simp only [this]
    rw [Finset.sum_congr rfl (fun i _ => show (1 - X i ω) - (1 - p) = p - X i ω by ring)]
    simp [Finset.sum_sub_distrib]
  have hsub : {ω | ε ≤ |(∑ i ∈ Finset.range n, X i ω) / n - p|} ⊆
      {ω | n * ε ≤ ∑ i ∈ Finset.range n, (X i ω - μ[X i])} ∪
      {ω | n * ε ≤ ∑ i ∈ Finset.range n, ((1 - X i ω) - μ[fun ω => 1 - X i ω])} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, hsum, hsum']
    have key : (∑ i ∈ Finset.range n, X i ω) / n - p = ((∑ i ∈ Finset.range n, X i ω) - n * p) / n := by
      field_simp
    rw [key, abs_div, abs_of_pos hnr, le_div_iff₀ hnr] at hω
    rcases le_abs'.mp (by linarith [hω] : n * ε ≤ |(∑ i ∈ Finset.range n, X i ω) - n * p|) with h | h
    · right; linarith
    · left; linarith
  calc μ.real {ω | ε ≤ |(∑ i ∈ Finset.range n, X i ω) / n - p|}
      ≤ μ.real ({ω | n * ε ≤ ∑ i ∈ Finset.range n, (X i ω - μ[X i])} ∪
          {ω | n * ε ≤ ∑ i ∈ Finset.range n, ((1 - X i ω) - μ[fun ω => 1 - X i ω])}) := measureReal_mono hsub
    _ ≤ μ.real {ω | n * ε ≤ ∑ i ∈ Finset.range n, (X i ω - μ[X i])} +
          μ.real {ω | n * ε ≤ ∑ i ∈ Finset.range n, ((1 - X i ω) - μ[fun ω => 1 - X i ω])} := measureReal_union_le _ _
    _ ≤ 2 * exp (-2 * n * ε ^ 2) := by linarith

/-- The simulator's 20,000 paths and 1 point: `2·e^(−2·20000·0.01²) = 2·e^(−4)`, under 5%. -/
theorem paths_enough : 2 * exp (-2 * (20000 : ℕ) * (1 / 100 : ℝ) ^ 2) < 0.05 := by
  have h4 : -2 * ((20000 : ℕ) : ℝ) * (1 / 100 : ℝ) ^ 2 = -4 := by norm_num
  rw [h4]
  have he : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
  have h : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
  have : (40 : ℝ) < exp 4 := by rw [h]; nlinarith [pow_lt_pow_left₀ he (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)]
  rw [exp_neg]
  have hp : 0 < exp 4 := exp_pos 4
  rw [mul_inv_lt_iff₀ hp]
  linarith

/-- **#14** With the simulator's 20,000 paths, a chance computed (before rounding) is 1 percentage point or more away
from the model's own with probability under 5%: within ±1 point at 95% confidence, each number on its own. -/
theorem odds_within_one_point {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) (hm : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hp : ∀ i, μ[X i] = p) :
    μ.real {ω | (1 / 100 : ℝ) ≤ |(∑ i ∈ Finset.range 20000, X i ω) / (20000 : ℕ) - p|} < 0.05 :=
  (share_close h_indep hm hb hp 20000 (by norm_num) (by norm_num)).trans_lt paths_enough

end Kanon.Simulator
