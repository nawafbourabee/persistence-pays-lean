import PersistencePays.EpochAcceptance

/-!
# Exact rejection probabilities for a fixed noise block

The threshold has the actual rate-one exponential law. No rejection
probability is assumed as a hypothesis. The result is conditional on a fixed
noise block; averaging over independent Gaussian noise is a separate step.
-/

namespace PersistencePays.EpochAcceptance

open MeasureTheory ProbabilityTheory Set

variable {α : Type*}

/-- Maximum accumulated work over the nonempty prefixes of an epoch. -/
noncomputable def peakWork (accept : ℕ → α → α) (defect : ℕ → α → ℝ)
    (z : α) (n : ℕ) (hn : 0 < n) : ℝ :=
  (Finset.range n).sup' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
    (fun k => accumulatedWork accept defect z (k + 1))

theorem allAccepted_iff_peakWork
    (accept reject : ℕ → α → α) (defect : ℕ → α → ℝ)
    (z : α) (ell : ℝ) (n : ℕ) (hn : 0 < n) :
    allAccepted accept reject defect z ell n ↔ peakWork accept defect z n hn < ell := by
  rw [allAccepted_iff_partialWork, peakWork, Finset.sup'_lt_iff]
  simp only [Finset.mem_range]

/-- The exact one-dimensional integral underlying Proposition 5.1. -/
theorem exponential_rejection_probability (s : ℝ) :
    (expMeasure 1).real (Iic s) = 1 - Real.exp (-max s 0) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  rw [← cdf_eq_real, cdf_expMeasure_eq (by norm_num)]
  by_cases hs : 0 ≤ s
  · simp [hs]
  · have hs' : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    simp [hs, max_eq_right hs']

/-- Proposition 5.1's exact probability conditional on the entire fixed
noise block: probability of any rejection is 1-exp(-positive peak work). -/
theorem rejection_probability_fixed_noise
    (accept reject : ℕ → α → α) (defect : ℕ → α → ℝ)
    (z : α) (n : ℕ) (hn : 0 < n) :
    (expMeasure 1).real {ell | ¬ allAccepted accept reject defect z ell n} =
      1 - Real.exp (-max (peakWork accept defect z n hn) 0) := by
  have hevent : {ell | ¬ allAccepted accept reject defect z ell n} =
      Iic (peakWork accept defect z n hn) := by
    ext ell
    simp only [mem_ofPred_eq, mem_Iic, allAccepted_iff_peakWork
      accept reject defect z ell n hn, not_lt]
  rw [hevent, exponential_rejection_probability]

/-- Integrating an independent exponential threshold against a measurable
random work maximum gives the exact rejection probability. -/
theorem exponential_rejection_probability_product
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Ω → ℝ) (hs : Measurable s) :
    (μ.prod (expMeasure 1)).real {p : Ω × ℝ | p.2 ≤ s p.1} =
      ∫ ω, 1 - Real.exp (-max (s ω) 0) ∂μ := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hevent : MeasurableSet {p : Ω × ℝ | p.2 ≤ s p.1} :=
    measurableSet_le measurable_snd (hs.comp measurable_fst)
  rw [Measure.real, Measure.prod_apply hevent,
    ← integral_toReal (measurable_measure_prodMk_left hevent).aemeasurable
      (Filter.Eventually.of_forall (fun _ => measure_lt_top _ _))]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact exponential_rejection_probability (s ω)

/-- Proposition 5.1's expectation formula for arbitrary independent noise
blocks. Measurability of the concrete work maximum is the only regularity
requirement. The probability formula itself is proved, not assumed. -/
theorem rejection_probability_independent_noise
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (accept reject : Ω → ℕ → α → α) (defect : Ω → ℕ → α → ℝ)
    (z : Ω → α) (n : ℕ) (hn : 0 < n)
    (hm : Measurable (fun ω => peakWork (accept ω) (defect ω) (z ω) n hn)) :
    (μ.prod (expMeasure 1)).real
        {p : Ω × ℝ | ¬ allAccepted (accept p.1) (reject p.1)
          (defect p.1) (z p.1) p.2 n} =
      ∫ ω, 1 - Real.exp (-max (peakWork (accept ω) (defect ω) (z ω) n hn) 0) ∂μ := by
  have hevent : {p : Ω × ℝ | ¬ allAccepted (accept p.1) (reject p.1)
      (defect p.1) (z p.1) p.2 n} =
      {p : Ω × ℝ | p.2 ≤ peakWork (accept p.1) (defect p.1) (z p.1) n hn} := by
    ext p
    simp only [mem_ofPred_eq, allAccepted_iff_peakWork
      (accept p.1) (reject p.1) (defect p.1) (z p.1) p.2 n hn, not_lt]
  rw [hevent]
  exact exponential_rejection_probability_product μ _ hm

end PersistencePays.EpochAcceptance
