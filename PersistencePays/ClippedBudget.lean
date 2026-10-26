import PersistencePays.EpochRejectionBound

/-! A clipped expectation bound with two explicit exceptional events. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped ENNReal

theorem clipped_budget_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B M : Set Ω)
    (hB : MeasurableSet B) (hM : MeasurableSet M)
    (f g : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hgood : ∀ x ∈ B, x ∉ M → f x ≤ c + g x)
    (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂μ) ≤
      μ Bᶜ + μ M + ENNReal.ofReal c + ∫⁻ x in B, ENNReal.ofReal (g x) ∂μ := by
  calc
    _ ≤ ∫⁻ x, Bᶜ.indicator (fun _ => (1:ℝ≥0∞)) x +
        M.indicator (fun _ => (1:ℝ≥0∞)) x + ENNReal.ofReal c +
        B.indicator (fun x => ENNReal.ofReal (g x)) x ∂μ := by
      apply lintegral_mono
      intro x
      have hone : ENNReal.ofReal (min 1 (f x)) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (min_le_left 1 (f x))
      by_cases hb : x ∈ B
      · by_cases hm : x ∈ M
        · simp only [indicator_of_mem hb, indicator_of_mem hm,
            indicator_of_notMem (show x ∉ Bᶜ from not_not.mpr hb), zero_add]
          exact hone.trans ((le_add_of_nonneg_right (by positivity)).trans
            (le_add_of_nonneg_right (by positivity)))
        · simp only [indicator_of_mem hb, indicator_of_notMem hm,
            indicator_of_notMem (show x ∉ Bᶜ from not_not.mpr hb), zero_add]
          rw [← ENNReal.ofReal_add hc (hg0 x)]
          exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (hgood x hb hm))
      · simp only [indicator_of_mem (show x ∈ Bᶜ from hb), indicator_of_notMem hb, add_zero]
        exact hone.trans ((le_add_of_nonneg_right (by positivity)).trans
          (le_add_of_nonneg_right (by positivity)))
    _ = _ := by
      have h₁ : Measurable (fun x => Bᶜ.indicator (fun _ => (1:ℝ≥0∞)) x) :=
        measurable_const.indicator hB.compl
      have h₂ : Measurable (fun x => Bᶜ.indicator (fun _ => (1:ℝ≥0∞)) x +
          M.indicator (fun _ => (1:ℝ≥0∞)) x) := h₁.add (measurable_const.indicator hM)
      have h₃ : Measurable (fun x => Bᶜ.indicator (fun _ => (1:ℝ≥0∞)) x +
          M.indicator (fun _ => (1:ℝ≥0∞)) x + ENNReal.ofReal c) := h₂.add measurable_const
      rw [lintegral_add_left h₃, lintegral_add_left h₂, lintegral_add_left h₁,
        lintegral_indicator_const hB.compl, lintegral_indicator_const hM,
        lintegral_const, measure_univ, mul_one, one_mul, one_mul,
        lintegral_indicator hB]

end PersistencePays
#print axioms PersistencePays.clipped_budget_lintegral
