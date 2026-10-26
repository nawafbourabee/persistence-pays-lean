import Mathlib

/-!
Nonnegative integral architecture for the Gaussian bridge inequality (Lemma 3.2).
All integrals are extended nonnegative integrals. No moment or prior square-root
integrability assumption is imposed. The final bridge application is separated
from the analytic inequality so Gaussian factorization can be proved explicitly.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace PersistencePays

variable {S : Type*} [MeasurableSpace S]

theorem lintegral_sqrt_le_sqrt_lintegral (μ : Measure S) [IsProbabilityMeasure μ]
    (f : S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ^ (1 / 2 : ℝ) ∂μ) ≤ (∫⁻ x, f x ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hf.pow_const (1 / 2 : ℝ)).aemeasurable
    (measurable_const : Measurable (fun _ : S => (1 : ℝ≥0∞))).aemeasurable
  simpa only [Pi.mul_apply, mul_one, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one, ENNReal.one_rpow, lintegral_const, measure_univ, mul_one] using h

theorem lintegral_sqrt_mul_le (μ : Measure S) (f g : S → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (f x * g x) ^ (1 / 2 : ℝ) ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hf.pow_const (1 / 2 : ℝ)).aemeasurable
    (hg.pow_const (1 / 2 : ℝ)).aemeasurable
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simpa only [Pi.mul_apply,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one] using h

section Convolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Nonnegative convolution with the convention used in the paper. -/
noncomputable def nonnegativeConvolution (f g : E → ℝ≥0∞) (y : E) : ℝ≥0∞ :=
  ∫⁻ x, f (y - x) * g x

theorem measurable_nonnegativeConvolution (f g : E → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (nonnegativeConvolution f g) := by
  apply Measurable.lintegral_prod_right
  exact (hf.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)

/-- Tonelli and translation invariance give the convolution mass identity even
    when either side is infinite. -/
theorem lintegral_nonnegativeConvolution (f g : E → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ y, nonnegativeConvolution f g y) = (∫⁻ y, f y) * ∫⁻ x, g x := by
  unfold nonnegativeConvolution
  rw [lintegral_lintegral_swap]
  · calc
      (∫⁻ x, ∫⁻ y, f (y - x) * g x) = ∫⁻ x, (∫⁻ y, f y) * g x := by
        apply lintegral_congr
        intro x
        have hfx : Measurable (fun y => f (y - x)) := hf.comp (measurable_id.sub_const x)
        rw [lintegral_mul_const _ hfx,
          (measurePreserving_sub_right (volume : Measure E) x).lintegral_comp hf]
      _ = (∫⁻ y, f y) * ∫⁻ x, g x := lintegral_const_mul _ hg
  · exact ((hf.comp (measurable_fst.sub measurable_snd)).mul
      (hg.comp measurable_snd)).aemeasurable

/-- Jensen's square-root inequality for convolution by a probability density. -/
theorem convolution_sqrt_le (f g : E → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hgmass : ∫⁻ x, g x = 1) (y : E) :
    nonnegativeConvolution (fun x => f x ^ (1 / 2 : ℝ)) g y ≤
      (nonnegativeConvolution f g y) ^ (1 / 2 : ℝ) := by
  let μ : Measure E := volume.withDensity g
  have hm : μ Set.univ = 1 := by
    simp only [μ, withDensity_apply g MeasurableSet.univ, Measure.restrict_univ]
    exact hgmass
  let : IsProbabilityMeasure μ := ⟨hm⟩
  have hfy : Measurable (fun x => f (y - x)) := hf.comp (measurable_const.sub measurable_id)
  have h := lintegral_sqrt_le_sqrt_lintegral μ _ hfy
  rw [lintegral_withDensity_eq_lintegral_mul volume hg (hfy.pow_const _),
    lintegral_withDensity_eq_lintegral_mul volume hg hfy] at h
  simpa only [Pi.mul_apply, mul_comm, nonnegativeConvolution] using h

/-- The analytic conclusion of the bridge argument. Its factorization premise is
    subsequently instantiated by the explicit Gaussian bridge identity; it is not
    a claim that Lemma 3.2 has already been proved for Gaussian densities. -/
theorem square_root_mass_le_of_convolution_factorization
    (k g P Q : E → ℝ≥0∞)
    (hk : Measurable k) (hg : Measurable g) (hP : Measurable P) (hQ : Measurable Q)
    (hgmass : ∫⁻ x, g x = 1) (hPmass : ∫⁻ x, P x = 1) (hQmass : ∫⁻ x, Q x = 1)
    (hbridge : ∀ y, nonnegativeConvolution k g y = P y * Q y) :
    (∫⁻ x, k x ^ (1 / 2 : ℝ)) ≤ 1 := by
  calc
    (∫⁻ x, k x ^ (1 / 2 : ℝ)) =
        ∫⁻ y, nonnegativeConvolution (fun x => k x ^ (1 / 2 : ℝ)) g y := by
      rw [lintegral_nonnegativeConvolution _ _ (hk.pow_const _) hg, hgmass, mul_one]
    _ ≤ ∫⁻ y, (nonnegativeConvolution k g y) ^ (1 / 2 : ℝ) :=
      lintegral_mono (convolution_sqrt_le k g hk hg hgmass)
    _ = ∫⁻ y, (P y * Q y) ^ (1 / 2 : ℝ) := by simp only [hbridge]
    _ ≤ (∫⁻ y, P y) ^ (1 / 2 : ℝ) * (∫⁻ y, Q y) ^ (1 / 2 : ℝ) :=
      lintegral_sqrt_mul_le volume P Q hP hQ
    _ = 1 := by rw [hPmass, hQmass, ENNReal.one_rpow, one_mul]

end Convolution
end PersistencePays

#print axioms PersistencePays.square_root_mass_le_of_convolution_factorization
