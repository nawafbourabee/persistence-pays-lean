import PersistencePays.Pinsker
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! The Gaussian variational estimate underlying Lemma 4.1(S1). -/
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_linear_mgf (L : StrongDual ℝ E) :
    HasSubgaussianMGF L (‖L‖₊ ^ 2) (stdGaussian E) := by
  have hm : (stdGaussian E).map L = gaussianReal 0 (‖L‖₊ ^ 2) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    congr 1
    ext
    simp
  constructor
  · intro t
    have hi : Integrable (fun x : ℝ => exp (t*x)) ((stdGaussian E).map L) := by
      rw [hm]
      exact integrable_exp_mul_gaussianReal t
    exact (integrable_map_measure (by fun_prop) L.continuous.measurable.aemeasurable).mp hi
  · intro t
    rw [mgf_gaussianReal hm]
    simp

/-- Relative entropy controls the squared mean of a vector under the standard
Gaussian reference. This is the exact constant in Lemma 4.1(S1). -/
theorem gaussian_mean_entropy (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun v : E => v) μ) (hD : klDiv μ (stdGaussian E) ≠ ∞) :
    ‖∫ v, v ∂μ‖ ^ 2 ≤ 2 * (klDiv μ (stdGaussian E)).toReal := by
  let a : E := ∫ v, v ∂μ
  let L : StrongDual ℝ E := innerSL ℝ a
  have hL : Integrable L μ := L.integrable_comp hμ
  have hh := subgaussian_expectation_entropy μ (stdGaussian E) hD hL
    (stdGaussian_linear_mgf L) 1
  have hmean : (∫ v, L v ∂μ) = ‖a‖ ^ 2 := by
    rw [L.integral_comp_comm hμ]
    exact real_inner_self_eq_norm_sq a
  have hnorm : ((‖L‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖a‖ ^ 2 := by
    simp [L, innerSL_apply_norm]
  rw [hmean, hnorm] at hh
  norm_num at hh
  nlinarith

/-- Extended-valued version also covering infinite KL. -/
theorem gaussian_mean_entropy_ennreal (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun v : E => v) μ) :
    ENNReal.ofReal (‖∫ v, v ∂μ‖ ^ 2) ≤ 2 * klDiv μ (stdGaussian E) := by
  by_cases hD : klDiv μ (stdGaussian E) = ∞
  · simp [hD]
  have hh := ENNReal.ofReal_le_ofReal (gaussian_mean_entropy μ hμ hD)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hD] using hh

end
end PersistencePays
#print axioms PersistencePays.gaussian_mean_entropy
