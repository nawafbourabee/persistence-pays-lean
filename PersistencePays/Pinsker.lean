import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
Pinsker's inequality, proved from actual relative entropy and Hoeffding's lemma.
The intermediate variational inequality does not assume a density bounded away
from zero, and the final event inequality assumes only finite relative entropy.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

namespace PersistencePays

/-- The exponential/relative-entropy Young inequality, including zero density. -/
theorem mul_le_klFun_add_exp {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x * y ≤ klFun x + exp y - 1 := by
  rcases eq_or_lt_of_le hx with h0 | hx
  · subst x
    simp only [klFun, zero_mul, zero_add]
    linarith [exp_pos y]
  · have h := mul_le_mul_of_nonneg_left (add_one_le_exp (y - log x)) hx.le
    rw [exp_sub, exp_log hx] at h
    have he : x * (exp y / x) = exp y := by field_simp
    rw [he] at h
    unfold klFun
    nlinarith

variable {S : Type*} [MeasurableSpace S]

/-- One side of the entropy variational principle. The exponential test need only
    have integral at most one under the reference measure. -/
theorem integral_le_klDiv_of_exp_integral_le_one
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) (F : S → ℝ)
    (hF : Integrable F μ) (heF : Integrable (fun x => exp (F x)) ν)
    (he : ∫ x, exp (F x) ∂ν ≤ 1) :
    ∫ x, F x ∂μ ≤ (klDiv μ ν).toReal := by
  obtain ⟨hac, hlog⟩ := klDiv_ne_top_iff.mp hD
  have hkl : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν :=
    (integrable_klFun_rnDeriv_iff hac).mpr hlog
  have hmul : Integrable (fun x => (μ.rnDeriv ν x).toReal * F x) ν :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hF
  have hsum : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal + exp (F x)) ν :=
    hkl.add heF
  have hi := integral_mono hmul ((hkl.add heF).sub (integrable_const 1))
    (fun x => mul_le_klFun_add_exp ENNReal.toReal_nonneg (F x))
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  rw [integral_toReal_rnDeriv_mul hac,
    integral_sub hsum (integrable_const 1), integral_add hkl heF] at hi
  rw [← toReal_klDiv_eq_integral_klFun hac] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

/-- Relative entropy controls the expectation of a reference-sub-Gaussian test.
    This form is useful independently of Pinsker's inequality. -/
theorem subgaussian_expectation_entropy
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) {f : S → ℝ} {c : ℝ≥0}
    (hf : Integrable f μ) (hsg : HasSubgaussianMGF f c ν) (t : ℝ) :
    t * (∫ x, f x ∂μ) - c * t ^ 2 / 2 ≤ (klDiv μ ν).toReal := by
  let a : ℝ := c * t ^ 2 / 2
  have hF : Integrable (fun x => t * f x - a) μ :=
    (hf.const_mul t).sub (integrable_const a)
  have heF : Integrable (fun x => exp (t * f x - a)) ν := by
    simp only [exp_sub]
    exact (hsg.integrable_exp_mul t).div_const (exp a)
  have he : (∫ x, exp (t * f x - a) ∂ν) ≤ 1 := by
    simp only [exp_sub, integral_div]
    apply (div_le_one (exp_pos a)).mpr
    exact hsg.mgf_le t
  have h := integral_le_klDiv_of_exp_integral_le_one μ ν hD _ hF heF he
  simpa only [integral_sub (hf.const_mul t) (integrable_const a),
    integral_const_mul, integral_const, probReal_univ,
    smul_eq_mul, one_mul, a] using h

/-- Sharp Pinsker bound for every measurable test with values in `[0,1]`. -/
theorem pinsker_bounded_test_sq
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) (f : S → ℝ) (hm : Measurable f)
    (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    2 * ((∫ x, f x ∂μ) - ∫ x, f x ∂ν) ^ 2 ≤ (klDiv μ ν).toReal := by
  have hfμ : Integrable f μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (Filter.Eventually.of_forall hb)
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := ν) hm.aemeasurable
    (Filter.Eventually.of_forall hb)
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by norm_num
  rw [hc] at hsg
  have hcenter : Integrable (fun x => f x - ∫ y, f y ∂ν) μ :=
    hfμ.sub (integrable_const (∫ x, f x ∂ν))
  have h := subgaussian_expectation_entropy μ ν hD
    hcenter hsg
    (4 * ((∫ x, f x ∂μ) - ∫ x, f x ∂ν))
  simp only [integral_sub hfμ (integrable_const (∫ x, f x ∂ν)),
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  norm_num at h
  nlinarith [h]

/-- Sharp eventwise Pinsker inequality. This uses the conventional probability
    normalization of total variation, the supremum of event discrepancies. -/
theorem pinsker_event_sq
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A) :
    2 * (μ.real A - ν.real A) ^ 2 ≤ (klDiv μ ν).toReal := by
  have hb : ∀ x, A.indicator (fun _ : S => (1 : ℝ)) x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have h := pinsker_bounded_test_sq μ ν hD _ (measurable_const.indicator hA) hb
  simpa only [integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one] using h

/-- Eventwise Pinsker in its usual square-root form. -/
theorem pinsker_event
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ sqrt ((klDiv μ ν).toReal / 2) := by
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_abs, sq_sqrt (by positivity)]
  have h := pinsker_event_sq μ ν hD A hA
  linarith

/-- Extended-valued eventwise Pinsker, also covering infinite relative entropy. -/
theorem pinsker_event_sq_ennreal
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set S) (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν := by
  by_cases hD : klDiv μ ν = ∞
  · simp [hD]
  · exact (ENNReal.ofReal_le_ofReal (pinsker_event_sq μ ν hD A hA)).trans_eq
      (ENNReal.ofReal_toReal hD)

/-- Probability-normalized total variation: the supremum of discrepancies of
    measurable events. The extended codomain permits a direct supremum. -/
noncomputable def probabilityTV (μ ν : Measure S) : ℝ≥0∞ :=
  ⨆ (A : Set S) (_ : MeasurableSet A), ENNReal.ofReal |μ.real A - ν.real A|

/-- Pinsker's inequality for total variation with the sharp factor `1/2`. -/
theorem pinsker_probabilityTV
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) :
    probabilityTV μ ν ≤ ENNReal.ofReal (sqrt ((klDiv μ ν).toReal / 2)) := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  exact ENNReal.ofReal_le_ofReal (pinsker_event μ ν hD A hA)

end PersistencePays

#print axioms PersistencePays.integral_le_klDiv_of_exp_integral_le_one
#print axioms PersistencePays.subgaussian_expectation_entropy
#print axioms PersistencePays.pinsker_event
#print axioms PersistencePays.pinsker_probabilityTV
