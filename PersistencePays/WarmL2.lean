import PersistencePays.KernelEntropy
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! L2-warm transfer of whole-path events and stationary union bounds. -/

namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {S T Ω : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Ω]

/-- The literal L2 norm of the Radon–Nikodym density in Theorem 1. -/
def warmL2 (ν μ : Measure S) : ℝ≥0∞ :=
  eLpNorm (fun x => (ν.rnDeriv μ x).toReal) 2 μ

theorem warmL2_eq_integral (ν μ : Measure S) [SigmaFinite ν] :
    warmL2 ν μ = (∫⁻ x, ν.rnDeriv μ x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [warmL2, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx
  rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]

/-- Applying an arbitrary path kernel transfers any event probability from a
reference start with the exact L2 warmness factor. No pointwise density cap
or independence along the path is required. -/
theorem warmL2_kernel_event (ν μ : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hac : ν ≪ μ) (K : Kernel S T) [IsMarkovKernel K]
    (A : Set T) (hA : MeasurableSet A) :
    (K ∘ₘ ν) A ≤ warmL2 ν μ * ((K ∘ₘ μ) A) ^ (1 / 2 : ℝ) := by
  rw [warmL2_eq_integral, Measure.bind_apply hA K.aemeasurable,
    Measure.bind_apply hA K.aemeasurable,
    ← lintegral_rnDeriv_mul hac (K.measurable_coe hA).aemeasurable]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (Measure.measurable_rnDeriv ν μ).aemeasurable (K.measurable_coe hA).aemeasurable
  apply hh.trans
  gcongr with x
  rw [ENNReal.rpow_two]
  calc
    (K x A) ^ 2 = K x A * K x A := pow_two _
    _ ≤ K x A * 1 := mul_le_mul_right prob_le_one _
    _ = _ := mul_one _

/-- A finite union of nonlocal path events is controlled by stationary
marginals alone; no independence among the observed times is used. -/
theorem stationary_path_union_bound (P : Measure Ω) (π : Measure S)
    (X : ℕ → Ω → S) (hX : ∀ j, Measurable (X j))
    (hmarg : ∀ j, P.map (X j) = π) (A : Set S) (hA : MeasurableSet A) (n : ℕ) :
    P {ω | ∃ j < n, X j ω ∈ A} ≤ (n : ℝ≥0∞) * π A := by
  have he : {ω | ∃ j < n, X j ω ∈ A} = ⋃ j ∈ Finset.range n, (X j) ⁻¹' A := by
    ext ω
    simp
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range n, P ((X j) ⁻¹' A) := measure_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range n, π A := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Measure.map_apply (hX j) hA, hmarg j]
    _ = _ := by simp

end
end PersistencePays

#print axioms PersistencePays.warmL2_kernel_event
#print axioms PersistencePays.stationary_path_union_bound
