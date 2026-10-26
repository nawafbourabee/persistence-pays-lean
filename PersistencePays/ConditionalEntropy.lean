import PersistencePays.GaussianMeanEntropy
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import PersistencePays.TransportReferences
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Disintegration.Integral

/-! Actual conditional relative entropy and the conditional Gaussian mean bound. -/
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace.CountableOrCountablyGenerated S T]

/-- Fiberwise relative entropy integrates to the relative entropy of the
composition products when their first marginal is the same. -/
theorem klDiv_compProd_right_integral_of_ac (ν : Measure S) [IsProbabilityMeasure ν]
    (κ η : Kernel S T) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ν ⊗ₘ κ ≪ ν ⊗ₘ η) :
    klDiv (ν ⊗ₘ κ) (ν ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hRN := rnDeriv_measure_compProd_right ν κ η
  calc
    _ = ∫⁻ z, ENNReal.ofReal (klFun ((κ.rnDeriv η z.1 z.2).toReal)) ∂(ν ⊗ₘ η) := by
      apply lintegral_congr_ae
      filter_upwards [hRN] with z hz
      rw [hz]
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (klFun ((κ.rnDeriv η x y).toReal)) ∂η x ∂ν := by
      apply Measure.lintegral_compProd
      fun_prop
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hac.kernel_of_compProd] with x hx
      rw [klDiv_eq_lintegral_klFun_of_ac hx]
      apply lintegral_congr_ae
      filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := x)] with y hy
      rw [hy]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Chain-rule decomposition used to define the phase-space entropy functional. -/
theorem klDiv_product_reference_decomposition
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (π γ : Measure E) [IsProbabilityMeasure π] [IsProbabilityMeasure γ] :
    klDiv μ (π.prod γ) = klDiv μ.fst π + klDiv μ (μ.fst.prod γ) := by
  have hh := klDiv_compProd_eq_add μ.fst π μ.condKernel (Kernel.const E γ)
  simpa only [μ.disintegrate μ.condKernel, Measure.compProd_const] using hh

/-- Conditional Gaussian entropy equals velocity entropy plus mutual
information, expressed entirely through actual probability measures. -/
theorem conditional_entropy_mutual_information
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (γ : Measure E) [IsProbabilityMeasure γ] :
    klDiv μ (μ.fst.prod γ) = klDiv μ.snd γ + klDiv μ (μ.fst.prod μ.snd) := by
  letI : IsProbabilityMeasure (μ.map Prod.swap) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have hh := klDiv_product_reference_decomposition (μ.map Prod.swap) γ μ.fst
  simp only [Measure.fst_map_swap] at hh
  have he0 : (μ.fst.prod γ).map Prod.swap = γ.prod μ.fst := Measure.prod_swap
  have he1 : (μ.fst.prod μ.snd).map Prod.swap = μ.snd.prod μ.fst := Measure.prod_swap
  rw [← he0, ← he1] at hh
  have h0 := klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : (E × E) ≃ᵐ (E × E)) μ (μ.fst.prod γ)
  have h1 := klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : (E × E) ≃ᵐ (E × E)) μ (μ.fst.prod μ.snd)
  change klDiv (μ.map Prod.swap) ((μ.fst.prod γ).map Prod.swap) = _ at h0
  change klDiv (μ.map Prod.swap) ((μ.fst.prod μ.snd).map Prod.swap) = _ at h1
  rwa [h0, h1] at hh

/-- Integrated squared norm of the actual conditional mean velocity. -/
def conditionalMeanSquare (μ : Measure (E × E)) [IsProbabilityMeasure μ] : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖∫ v, v ∂μ.condKernel x‖ ^ 2) ∂μ.fst

/-- Lemma 4.1(S1), using actual disintegration and actual conditional KL. -/
theorem conditional_mean_entropy (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : Integrable (Prod.snd : E × E → E) μ) :
    conditionalMeanSquare μ ≤ 2 * conditionalGaussianEntropy μ (stdGaussian E) 0 := by
  by_cases hD : conditionalGaussianEntropy μ (stdGaussian E) 0 = ∞
  · simp [hD]
  have hac : μ ≪ μ.fst.prod (stdGaussian E) := by
    simpa only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero]
      using (klDiv_ne_top_iff.mp hD).1
  have hprod : μ.fst ⊗ₘ Kernel.const E (stdGaussian E) = μ.fst.prod (stdGaussian E) := by
    rw [Measure.compProd_const]
  have hdis : μ.fst ⊗ₘ μ.condKernel = μ := μ.disintegrate μ.condKernel
  have hc : klDiv μ (μ.fst.prod (stdGaussian E)) =
      ∫⁻ x, klDiv (μ.condKernel x) (stdGaussian E) ∂μ.fst := by
    have h := klDiv_compProd_right_integral_of_ac μ.fst μ.condKernel (Kernel.const E (stdGaussian E))
      (by rwa [hdis, hprod])
    simpa only [hdis, hprod, Kernel.const_apply] using h
  unfold conditionalMeanSquare
  calc
    _ ≤ ∫⁻ x, 2 * klDiv (μ.condKernel x) (stdGaussian E) ∂μ.fst := by
      apply lintegral_mono_ae
      filter_upwards [hμ.condKernel_ae] with x hx
      exact gaussian_mean_entropy_ennreal (μ.condKernel x) hx
    _ = 2 * klDiv μ (μ.fst.prod (stdGaussian E)) := by
      rw [lintegral_const_mul' _ _ (by norm_num), hc]
    _ = _ := by simp only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero]

end
end PersistencePays
#print axioms PersistencePays.conditional_mean_entropy

#print axioms PersistencePays.klDiv_product_reference_decomposition

#print axioms PersistencePays.conditional_entropy_mutual_information
