import PersistencePays.CovarianceMatrix
import PersistencePays.ConditionalEntropy

/-! Finiteness and integrability of the actual conditional velocity laws.
These facts are derived from joint second moments and finite conditional KL. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma conditional_kl_lintegral (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    conditionalGaussianEntropy μ (stdGaussian E) 0 =
      ∫⁻ x,klDiv (μ.condKernel x) (stdGaussian E) ∂μ.fst := by
  have hac : μ ≪ μ.fst.prod (stdGaussian E) := by
    simpa only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
      using (klDiv_ne_top_iff.mp hD).1
  have hh := klDiv_compProd_right_integral_of_ac μ.fst μ.condKernel (Kernel.const E (stdGaussian E))
    (by simpa only [μ.disintegrate μ.condKernel,Measure.compProd_const] using hac)
  simpa only [μ.disintegrate μ.condKernel,Measure.compProd_const,Kernel.const_apply,
    conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero] using hh

lemma conditional_kl_aemeasurable (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    AEMeasurable (fun x => klDiv (μ.condKernel x) (stdGaussian E)) μ.fst := by
  let η := Kernel.const E (stdGaussian E)
  have hac : μ.fst ⊗ₘ μ.condKernel ≪ μ.fst ⊗ₘ η := by
    simpa only [μ.disintegrate μ.condKernel,Measure.compProd_const,η,
      conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
      using (klDiv_ne_top_iff.mp hD).1
  have hm : Measurable (fun x => ∫⁻ v,
      ENNReal.ofReal (klFun ((μ.condKernel.rnDeriv η x v).toReal)) ∂stdGaussian E) := by
    exact (show Measurable (fun z : E×E =>
      ENNReal.ofReal (klFun ((μ.condKernel.rnDeriv η z.1 z.2).toReal))) by fun_prop).lintegral_prod_right
  apply hm.aemeasurable.congr
  filter_upwards [hac.kernel_of_compProd] with x hx
  change μ.condKernel x ≪ stdGaussian E at hx
  rw [klDiv_eq_lintegral_klFun_of_ac hx]
  apply lintegral_congr_ae
  filter_upwards [μ.condKernel.rnDeriv_eq_rnDeriv_measure (η:=η) (a:=x)] with v hv
  rw [hv]
  rfl

lemma conditional_laws_finite_entropy (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    ∀ᵐ x ∂μ.fst,klDiv (μ.condKernel x) (stdGaussian E) ≠ ∞ := by
  have hi : (∫⁻ x,klDiv (μ.condKernel x) (stdGaussian E) ∂μ.fst) ≠ ∞ := by
    rwa [← conditional_kl_lintegral μ hD]
  exact (ae_lt_top' (conditional_kl_aemeasurable μ hD) hi).mono (fun _ hx => hx.ne)

lemma conditional_laws_second_moments (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) : ∀ᵐ x ∂μ.fst,MemLp id 2 (μ.condKernel x) := by
  have hi : Integrable (fun z:E×E => ‖z.2‖^2) μ := hm.snd.norm.integrable_sq
  filter_upwards [hi.condKernel_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr hx

lemma conditional_kl_integral (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    Integrable (fun x => (klDiv (μ.condKernel x) (stdGaussian E)).toReal) μ.fst ∧
    (∫ x,(klDiv (μ.condKernel x) (stdGaussian E)).toReal ∂μ.fst) =
      (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := by
  have hm := conditional_kl_aemeasurable μ hD
  have hi : (∫⁻ x,klDiv (μ.condKernel x) (stdGaussian E) ∂μ.fst) ≠ ∞ := by
    rwa [← conditional_kl_lintegral μ hD]
  refine ⟨integrable_toReal_of_lintegral_ne_top hm hi,?_⟩
  rw [integral_toReal hm (ae_lt_top' hm hi),← conditional_kl_lintegral μ hD]

lemma conditional_mean_square_integral (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    Integrable (fun x => ‖∫ v,v ∂μ.condKernel x‖^2) μ.fst ∧
    (∫ x,‖∫ v,v ∂μ.condKernel x‖^2 ∂μ.fst) = (conditionalMeanSquare μ).toReal := by
  have hmean : StronglyMeasurable (fun x => ∫ v:E,v ∂μ.condKernel x) :=
    stronglyMeasurable_id.integral_kernel
  have hi : Integrable (fun x => ‖∫ v,v ∂μ.condKernel x‖^2) μ.fst := by
    apply ((conditional_kl_integral μ hD).1.const_mul 2).mono'
      (hmean.measurable.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [conditional_laws_second_moments μ hm,conditional_laws_finite_entropy μ hD]
      with x hx hdx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact gaussian_mean_entropy (μ.condKernel x) (hx.integrable (by norm_num)) hdx
  refine ⟨hi,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖∫ v,v ∂μ.condKernel x‖)) hi.aestronglyMeasurable]
  rfl

end PersistencePays
#print axioms PersistencePays.conditional_laws_second_moments
#print axioms PersistencePays.conditional_kl_integral
#print axioms PersistencePays.conditional_mean_square_integral
