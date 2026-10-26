import PersistencePays.Corrector
import PersistencePays.ConditionalEntropy

/-! Conditional-mean representation and the sharp Cauchy–Schwarz part of S3. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conditionalMeanVelocity (μ : Measure (E × E)) [IsProbabilityMeasure μ] (x : E) : E :=
  ∫ v, v ∂μ.condKernel x

theorem measurable_conditionalMeanVelocity (μ : Measure (E × E)) [IsProbabilityMeasure μ] :
    Measurable (conditionalMeanVelocity μ) :=
  (stronglyMeasurable_id.integral_kernel (κ := μ.condKernel)).measurable

theorem conditionalMeanVelocity_memLp (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hV : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    MemLp (conditionalMeanVelocity μ) 2 μ.fst := by
  have hb := conditional_mean_entropy μ (hμ.snd.integrable (by norm_num))
  have hJ : conditionalMeanSquare μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hV) hb
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_conditionalMeanVelocity μ).aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_conditionalMeanVelocity μ).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp
  exact hJ

theorem transportCorrector_conditional (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume) :
    transportCorrector μ ξ =
      ∫ x, ⟪conditionalMeanVelocity μ x,x-positionBrenierMap μ ξ x⟫ ∂μ.fst := by
  unfold transportCorrector
  rw [← Measure.integral_condKernel (transportCorrector_integrable μ ξ hμ hξ hac)]
  apply integral_congr_ae
  filter_upwards [(hμ.snd.integrable (by norm_num)).condKernel_ae] with x hx
  change (∫ v : E, ⟪v,x-positionBrenierMap μ ξ x⟫ ∂μ.condKernel x) = _
  have hi : Integrable (fun v : E => v) (μ.condKernel x) := hx
  calc
    _ = ∫ v : E, ⟪x-positionBrenierMap μ ξ x,v⟫ ∂μ.condKernel x :=
      integral_congr_ae (Filter.Eventually.of_forall (fun v => real_inner_comm _ _))
    _ = ⟪x-positionBrenierMap μ ξ x,conditionalMeanVelocity μ x⟫ := integral_inner hi _
    _ = _ := real_inner_comm _ _

theorem transportCorrector_conditional_bound (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume)
    (hV : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞) :
    |transportCorrector μ ξ| ≤ Real.sqrt (conditionalMeanSquare μ).toReal *
      Real.sqrt ((QuadraticTransport.cost ⟨μ.fst,inferInstance⟩ ξ).toReal) := by
  have hf : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hT := QuadraticTransport.brenierMap_memLp ⟨μ.fst,inferInstance⟩ ξ hf hξ hac
  have hmean := conditionalMeanVelocity_memLp μ hμ hV
  have hJ : (∫ x, ‖conditionalMeanVelocity μ x‖^2 ∂μ.fst) =
      (conditionalMeanSquare μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      hmean.integrable_norm_pow'.aestronglyMeasurable
  have hcost := QuadraticTransport.brenierMap_displacement_cost ⟨μ.fst,inferInstance⟩ ξ hf hξ hac
  change (∫ x, ‖x-positionBrenierMap μ ξ x‖^2 ∂μ.fst) = _ at hcost
  rw [transportCorrector_conditional μ ξ hμ hξ hac, ← hJ, ← hcost]
  exact abs_integral_inner_le_sqrt hmean (hf.sub hT)

end PersistencePays
#print axioms PersistencePays.transportCorrector_conditional_bound
