import PersistencePays.EntropySemicontinuity
import PersistencePays.TransportEntropy

/-! Weak continuity of the actual free-transport law and lower semicontinuity,
hence measurability, of its conditional Gaussian entropy as a function of time. -/
open MeasureTheory InformationTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def transportProbability (μ : Measure (E×E)) [IsProbabilityMeasure μ] (t : ℝ) :
    ProbabilityMeasure (E×E) := ⟨transportJoint μ t, inferInstance⟩

theorem continuous_transportProbability (μ : Measure (E×E)) [IsProbabilityMeasure μ] :
    Continuous (transportProbability μ) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have he (t : ℝ) :
      (∫ z, f z ∂(transportProbability μ t : Measure (E×E))) =
        ∫ z, f (freeTransport t z) ∂μ := by
    exact integral_map (measurable_freeTransport t).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound:=fun _ => ‖f‖)
  · intro t
    exact (f.continuous.measurable.comp (measurable_freeTransport t)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm (freeTransport t z))
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro z
    apply f.continuous.comp
    unfold freeTransport drift
    fun_prop

theorem lowerSemicontinuous_conditionalGaussianEntropy
    (μ : Measure (E×E)) (γ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] :
    LowerSemicontinuous (conditionalGaussianEntropy μ γ) :=
  (conditionalKL_lowerSemicontinuous (E:=E) (⟨γ,inferInstance⟩ : ProbabilityMeasure E)).comp
    (continuous_transportProbability μ)

theorem measurable_conditionalGaussianEntropy
    (μ : Measure (E×E)) (γ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] :
    Measurable (conditionalGaussianEntropy μ γ) :=
  (lowerSemicontinuous_conditionalGaussianEntropy μ γ).measurable

end
end PersistencePays
#print axioms PersistencePays.measurable_conditionalGaussianEntropy
