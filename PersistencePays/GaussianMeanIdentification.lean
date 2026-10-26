import PersistencePays.GaussianFlightMoments
import PersistencePays.GaussianMeanField
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The smooth posterior formula is the conditional mean of the actual law,
including when the compact latent law is presented through a continuous map. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

lemma posteriorMean_map (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) (ε s:ℝ) (y:E) :
    (∫ z,regressionLatentMean s z ∂flightPosterior (μ.map g) ε s y)=
      gaussianMeanRemainder μ g ε s y := by
  have hψ:Measurable (fun z:E×E => regressionExponent ε s (y,z)) := by
    unfold regressionExponent regressionScore regressionLogWeight latentCenter
    fun_prop
  have hF:=regressionLatentMean_measurable (E:=E) s
  rw [flightPosterior,integral_tilted]
  have hden:(∫ z,Real.exp (regressionExponent ε s (y,z)) ∂μ.map g)=
      ∫ z,Real.exp (regressionExponent ε s (y,g z)) ∂μ :=
    integral_map hg.measurable.aemeasurable hψ.exp.aestronglyMeasurable
  rw [hden]
  rw [integral_map hg.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x:E×E =>
      (Real.exp (regressionExponent ε s (y,x))/(∫ z,Real.exp (regressionExponent ε s (y,g z)) ∂μ))•
        regressionLatentMean s x) _ from ((hψ.exp.div_const _).smul hF).aestronglyMeasurable)]
  unfold gaussianMeanRemainder affinePosteriorMean affinePosteriorWeight
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [regressionExponent,smul_smul,div_eq_inv_mul]

lemma compactLatent_memLp (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) : MemLp id 2 (μ.map g) := by
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hg.measurable.aemeasurable).mpr
    (hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))

/-- The vector field for which the actual flow is constructed is exactly the
conditional mean velocity, almost everywhere under the actual position law. -/
theorem gaussianMeanField_eq_conditionalMean (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ∀ᵐ y ∂(gaussianFlightLaw (μ.map g) ε s).fst,
      (∫ v,v ∂(gaussianFlightLaw (μ.map g) ε s).condKernel y)=gaussianMeanField μ g ε s y := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  filter_upwards [gaussianFlightLaw_conditional_moments (μ.map g) (compactLatent_memLp μ g hg) hε s]
    with y hy
  rw [hy.1,posteriorMean_map μ g hg ε s y]
  rfl

end
end PersistencePays
#print axioms PersistencePays.gaussianMeanField_eq_conditionalMean
