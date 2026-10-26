import PersistencePays.GaussianFlightConditional
import PersistencePays.GaussianMixtureMoments
import PersistencePays.TiltedMoments

/-! Literal conditional mean and covariance formulas for the Gaussian-smoothed
free-flight law. Posterior moments are proved finite from the input moments. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def flightPosterior (μ:Measure (E×E)) (ε s:ℝ) (y:E):Measure (E×E) :=
  μ.tilted (fun z => regressionExponent ε s (y,z))

lemma regressionExponent_integrable (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    Integrable (fun z => Real.exp (regressionExponent ε s (y,z))) μ := by
  have hh:=gaussianLikelihoodExponent_integrable μ
    (isotropicScale (observationNoise ε s) (observationNoise_pos hε s).ne')
    (show Measurable (latentCenter (E:=E) s) by unfold latentCenter; fun_prop) y
  simpa only [regressionExponent_eq_gaussian hε] using hh

lemma flightPosterior_probability (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) : IsProbabilityMeasure (flightPosterior μ ε s y) :=
  isProbabilityMeasure_tilted (regressionExponent_integrable μ hε s y)

lemma flightPosterior_memLp (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hm:MemLp id 2 μ) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    MemLp id 2 (flightPosterior μ ε s y) := by
  have hb (z:E×E):regressionExponent ε s (y,z) ≤
      ‖(isotropicScale (observationNoise ε s) (observationNoise_pos hε s).ne').symm y‖^2/2 := by
    rw [← regressionExponent_eq_gaussian hε s (y,z)]
    exact gaussianLikelihoodExponent_bound _ _ y z
  exact memLp_tilted_of_upper μ (regressionExponent_integrable μ hε s y) hb hm

lemma regressionLatentMean_measurable (s:ℝ) : Measurable (regressionLatentMean (E:=E) s) := by
  unfold regressionLatentMean
  fun_prop

lemma flightPosterior_latent_memLp (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hm:MemLp id 2 μ) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    MemLp (regressionLatentMean s) 2 (flightPosterior μ ε s y) := by
  have hh:=flightPosterior_memLp μ hm hε s y
  exact (hh.snd.sub (hh.fst.const_smul s)).const_smul (1+s^2)⁻¹

lemma gaussianMixture_map (ρ:Measure (E×E)) [IsProbabilityMeasure ρ]
    (s:ℝ) (b:E) (τ:ℝ) :
    gaussianMixture (ρ.map (regressionLatentMean s)) b τ=
      (ρ.prod (stdGaussian E)).map (fun q:(E×E)×E => b+regressionLatentMean s q.1+τ•q.2) := by
  have he:(ρ.map (regressionLatentMean s)).prod (stdGaussian E)=
      (ρ.prod (stdGaussian E)).map (Prod.map (regressionLatentMean s) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map ρ (stdGaussian E)
      (regressionLatentMean_measurable s) measurable_id
  rw [gaussianMixture,he,Measure.map_map (by fun_prop) ((regressionLatentMean_measurable s).prodMap measurable_id)]
  rfl

/-- Both moment identities hold for the actual velocity disintegration. -/
theorem gaussianFlightLaw_conditional_moments (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hm:MemLp id 2 μ) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ∀ᵐ y ∂(gaussianFlightLaw μ ε s).fst,
      (∫ v,v ∂(gaussianFlightLaw μ ε s).condKernel y)=
        regressionBeta s•y+∫ z,regressionLatentMean s z ∂flightPosterior μ ε s y ∧
      ∀ u v:E,covarianceBilin ((gaussianFlightLaw μ ε s).condKernel y) u v=
        covarianceBilin ((flightPosterior μ ε s y).map (regressionLatentMean s)) u v+
          (ε^2/(1+s^2))*⟪u,v⟫ := by
  filter_upwards [(gaussianFlightLaw_conditional μ hε s).2] with y hy
  letI := flightPosterior_probability μ hε s y
  have hF:=flightPosterior_latent_memLp μ hm hε s y
  have hν:MemLp id 2 ((flightPosterior μ ε s y).map (regressionLatentMean s)) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (regressionLatentMean_measurable s).aemeasurable).mpr hF
  letI : IsProbabilityMeasure ((flightPosterior μ ε s y).map (regressionLatentMean s)) :=
    Measure.isProbabilityMeasure_map (regressionLatentMean_measurable s).aemeasurable
  have he:(gaussianFlightLaw μ ε s).condKernel y=
      gaussianMixture ((flightPosterior μ ε s y).map (regressionLatentMean s))
        (regressionBeta s•y) (regressionNoise ε s) := by
    rw [gaussianMixture_map]
    exact hy
  rw [he]
  refine ⟨?_,?_⟩
  · rw [gaussianMixture_mean _ hν,integral_map
      (regressionLatentMean_measurable s).aemeasurable
      (show AEStronglyMeasurable (fun x:E => x) _ from measurable_id.aestronglyMeasurable)]
  · intro u v
    rw [gaussianMixture_covariance _ hν]
    dsimp [regressionNoise]
    rw [div_pow,Real.sq_sqrt (by positivity)]

end
end PersistencePays
#print axioms PersistencePays.gaussianFlightLaw_conditional_moments
