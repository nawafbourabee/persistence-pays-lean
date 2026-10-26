import PersistencePays.GaussianLikelihood
import PersistencePays.GaussianLatentDefs

/-! The general Gaussian observation posterior, specialized to the exact
isotropic coefficients in Appendix A.2. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def isotropicScale (σ:ℝ) (hσ:σ≠0):E≃L[ℝ]E :=
  (LinearEquiv.smulOfNeZero ℝ E σ hσ).toContinuousLinearEquiv

@[simp] lemma isotropicScale_apply (σ:ℝ) (hσ:σ≠0) (x:E) : isotropicScale σ hσ x=σ•x := rfl
@[simp] lemma isotropicScale_symm_apply (σ:ℝ) (hσ:σ≠0) (x:E) :
    (isotropicScale σ hσ).symm x=σ⁻¹•x := rfl

lemma observationNoise_pos {ε:ℝ} (hε:0<ε) (s:ℝ) : 0<observationNoise ε s := by
  dsimp [observationNoise]
  positivity

lemma regressionExponent_eq_gaussian {ε:ℝ} (hε:0<ε) (s:ℝ) (q:E×(E×E)) :
    gaussianLikelihoodExponent (isotropicScale (observationNoise ε s)
      (observationNoise_pos hε s).ne') (latentCenter s) q=regressionExponent ε s q := by
  have ha:0<Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have has:(Real.sqrt (1+s^2))^2=1+s^2 := Real.sq_sqrt (by positivity)
  dsimp [gaussianLikelihoodExponent,regressionExponent,regressionScore,regressionLogWeight]
  simp only [real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  dsimp [observationNoise]
  field_simp [hε.ne',ha.ne',show 1+s^2≠0 by positivity]
  ring_nf
  rw [has]
  ring

/-- Actual position/latent law after Gaussian observation in free transport. -/
def flightObservation (μ:Measure (E×E)) (ε s:ℝ):Measure (E×(E×E)) :=
  (μ.prod (stdGaussian E)).map (fun q:(E×E)×E =>
    (observationNoise ε s•q.2+latentCenter s q.1,q.1))

instance flightObservation_finite (μ:Measure (E×E)) [IsFiniteMeasure μ] (ε s:ℝ) :
    IsFiniteMeasure (flightObservation μ ε s) := by unfold flightObservation; infer_instance
instance flightObservation_probability (μ:Measure (E×E)) [IsProbabilityMeasure μ] (ε s:ℝ) :
    IsProbabilityMeasure (flightObservation μ ε s) := by
  unfold flightObservation
  exact Measure.isProbabilityMeasure_map (by unfold latentCenter; fun_prop)

theorem flightObservation_posterior (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ∀ᵐ y ∂(flightObservation μ ε s).fst,
      (flightObservation μ ε s).condKernel y=μ.tilted (fun z => regressionExponent ε s (y,z)) := by
  have hh := (gaussian_observation_posterior μ
    (isotropicScale (observationNoise ε s) (observationNoise_pos hε s).ne')
    (show Measurable (latentCenter (E:=E) s) by unfold latentCenter; fun_prop)).2
  have he : gaussianObservationJoint μ
      (isotropicScale (observationNoise ε s) (observationNoise_pos hε s).ne') (latentCenter s)=
      flightObservation μ ε s := rfl
  change ∀ᵐ y ∂(flightObservation μ ε s).fst,
    (flightObservation μ ε s).condKernel y=μ.tilted (fun z =>
      gaussianLikelihoodExponent (isotropicScale (observationNoise ε s)
        (observationNoise_pos hε s).ne') (latentCenter s) (y,z)) at hh
  filter_upwards [hh] with y hy
  rw [hy]
  congr 1
  funext z
  exact regressionExponent_eq_gaussian hε s (y,z)

end
end PersistencePays
#print axioms PersistencePays.flightObservation_posterior
