import PersistencePays.GaussianMixtureFields

/-! The actual momentum flux equals density times the smooth conditional mean. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

lemma singleFlightDensity_factorization {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    singleFlightDensity ε s y z=singleFlightDensity ε s y (0,0)*
      Real.exp (regressionExponent ε s (y,z)) := by
  have hd:1+s^2≠0 := by positivity
  have he:singleFlightLog ε s y z=singleFlightLog ε s y (0,0)+regressionExponent ε s (y,z) := by
    unfold singleFlightLog flightResidual regressionExponent regressionScore regressionLogWeight
    simp only [latentCenter,smul_zero,add_zero,sub_zero,norm_sub_sq_real,real_inner_smul_left]
    rw [real_inner_comm (z.1+s•z.2) y]
    field_simp
    <;> ring
  unfold singleFlightDensity
  rw [he,Real.exp_add]
  ring

lemma regressionExponent_latent_continuous (g:Z→E×E) (hg:Continuous g) (ε s:ℝ) (y:E) :
    Continuous (fun z=>regressionExponent ε s (y,g z)) := by
  unfold regressionExponent regressionScore regressionLogWeight latentCenter
  fun_prop

lemma gaussianFlightDensity_factorization (μ:Measure Z) (g:Z→E×E)
    {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) :
    gaussianFlightDensity μ g ε s y=singleFlightDensity ε s y (0,0)*
      ∫z,Real.exp (regressionExponent ε s (y,g z)) ∂μ := by
  unfold gaussianFlightDensity
  have he:(fun z=>singleFlightDensity ε s y (g z))=(fun z=>singleFlightDensity ε s y (0,0)*
      Real.exp (regressionExponent ε s (y,g z))) := by
    funext z; exact singleFlightDensity_factorization hε s y (g z)
  rw [he,integral_const_mul]

/-- This is a pointwise identity, not merely an almost-everywhere choice of mean. -/
theorem gaussianFlightFlux_eq_density_mean (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    gaussianFlightFlux μ g ε s y=gaussianFlightDensity μ g ε s y •
      gaussianMeanField μ g ε s y := by
  let w:Z→ℝ:=fun z=>Real.exp (regressionExponent ε s (y,g z))
  let F:Z→E:=fun z=>regressionLatentMean s (g z)
  have hw:Continuous w := Real.continuous_exp.comp (regressionExponent_latent_continuous g hg ε s y)
  have hF:Continuous F := by unfold F regressionLatentMean; fun_prop
  have hi:Integrable w μ := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiF:Integrable (fun z=>w z•F z) μ :=
    (hw.smul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp:0<∫z,w z ∂μ := integral_exp_pos hi
  have hJ:gaussianFlightFlux μ g ε s y=
      singleFlightDensity ε s y (0,0) •
        ((∫z,w z ∂μ)•(regressionBeta s•y)+∫z,w z•F z ∂μ) := by
    unfold gaussianFlightFlux singleFlightFlux
    have he:(fun z=>singleFlightDensity ε s y (g z)•singleFlightVelocity s y (g z))=
        (fun z=>singleFlightDensity ε s y (0,0)•(w z•(regressionBeta s•y+F z))) := by
      funext z
      rw [singleFlightDensity_factorization hε.ne',singleFlightVelocity_eq,mul_smul]
    rw [he,integral_smul]
    congr 1
    simp_rw [smul_add]
    rw [integral_add (hi.smul_const _) hiF,integral_smul_const]
  rw [hJ,gaussianFlightDensity_factorization μ g hε.ne']
  change singleFlightDensity ε s y (0,0) •
      ((∫z,w z ∂μ)•(regressionBeta s•y)+∫z,w z•F z ∂μ)=
    (singleFlightDensity ε s y (0,0)*(∫z,w z ∂μ)) •
      (regressionBeta s•y+(∫z,w z ∂μ)⁻¹•∫z,w z•F z ∂μ)
  have hc:(∫z,w z ∂μ) •
      (regressionBeta s•y+(∫z,w z ∂μ)⁻¹•∫z,w z•F z ∂μ)=
      (∫z,w z ∂μ)•(regressionBeta s•y)+∫z,w z•F z ∂μ := by
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
  rw [mul_smul,hc]

end PersistencePays
#print axioms PersistencePays.gaussianFlightFlux_eq_density_mean
