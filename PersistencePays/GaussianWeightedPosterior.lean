import PersistencePays.GaussianFlightFlux
import PersistencePays.AffinePosteriorMoments

/-! Density-weighted Gaussian component moments and their normalized posterior. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma gaussian_weighted_posterior (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) (F:Z→V) :
    (∫z,singleFlightDensity ε s y (g z)•F z ∂μ)=
      gaussianFlightDensity μ g ε s y •
        affinePosteriorMean μ F (fun z=>regressionScore ε s (g z))
          (fun z=>regressionLogWeight ε s (g z)) y := by
  let w:Z→ℝ:=fun z=>Real.exp (regressionExponent ε s (y,g z))
  have hw:Continuous w:=Real.continuous_exp.comp (regressionExponent_latent_continuous g hg ε s y)
  have hi:Integrable w μ:=hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp:0<∫z,w z ∂μ:=integral_exp_pos hi
  have he:(fun z=>singleFlightDensity ε s y (g z)•F z)=
      (fun z=>singleFlightDensity ε s y (0,0)•(w z•F z)) := by
    funext z
    rw [singleFlightDensity_factorization hε.ne',mul_smul]
  rw [he,integral_smul,gaussianFlightDensity_factorization μ g hε.ne']
  change singleFlightDensity ε s y (0,0) • (∫z,w z•F z ∂μ)=
    (singleFlightDensity ε s y (0,0)*(∫z,w z ∂μ)) •
      ((∫z,w z ∂μ)⁻¹•∫z,w z•F z ∂μ)
  rw [smul_smul]
  congr 1
  field_simp

lemma affinePosteriorMean_const_add (μ:Measure Z) [IsProbabilityMeasure μ]
    (F:Z→V) (H:Z→E) (k:Z→ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (y:E) (c:V) :
    affinePosteriorMean μ (fun z=>c+F z) H k y=c+affinePosteriorMean μ F H k y := by
  letI:=affinePosterior_tilt_probability μ H k hH hk y
  rw [affinePosteriorMean_eq_integral,affinePosteriorMean_eq_integral,
    integral_add (integrable_const _) (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp

lemma affinePosteriorCovariance_const_add (μ:Measure Z) [IsProbabilityMeasure μ]
    (F H:Z→E) (k:Z→ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (τ:ℝ) (y c:E) :
    affinePosteriorCovariance μ (fun z=>c+F z) H k τ y=
      affinePosteriorCovariance μ F H k τ y := by
  let ρ:=μ.tilted (fun z=>⟪H z,y⟫+k z)
  letI:IsProbabilityMeasure ρ:=affinePosterior_tilt_probability μ H k hH hk y
  letI:IsProbabilityMeasure (ρ.map F):=Measure.isProbabilityMeasure_map hF.measurable.aemeasurable
  have hm:ρ.map (fun z=>c+F z)=(ρ.map F).map (fun x=>c+x) := by
    rw [Measure.map_map (by fun_prop) hF.measurable]
    rfl
  ext v
  apply ext_inner_left ℝ
  intro u
  rw [affinePosteriorCovariance_bilin μ (fun z=>c+F z) H k (continuous_const.add hF) hH hk,
    affinePosteriorCovariance_bilin μ F H k hF hH hk]
  change covarianceBilin (ρ.map (fun z=>c+F z)) u v+_=covarianceBilin (ρ.map F) u v+_
  rw [hm,covarianceBilin_map_const_add]

end PersistencePays
#print axioms PersistencePays.gaussian_weighted_posterior
#print axioms PersistencePays.affinePosteriorCovariance_const_add
