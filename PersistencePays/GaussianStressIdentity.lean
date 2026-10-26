import PersistencePays.GaussianCovarianceIdentity
import PersistencePays.GaussianMixturePDE

/-! The actual covariance stress equals the conserved second moment minus mean flux. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

def gaussianFlightStress (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):E→L[ℝ]E :=
  gaussianFlightDensity μ g ε s y • gaussianRegressionCovariance μ g ε s y

theorem gaussianFlightStress_eq_moment_defect (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    gaussianFlightStress μ g ε s y=gaussianFlightSecondMoment μ g ε s y-
      gaussianFlightDensity μ g ε s y • rankOneField (gaussianMeanField μ g ε s) y := by
  let F:Z→E:=fun z=>regressionLatentMean s (g z)
  let H:Z→E:=fun z=>regressionScore ε s (g z)
  let k:Z→ℝ:=fun z=>regressionLogWeight ε s (g z)
  let B:Z→E:=fun z=>regressionBeta s•y+F z
  let R:Z→E→L[ℝ]E:=fun z=>(innerSL ℝ (B z)).smulRight (B z)
  let I:E→L[ℝ]E:=(ε^2/(1+s^2))•ContinuousLinearMap.id ℝ E
  have hF:Continuous F:=regressionLatentMean_latent_continuous g hg s
  have hH:Continuous H:=regressionScore_latent_continuous g hg ε s
  have hk:Continuous k:=regressionLogWeight_latent_continuous g hg ε s
  have hB:Continuous B:=continuous_const.add hF
  have hR:Continuous R:=(ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂
    ((innerSL ℝ).continuous.comp hB) hB
  have hm:affinePosteriorMean μ B H k y=gaussianMeanField μ g ε s y :=
    affinePosteriorMean_const_add μ F H k hF hH hk y (regressionBeta s•y)
  have hc:affinePosteriorCovariance μ B H k (ε^2/(1+s^2)) y=
      gaussianRegressionCovariance μ g ε s y :=
    affinePosteriorCovariance_const_add μ F H k hF hH hk _ y (regressionBeta s•y)
  have hM:gaussianFlightSecondMoment μ g ε s y=
      gaussianFlightDensity μ g ε s y • (I+affinePosteriorMean μ R H k y) := by
    unfold gaussianFlightSecondMoment
    have he:(fun z=>singleFlightMoment ε s y (g z))=
        (fun z=>singleFlightDensity ε s y (g z)•(I+R z)) := by
      funext z
      unfold singleFlightMoment rankOneField
      dsimp only
      rw [singleFlightVelocity_eq]
      change _=singleFlightDensity ε s y (g z)•(I+R z)
      dsimp only [R,B,F,I]
      module
    rw [he,gaussian_weighted_posterior μ g hg hε,
      affinePosteriorMean_const_add μ R H k hR hH hk]
  rw [hM]
  unfold gaussianFlightStress
  rw [←hc]
  unfold affinePosteriorCovariance
  rw [hm]
  change gaussianFlightDensity μ g ε s y •
      (affinePosteriorMean μ R H k y-rankOneField (gaussianMeanField μ g ε s) y+I)=_
  module

theorem gaussianFlightStress_space_contDiff (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ContDiff ℝ 1 (gaussianFlightStress μ g ε s) := by
  have hp:ContDiff ℝ 1 (fun y:E=>(s,y)) := contDiff_const.prodMk contDiff_id
  have hM := (gaussianFlightSecondMoment_contDiff 1 μ g hg hε.ne').comp hp
  have hn:ContDiff ℝ 1 (gaussianFlightDensity μ g ε s):=
    (gaussianFlightDensity_contDiff 1 μ g hg hε.ne').comp (contDiff_const.prodMk contDiff_id)
  have hb:ContDiff ℝ 1 (gaussianMeanField μ g ε s):=
    (gaussianMeanField_contDiff 1 μ g hg hε.ne').comp (contDiff_const.prodMk contDiff_id)
  have he:gaussianFlightStress μ g ε s=(fun y=>gaussianFlightSecondMoment μ g ε s y-
      gaussianFlightDensity μ g ε s y • rankOneField (gaussianMeanField μ g ε s) y) := by
    funext y; exact gaussianFlightStress_eq_moment_defect μ g hg hε s y
  rw [he]
  exact hM.sub (hn.smul (rankOneField_contDiff hb))

theorem gaussianFlightStress_actual (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ∀ᵐ y ∂(gaussianFlightLaw (μ.map g) ε s).fst,∀u v:E,
      ⟪u,gaussianFlightStress μ g ε s y v⟫=gaussianFlightDensity μ g ε s y*
        covarianceBilin ((gaussianFlightLaw (μ.map g) ε s).condKernel y) u v := by
  filter_upwards [gaussianRegressionCovariance_actual μ g hg hε s] with y hy
  intro u v
  simp only [gaussianFlightStress,ContinuousLinearMap.smul_apply,real_inner_smul_right,hy]

end PersistencePays
#print axioms PersistencePays.gaussianFlightStress_eq_moment_defect
#print axioms PersistencePays.gaussianFlightStress_actual
