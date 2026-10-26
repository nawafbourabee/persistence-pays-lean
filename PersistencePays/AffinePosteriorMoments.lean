import PersistencePays.GaussianCovarianceField
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.MeasureTheory.Measure.Tilted

/-! The affine posterior's mean and covariance operators are actual moments. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
variable {E Z V:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Z] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma affinePosteriorMean_eq_integral (μ:Measure Z) (F:Z→V) (H:Z→E) (k:Z→ℝ) (y:E) :
    affinePosteriorMean μ F H k y=
      ∫z,F z ∂μ.tilted (fun z=>⟪H z,y⟫+k z) := by
  rw [integral_tilted]
  unfold affinePosteriorMean affinePosteriorWeight
  rw [←integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [smul_smul,div_eq_inv_mul]

variable [TopologicalSpace Z] [CompactSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

lemma affinePosterior_tilt_probability (μ:Measure Z) [IsProbabilityMeasure μ]
    (H:Z→E) (k:Z→ℝ) (hH:Continuous H) (hk:Continuous k) (y:E) :
    IsProbabilityMeasure (μ.tilted (fun z=>⟪H z,y⟫+k z)) := by
  apply isProbabilityMeasure_tilted
  exact (Real.continuous_exp.comp ((hH.inner continuous_const).add hk)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem affinePosteriorCovariance_bilin (μ:Measure Z) [IsProbabilityMeasure μ]
    (F H:Z→E) (k:Z→ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (τ:ℝ) (y u v:E) :
    ⟪u,affinePosteriorCovariance μ F H k τ y v⟫=
      covarianceBilin ((μ.tilted (fun z=>⟪H z,y⟫+k z)).map F) u v+τ*⟪u,v⟫ := by
  let ρ:=μ.tilted (fun z=>⟪H z,y⟫+k z)
  letI:IsProbabilityMeasure ρ:=affinePosterior_tilt_probability μ H k hH hk y
  letI:IsProbabilityMeasure (ρ.map F):=Measure.isProbabilityMeasure_map hF.measurable.aemeasurable
  have hFlp:MemLp F 2 ρ:=hF.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmap:MemLp id 2 (ρ.map F):=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hF.measurable.aemeasurable).mpr hFlp
  have hFu:MemLp (fun z=>⟪u,F z⟫) 2 ρ:=
    (continuous_const.inner hF).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFv:MemLp (fun z=>⟪v,F z⟫) 2 ρ:=
    (continuous_const.inner hF).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let R:Z→E→L[ℝ]E:=fun z=>(innerSL ℝ (F z)).smulRight (F z)
  have hR:Continuous R:=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂
      ((innerSL ℝ).continuous.comp hF) hF)
  have hiR:Integrable R ρ:=hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiRv:Integrable (fun z=>R z v) ρ:=
    (hR.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heR:⟪u,(∫z,R z ∂ρ) v⟫=∫z,⟪u,F z⟫*⟪v,F z⟫ ∂ρ := by
    rw [ContinuousLinearMap.integral_apply hiR v]
    have hh:=((innerSL ℝ u).integral_comp_comm hiRv).symm
    change ⟪u,∫z,R z v ∂ρ⟫=∫z,⟪u,R z v⟫ ∂ρ at hh
    rw [hh]
    apply integral_congr_ae
    filter_upwards with z
    simp only [R,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,real_inner_smul_right]
    rw [real_inner_comm (F z) v,mul_comm]
  have heM (a:E):⟪a,∫z,F z ∂ρ⟫=∫z,⟪a,F z⟫ ∂ρ :=
    ((innerSL ℝ a).integral_comp_comm (hFlp.integrable (by norm_num))).symm
  unfold affinePosteriorCovariance
  rw [affinePosteriorMean_eq_integral,affinePosteriorMean_eq_integral]
  change ⟪u,((∫z,R z ∂ρ)-(innerSL ℝ (∫z,F z ∂ρ)).smulRight (∫z,F z ∂ρ)+
    τ•ContinuousLinearMap.id ℝ E) v⟫=covarianceBilin (ρ.map F) u v+τ*⟪u,v⟫
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,inner_add_right,inner_sub_right,real_inner_smul_right]
  have hev:⟪∫z,F z ∂ρ,v⟫=∫z,⟪v,F z⟫ ∂ρ := (real_inner_comm _ _).trans (heM v)
  rw [heR,hev,heM u,
    covarianceBilin_apply_eq_cov hmap,covariance_map_fun (by fun_prop) (by fun_prop)
      hF.measurable.aemeasurable,covariance_eq_sub hFu hFv]
  simp only [Pi.mul_apply]
  ring

end PersistencePays
#print axioms PersistencePays.affinePosteriorCovariance_bilin
