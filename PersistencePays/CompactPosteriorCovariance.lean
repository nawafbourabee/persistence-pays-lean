import PersistencePays.CompactPosteriorDerivative

/-! Covariance representation of the derivative of a varying posterior mean. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
variable {P Z V:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem compactWeightedMean_norm (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:P→Z→ℝ} {F:P→Z→V} (hψ:Continuous ψ.uncurry) (hF:Continuous F.uncurry)
    (x:P) {A:ℝ} (hA:∀z,‖F x z‖≤A) : ‖compactWeightedMean μ ψ F x‖≤A := by
  have hw:Continuous (fun z=>Real.exp (ψ x z)):=Real.continuous_exp.comp
    (hψ.comp (continuous_const.prodMk continuous_id))
  have hn:=compact_weighted_integral_norm μ _ (F x) hw
    (hF.comp (continuous_const.prodMk continuous_id)) (fun z=>(Real.exp_pos _).le) hA
  have hp:=compactWeightedMean_normalizer_pos μ hψ x
  unfold compactWeightedMean
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  calc
    _ ≤ (∫z,Real.exp (ψ x z) ∂μ)⁻¹*((∫z,Real.exp (ψ x z) ∂μ)*A) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
    _ = A := by field_simp

theorem compactWeightedMean_fderiv_covariance (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:P→Z→ℝ} {F:P→Z→V} {ψ':P→Z→P→L[ℝ]ℝ} {F':P→Z→P→L[ℝ]V}
    (hψ:Continuous ψ.uncurry) (hF:Continuous F.uncurry)
    (hψ':Continuous ψ'.uncurry) (hF':Continuous F'.uncurry)
    (hdψ:∀x z,HasFDerivAt (fun y=>ψ y z) (ψ' x z) x)
    (hdF:∀x z,HasFDerivAt (fun y=>F y z) (F' x z) x) (x:P) :
    fderiv ℝ (compactWeightedMean μ ψ F) x=
      compactWeightedMean μ ψ F' x+
      compactWeightedMean μ ψ (fun y z=>(ψ' y z).smulRight (F y z)) x-
      (compactWeightedMean μ ψ ψ' x).smulRight (compactWeightedMean μ ψ F x) := by
  rw [(compactWeightedMean_hasFDerivAt μ hψ hF hψ' hF' hdψ hdF x).fderiv]
  have hw:Continuous (fun z=>Real.exp (ψ x z)):=Real.continuous_exp.comp
    (hψ.comp (continuous_const.prodMk continuous_id))
  have hcF':Continuous (F' x):=hF'.comp (continuous_const.prodMk continuous_id)
  have hcT:Continuous (fun z=>(ψ' x z).smulRight (F x z)):=
    (ContinuousLinearMap.smulRightL ℝ P V).continuous₂.comp₂
      (hψ'.comp (continuous_const.prodMk continuous_id))
      (hF.comp (continuous_const.prodMk continuous_id))
  have hiF':Integrable (fun z=>Real.exp (ψ x z) • F' x z) μ:=
    (hw.smul hcF').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiT:Integrable (fun z=>Real.exp (ψ x z) • (ψ' x z).smulRight (F x z)) μ:=
    (hw.smul hcT).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [smul_add]
  rw [integral_add hiF' hiT]
  unfold compactWeightedMean
  ext v
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    smul_add,smul_smul,smul_eq_mul,pow_two]
  module

end PersistencePays
#print axioms PersistencePays.compactWeightedMean_fderiv_covariance
