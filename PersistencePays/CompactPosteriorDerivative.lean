import PersistencePays.AffinePosteriorBounds

/-! The derivative and quantitative bound for a parameter-dependent posterior
expectation over a compact latent space. Normalizers cancel exactly. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
variable {P Z V:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

def compactWeightedMean (μ:Measure Z) (ψ:P→Z→ℝ) (F:P→Z→V) (x:P):V :=
  (∫z,Real.exp (ψ x z) ∂μ)⁻¹ • ∫z,Real.exp (ψ x z) • F x z ∂μ

theorem compactWeightedMean_normalizer_pos (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:P→Z→ℝ} (hψ:Continuous ψ.uncurry) (x:P) :
    0<∫z,Real.exp (ψ x z) ∂μ := by
  apply integral_exp_pos
  exact (Real.continuous_exp.comp (hψ.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem compactWeightedMean_hasFDerivAt (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:P→Z→ℝ} {F:P→Z→V} {ψ':P→Z→P→L[ℝ]ℝ} {F':P→Z→P→L[ℝ]V}
    (hψ:Continuous ψ.uncurry) (hF:Continuous F.uncurry)
    (hψ':Continuous ψ'.uncurry) (hF':Continuous F'.uncurry)
    (hdψ:∀x z,HasFDerivAt (fun y=>ψ y z) (ψ' x z) x)
    (hdF:∀x z,HasFDerivAt (fun y=>F y z) (F' x z) x) (x:P) :
    let D:=∫z,Real.exp (ψ x z) ∂μ
    let N:=∫z,Real.exp (ψ x z) • F x z ∂μ
    let D':=∫z,Real.exp (ψ x z) • ψ' x z ∂μ
    let N':=∫z,Real.exp (ψ x z) • (F' x z+(ψ' x z).smulRight (F x z)) ∂μ
    HasFDerivAt (compactWeightedMean μ ψ F)
      (D⁻¹ • N'-(D⁻¹)^2 • D'.smulRight N) x := by
  dsimp only
  have hw:Continuous (fun p:P×Z=>Real.exp (ψ p.1 p.2)):=Real.continuous_exp.comp hψ
  have hd:=compact_parameter_integral_hasFDerivAt μ
    (F:=fun x z=>Real.exp (ψ x z)) (F':=fun x z=>Real.exp (ψ x z) • ψ' x z)
    hw (hw.smul hψ') (fun x z=>(hdψ x z).exp) x
  have hn:=compact_parameter_integral_hasFDerivAt μ
    (F:=fun x z=>Real.exp (ψ x z) • F x z)
    (F':=fun x z=>Real.exp (ψ x z) • (F' x z+(ψ' x z).smulRight (F x z)))
    (hw.smul hF) (hw.smul (hF'.add ((ContinuousLinearMap.smulRightL ℝ P V).continuous₂.comp₂ hψ' hF)))
    (fun y z=>by
      convert ((hdψ y z).exp.smul (hdF y z)) using 1 <;>
        ext v <;> simp [smul_add,smul_smul]) x
  have hp:=compactWeightedMean_normalizer_pos μ hψ x
  have hh:=((hasFDerivAt_inv hp.ne').comp x hd).smul hn
  convert hh using 1
  · ext y
    rfl
  · ext v
    simp
    module

theorem compactWeightedMean_fderiv_norm (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:P→Z→ℝ} {F:P→Z→V} {ψ':P→Z→P→L[ℝ]ℝ} {F':P→Z→P→L[ℝ]V}
    (hψ:Continuous ψ.uncurry) (hF:Continuous F.uncurry)
    (hψ':Continuous ψ'.uncurry) (hF':Continuous F'.uncurry)
    (hdψ:∀x z,HasFDerivAt (fun y=>ψ y z) (ψ' x z) x)
    (hdF:∀x z,HasFDerivAt (fun y=>F y z) (F' x z) x)
    (x:P) {A B C:ℝ} (hA:0≤A) (hB:0≤B) (hC:0≤C)
    (bF:∀z,‖F x z‖≤A) (bψ':∀z,‖ψ' x z‖≤B) (bF':∀z,‖F' x z‖≤C) :
    ‖fderiv ℝ (compactWeightedMean μ ψ F) x‖≤C+2*A*B := by
  let w:Z→ℝ:=fun z=>Real.exp (ψ x z)
  let D:=∫z,w z ∂μ
  let N:=∫z,w z • F x z ∂μ
  let D':=∫z,w z • ψ' x z ∂μ
  let N':=∫z,w z • (F' x z+(ψ' x z).smulRight (F x z)) ∂μ
  have hw:Continuous w:=Real.continuous_exp.comp (hψ.comp (continuous_const.prodMk continuous_id))
  have hw0(z:Z):0≤w z:=(Real.exp_pos _).le
  have hp:0<D:=compactWeightedMean_normalizer_pos μ hψ x
  have hFc:Continuous (F x):=hF.comp (continuous_const.prodMk continuous_id)
  have hψc:Continuous (ψ' x):=hψ'.comp (continuous_const.prodMk continuous_id)
  have hF'c:Continuous (F' x):=hF'.comp (continuous_const.prodMk continuous_id)
  have hN:‖N‖≤D*A:=compact_weighted_integral_norm μ w _ hw hFc hw0 bF
  have hD':‖D'‖≤D*B:=compact_weighted_integral_norm μ w _ hw hψc hw0 bψ'
  have hN':‖N'‖≤D*(C+B*A):=compact_weighted_integral_norm μ w _ hw
    (hF'c.add ((ContinuousLinearMap.smulRightL ℝ P V).continuous₂.comp₂ hψc hFc)) hw0
    (fun z=>by
      apply (norm_add_le _ _).trans
      apply add_le_add (bF' z)
      change ‖(ψ' x z).smulRight (F x z)‖≤B*A
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul (bψ' z) (bF z) (norm_nonneg _) hB)
  have hd: fderiv ℝ (compactWeightedMean μ ψ F) x=D⁻¹•N'-(D⁻¹)^2•D'.smulRight N :=
    (compactWeightedMean_hasFDerivAt μ hψ hF hψ' hF' hdψ hdF x).fderiv
  rw [hd]
  calc
    _ ≤ ‖D⁻¹•N'‖+‖(D⁻¹)^2•D'.smulRight N‖:=norm_sub_le _ _
    _ = D⁻¹*‖N'‖+(D⁻¹)^2*(‖D'‖*‖N‖) := by
      rw [norm_smul,norm_smul,ContinuousLinearMap.norm_smulRight_apply,
        Real.norm_of_nonneg (inv_nonneg.mpr hp.le),Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ D⁻¹*(D*(C+B*A))+(D⁻¹)^2*((D*B)*(D*A)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hN' (inv_nonneg.mpr hp.le))
        (mul_le_mul_of_nonneg_left (mul_le_mul hD' hN (norm_nonneg _) (by positivity)) (sq_nonneg _))
    _ = C+2*A*B := by field_simp; ring

end PersistencePays
#print axioms PersistencePays.compactWeightedMean_fderiv_norm
