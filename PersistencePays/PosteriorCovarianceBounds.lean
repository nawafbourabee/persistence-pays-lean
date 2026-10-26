import PersistencePays.GaussianCovarianceField
import PersistencePays.AffinePosteriorSecondBound

/-! Uniform covariance and spatial derivative bounds for actual compact affine
posteriors; the potentially small normalization cancels in the proved bounds. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped InnerProductSpace NNReal
variable {E Z:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem affinePosteriorCovariance_norm (μ:Measure Z) [IsProbabilityMeasure μ]
    (F H:Z→E) (k:Z→ℝ) (τ:ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    {A:ℝ} (hA0:0≤A) (hA:∀z,‖F z‖≤A) (y:E) :
    ‖affinePosteriorCovariance μ F H k τ y‖≤2*A^2+|τ| := by
  let R:Z→E→L[ℝ]E:=fun z=>(innerSL ℝ (F z)).smulRight (F z)
  have hR:Continuous R:=(ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂
    ((innerSL ℝ).continuous.comp hF) hF
  have hbR (z:Z):‖R z‖≤A^2 := by
    dsimp only [R]
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,pow_two]
    exact mul_le_mul (hA z) (hA z) (norm_nonneg _) hA0
  have hsecond:=affinePosteriorMean_norm μ R H k hR hH hk hbR y
  have hmean:=affinePosteriorMean_norm μ F H k hF hH hk hA y
  have hrank:‖(innerSL ℝ (affinePosteriorMean μ F H k y)).smulRight
      (affinePosteriorMean μ F H k y)‖≤A^2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,pow_two]
    exact mul_le_mul hmean hmean (norm_nonneg _) hA0
  have hid:‖τ•ContinuousLinearMap.id ℝ E‖≤|τ| := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg τ)).trans_eq (mul_one _)
  unfold affinePosteriorCovariance
  exact (norm_add_le _ _).trans ((add_le_add
    ((norm_sub_le _ _).trans (add_le_add hsecond hrank)) hid).trans_eq (by ring))

theorem affinePosteriorCovariance_lipschitz (μ:Measure Z) [IsProbabilityMeasure μ]
    (F H:Z→E) (k:Z→ℝ) (τ:ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (A B:ℝ≥0) (hA:∀z,‖F z‖≤A) (hB:∀z,‖H z‖≤B) :
    LipschitzWith (6*A^2*B) (affinePosteriorCovariance μ F H k τ) := by
  let R:Z→E→L[ℝ]E:=fun z=>(innerSL ℝ (F z)).smulRight (F z)
  have hR:Continuous R:=(ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂
    ((innerSL ℝ).continuous.comp hF) hF
  have hbR (z:Z):‖R z‖≤(A:ℝ)^2 := by
    dsimp only [R]
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,pow_two]
    exact mul_le_mul (hA z) (hA z) (norm_nonneg _) A.property
  have hm:=affinePosteriorMean_lipschitz μ F H k hF hH hk A B hA hB
  have hRlip:=affinePosteriorMean_lipschitz μ R H k hR hH hk (A^2) B (fun z=>by exact_mod_cast hbR z) hB
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  have hmxy:=hm.dist_le_mul x y
  have hRxy:=hRlip.dist_le_mul x y
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat] at hmxy hRxy
  have hmx:=affinePosteriorMean_norm μ F H k hF hH hk hA x
  have hmy:=affinePosteriorMean_norm μ F H k hF hH hk hA y
  have hbil:=smulRight_sub_norm_le (innerSL ℝ (affinePosteriorMean μ F H k x))
    (innerSL ℝ (affinePosteriorMean μ F H k y))
    (affinePosteriorMean μ F H k x) (affinePosteriorMean μ F H k y)
  simp only [←map_sub,innerSL_apply_norm] at hbil
  have hsub : affinePosteriorCovariance μ F H k τ x-affinePosteriorCovariance μ F H k τ y=
      (affinePosteriorMean μ R H k x-affinePosteriorMean μ R H k y)-
      ((innerSL ℝ (affinePosteriorMean μ F H k x)).smulRight (affinePosteriorMean μ F H k x)-
       (innerSL ℝ (affinePosteriorMean μ F H k y)).smulRight (affinePosteriorMean μ F H k y)) := by
    unfold affinePosteriorCovariance R
    abel
  rw [hsub]
  calc
    _≤‖affinePosteriorMean μ R H k x-affinePosteriorMean μ R H k y‖+
       ‖(innerSL ℝ (affinePosteriorMean μ F H k x)).smulRight (affinePosteriorMean μ F H k x)-
        (innerSL ℝ (affinePosteriorMean μ F H k y)).smulRight (affinePosteriorMean μ F H k y)‖:=norm_sub_le _ _
    _≤2*(A:ℝ)^2*B*‖x-y‖+
       ((A:ℝ)*(2*A*B*‖x-y‖)+(2*A*B*‖x-y‖)*A):=by
      apply add_le_add hRxy
      apply hbil.trans
      exact add_le_add
        (mul_le_mul hmx hmxy (norm_nonneg _) A.property)
        (mul_le_mul hmxy hmy (norm_nonneg _) (by positivity))
    _=_:=by simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat]; ring

theorem affinePosteriorCovariance_fderiv_bound (μ:Measure Z) [IsProbabilityMeasure μ]
    (F H:Z→E) (k:Z→ℝ) (τ:ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (A B:ℝ≥0) (hA:∀z,‖F z‖≤A) (hB:∀z,‖H z‖≤B) (y:E) :
    ‖fderiv ℝ (affinePosteriorCovariance μ F H k τ) y‖≤6*(A:ℝ)^2*B := by
  exact_mod_cast norm_fderiv_le_of_lipschitz ℝ
    (affinePosteriorCovariance_lipschitz μ F H k τ hF hH hk A B hA hB)

end PersistencePays
#print axioms PersistencePays.affinePosteriorCovariance_norm
#print axioms PersistencePays.affinePosteriorCovariance_fderiv_bound
