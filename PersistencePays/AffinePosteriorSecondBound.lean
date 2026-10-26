import PersistencePays.AffinePosteriorBounds

/-! The spatial derivative is a covariance. Bounded latent scores give a
uniform Lipschitz bound on that covariance and hence a quadratic remainder. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped InnerProductSpace NNReal
variable {E Z V:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem affinePosteriorMean_fderiv_covariance (μ:Measure Z) [IsProbabilityMeasure μ]
    (F:Z→V) (H:Z→E) (k:Z→ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k) (y:E) :
    fderiv ℝ (affinePosteriorMean μ F H k) y=
      affinePosteriorMean μ (fun z=>(innerSL ℝ (H z)).smulRight (F z)) H k y-
      (affinePosteriorMean μ (fun z=>innerSL ℝ (H z)) H k y).smulRight
        (affinePosteriorMean μ F H k y) := by
  rw [(affinePosteriorMean_hasFDerivAt μ F H k hF hH hk y).fderiv]
  unfold affinePosteriorMean
  ext v
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,smul_smul,pow_two]
  module

theorem smulRight_sub_norm_le (r s:E→L[ℝ]ℝ) (v w:V) :
    ‖r.smulRight v-s.smulRight w‖≤‖r‖*‖v-w‖+‖r-s‖*‖w‖ := by
  have heq:r.smulRight v-s.smulRight w=r.smulRight (v-w)+(r-s).smulRight w := by
    ext x
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply,smul_sub,sub_smul]
    module
  rw [heq]
  exact (norm_add_le _ _).trans_eq (by rw [ContinuousLinearMap.norm_smulRight_apply,
    ContinuousLinearMap.norm_smulRight_apply])

theorem affinePosteriorMean_fderiv_lipschitz (μ:Measure Z) [IsProbabilityMeasure μ]
    (F:Z→V) (H:Z→E) (k:Z→ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (A B:ℝ≥0) (hA:∀z,‖F z‖≤A) (hB:∀z,‖H z‖≤B) :
    LipschitzWith (6*A*B^2) (fderiv ℝ (affinePosteriorMean μ F H k)) := by
  let R:Z→E→L[ℝ]ℝ:=fun z=>innerSL ℝ (H z)
  let T:Z→E→L[ℝ]V:=fun z=>(R z).smulRight (F z)
  have hR:Continuous R:=(innerSL ℝ).continuous.comp hH
  have hT:Continuous T:=(ContinuousLinearMap.smulRightL ℝ E V).continuous₂.comp₂ hR hF
  have hbR(z:Z):‖R z‖≤B := by simpa only [R,innerSL_apply_norm] using hB z
  have hbT(z:Z):‖T z‖≤B*A := by
    change ‖(R z).smulRight (F z)‖≤_
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (hbR z) (hA z) (norm_nonneg _) B.property
  have hFl:=affinePosteriorMean_lipschitz μ F H k hF hH hk A B hA hB
  have hRl:=affinePosteriorMean_lipschitz μ R H k hR hH hk B B hbR hB
  have hTl:=affinePosteriorMean_lipschitz μ T H k hT hH hk (B*A) B hbT hB
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,affinePosteriorMean_fderiv_covariance μ F H k hF hH hk]
  have hFxy:=hFl.dist_le_mul x y
  have hRxy:=hRl.dist_le_mul x y
  have hTxy:=hTl.dist_le_mul x y
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_ofNat] at hFxy hRxy hTxy
  have hRx:=affinePosteriorMean_norm μ R H k hR hH hk hbR x
  have hFy:=affinePosteriorMean_norm μ F H k hF hH hk hA y
  have hbil:=smulRight_sub_norm_le (affinePosteriorMean μ R H k x)
    (affinePosteriorMean μ R H k y) (affinePosteriorMean μ F H k x) (affinePosteriorMean μ F H k y)
  change ‖(affinePosteriorMean μ T H k x-
      (affinePosteriorMean μ R H k x).smulRight (affinePosteriorMean μ F H k x))-
      (affinePosteriorMean μ T H k y-
      (affinePosteriorMean μ R H k y).smulRight (affinePosteriorMean μ F H k y))‖≤_
  calc
    _ ≤ ‖affinePosteriorMean μ T H k x-affinePosteriorMean μ T H k y‖+
        ‖(affinePosteriorMean μ R H k x).smulRight (affinePosteriorMean μ F H k x)-
          (affinePosteriorMean μ R H k y).smulRight (affinePosteriorMean μ F H k y)‖ :=
      by
        convert norm_sub_le
          (affinePosteriorMean μ T H k x-affinePosteriorMean μ T H k y)
          ((affinePosteriorMean μ R H k x).smulRight (affinePosteriorMean μ F H k x)-
            (affinePosteriorMean μ R H k y).smulRight (affinePosteriorMean μ F H k y)) using 1
        congr 1
        abel
    _ ≤ 2*((B:ℝ)*A)*B*‖x-y‖+
        ((B:ℝ)*(2*A*B*‖x-y‖)+(2*B*B*‖x-y‖)*A) := by
      apply add_le_add hTxy
      apply hbil.trans
      exact add_le_add
        (mul_le_mul hRx hFxy (norm_nonneg _) B.property)
        (mul_le_mul hRxy hFy (norm_nonneg _) (by positivity))
    _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow]; ring

theorem quadratic_remainder_of_lipschitz_fderiv {f:E→V} (hf:Differentiable ℝ f)
    {K:ℝ≥0} (hK:LipschitzWith K (fderiv ℝ f)) (x y:E) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖≤(K:ℝ)*‖y-x‖^2 := by
  have hh:‖f y-f x-fderiv ℝ f x (y-x)‖≤((K:ℝ)*‖y-x‖)*‖y-x‖ := by
    apply (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z _=>(hf z).hasFDerivAt.hasFDerivWithinAt)
    · intro z hz
      have hd:=hK.dist_le_mul z x
      have hz':dist z x≤dist x y:=segment_subset_closedBall_left x y hz
      calc
        _ ≤ (K:ℝ)*dist z x := by simpa only [dist_eq_norm] using hd
        _ ≤ (K:ℝ)*dist x y := mul_le_mul_of_nonneg_left hz' K.property
        _ = (K:ℝ)*‖y-x‖ := by rw [dist_comm,dist_eq_norm]
    · exact left_mem_segment ℝ x y
    · exact right_mem_segment ℝ x y
  nlinarith [hh]

theorem affinePosteriorMean_quadratic_remainder (μ:Measure Z) [IsProbabilityMeasure μ]
    (F:Z→V) (H:Z→E) (k:Z→ℝ) (hF:Continuous F) (hH:Continuous H) (hk:Continuous k)
    (A B:ℝ≥0) (hA:∀z,‖F z‖≤A) (hB:∀z,‖H z‖≤B) (x y:E) :
    ‖affinePosteriorMean μ F H k y-affinePosteriorMean μ F H k x-
      fderiv ℝ (affinePosteriorMean μ F H k) x (y-x)‖≤
      (6*(A:ℝ)*B^2)*‖y-x‖^2 := by
  exact_mod_cast quadratic_remainder_of_lipschitz_fderiv
    (fun z=>(affinePosteriorMean_hasFDerivAt μ F H k hF hH hk z).differentiableAt)
    (affinePosteriorMean_fderiv_lipschitz μ F H k hF hH hk A B hA hB) x y

end PersistencePays
#print axioms PersistencePays.affinePosteriorMean_quadratic_remainder
