import PersistencePays.GaussianMeanField
import PersistencePays.PartialDerivativeContinuous

/-! Global bounds for the actual compact-latent conditional-mean formula. -/
set_option maxHeartbeats 1600000
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped InnerProductSpace NNReal
universe u
variable {E Z:Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem gaussianMeanRemainder_bounds (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (A B:ℝ≥0)
    (hA:∀s z,‖regressionLatentMean s (g z)‖≤A)
    (hB:∀s z,‖regressionScore ε s (g z)‖≤B) (s:ℝ) :
    (∀y,‖gaussianMeanRemainder μ g ε s y‖≤A) ∧
    LipschitzWith (2*A*B) (gaussianMeanRemainder μ g ε s) ∧
    (∀y,‖fderiv ℝ (gaussianMeanRemainder μ g ε s) y‖≤(2*A*B:ℝ≥0)) ∧
    LipschitzWith (6*A*B^2) (fderiv ℝ (gaussianMeanRemainder μ g ε s)) := by
  have hF:Continuous (fun z=>regressionLatentMean s (g z)) :=
    (regressionLatentMean_contDiff 0).continuous.comp (continuous_const.prodMk hg)
  have hH:Continuous (fun z=>regressionScore ε s (g z)) :=
    (regressionScore_contDiff 0 hε).continuous.comp (continuous_const.prodMk hg)
  have hk:Continuous (fun z=>regressionLogWeight ε s (g z)) :=
    (regressionLogWeight_contDiff 0 hε).continuous.comp (continuous_const.prodMk hg)
  refine ⟨affinePosteriorMean_norm μ _ _ _ hF hH hk (hA s),
    affinePosteriorMean_lipschitz μ _ _ _ hF hH hk A B (hA s) (hB s),?_,
    affinePosteriorMean_fderiv_lipschitz μ _ _ _ hF hH hk A B (hA s) (hB s)⟩
  intro y
  exact_mod_cast affinePosteriorMean_fderiv_bound μ _ _ _ hF hH hk
    A.property B.property (hA s) (hB s) y

theorem regressionBeta_abs_le_one (s:ℝ) : |regressionBeta s|≤1 := by
  have hd:0<1+s^2 := by positivity
  rw [regressionBeta,abs_div,abs_of_pos hd]
  apply (div_le_one hd).mpr
  nlinarith [sq_nonneg (|s|-1),sq_abs s]

theorem gaussianMeanField_spatial_fderiv (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) :
    fderiv ℝ (gaussianMeanField μ g ε s) y=
      regressionBeta s • ContinuousLinearMap.id ℝ E+
        fderiv ℝ (gaussianMeanRemainder μ g ε s) y := by
  have hb:Differentiable ℝ (gaussianMeanRemainder μ g ε s) :=
    ((gaussianMeanRemainder_contDiff 1 μ g hg hε).differentiable (by norm_num)).comp
      (differentiable_const s |>.prodMk differentiable_id)
  exact (((hasFDerivAt_id (𝕜:=ℝ) y).const_smul (regressionBeta s)).add
    (hb y).hasFDerivAt).fderiv

theorem gaussianMeanField_bounds (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (A B:ℝ≥0)
    (hA:∀s z,‖regressionLatentMean s (g z)‖≤A)
    (hB:∀s z,‖regressionScore ε s (g z)‖≤B) (s:ℝ) :
    LipschitzWith (1+2*A*B) (gaussianMeanField μ g ε s) ∧
    (∀y,‖fderiv ℝ (gaussianMeanField μ g ε s) y‖≤(1+2*A*B:ℝ≥0)) ∧
    (∀x y,‖gaussianMeanField μ g ε s y-gaussianMeanField μ g ε s x-
      fderiv ℝ (gaussianMeanField μ g ε s) x (y-x)‖≤
        (6*(A:ℝ)*B^2)*‖y-x‖^2) := by
  have hb:=gaussianMeanRemainder_bounds μ g hg hε A B hA hB s
  have hd:Differentiable ℝ (gaussianMeanField μ g ε s) :=
    ((gaussianMeanField_contDiff 1 μ g hg hε).differentiable (by norm_num)).comp
      (differentiable_const s |>.prodMk differentiable_id)
  have hn(y:E):‖fderiv ℝ (gaussianMeanField μ g ε s) y‖≤(1+2*A*B:ℝ≥0) := by
    rw [gaussianMeanField_spatial_fderiv μ g hg hε s y]
    calc
      _ ≤ ‖regressionBeta s • ContinuousLinearMap.id ℝ E‖+
          ‖fderiv ℝ (gaussianMeanRemainder μ g ε s) y‖ := norm_add_le _ _
      _ ≤ 1+(2*A*B:ℝ≥0) := add_le_add (by
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul (regressionBeta_abs_le_one s) ContinuousLinearMap.norm_id_le
          (norm_nonneg _) zero_le_one).trans_eq (by norm_num)) (hb.2.2.1 y)
      _ = _ := by simp
  refine ⟨?_,hn,?_⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le hd
    intro y
    exact_mod_cast hn y
  · intro x y
    have hl:LipschitzWith (6*A*B^2) (fderiv ℝ (gaussianMeanField μ g ε s)) := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      simpa only [dist_eq_norm,gaussianMeanField_spatial_fderiv μ g hg hε s,
        add_sub_add_left_eq_sub] using hb.2.2.2.dist_le_mul u v
    exact_mod_cast quadratic_remainder_of_lipschitz_fderiv hd hl x y

end PersistencePays
#print axioms PersistencePays.gaussianMeanField_bounds
