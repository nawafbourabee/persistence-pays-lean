import PersistencePays.GaussianWeightedPosterior
import PersistencePays.AffinePosteriorBounds

/-! A linear spatial score bound for the actual compact Gaussian mixture density. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

lemma gaussianFlightDensity_gradient_integral (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) :
    gradient (gaussianFlightDensity μ g ε s) y=
      ∫z,gradient (fun y=>singleFlightDensity ε s y (g z)) y ∂μ := by
  have hproj:ContDiff ℝ 1 (fun p:E×(E×E)=>((s,p.1),p.2)) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  have hn:ContDiff ℝ 1 (fun p:E×(E×E)=>singleFlightDensity ε s p.1 p.2):=
    (singleFlightDensity_contDiff 1 hε).comp hproj
  have hc:Continuous (fun z=>gradient (fun y=>singleFlightDensity ε s y (g z)) y) := by
    simp_rw [singleFlightDensity_gradient hε]
    apply Continuous.smul
    · exact (((singleFlightDensity_contDiff 0 hε).continuous.comp
        (show Continuous (fun z:Z=>((s,y),g z)) from continuous_const.prodMk hg)).div_const _).neg
    · unfold flightResidual latentCenter; fun_prop
  have hi:=hc.integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)
  apply ext_inner_left ℝ
  intro v
  rw [inner_gradient_right]
  have hh:=((innerSL ℝ v).integral_comp_comm hi).symm
  change ⟪v,∫z,gradient (fun y=>singleFlightDensity ε s y (g z)) y ∂μ⟫=
    ∫z,⟪v,gradient (fun y=>singleFlightDensity ε s y (g z)) y⟫ ∂μ at hh
  rw [hh]
  simp only [inner_gradient_right,RCLike.conj_to_real]
  exact compact_mixture_fderiv_apply μ g hg hn y v

lemma gaussianFlightDensity_gradient_formula (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    gradient (gaussianFlightDensity μ g ε s) y=
      gaussianFlightDensity μ g ε s y •
        (-(ε^2*(1+s^2))⁻¹•y+
          affinePosteriorMean μ (fun z=>regressionScore ε s (g z))
            (fun z=>regressionScore ε s (g z)) (fun z=>regressionLogWeight ε s (g z)) y) := by
  rw [gaussianFlightDensity_gradient_integral μ g hg hε.ne']
  have he (z:Z):gradient (fun y=>singleFlightDensity ε s y (g z)) y=
      singleFlightDensity ε s y (g z) •
        (-(ε^2*(1+s^2))⁻¹•y+regressionScore ε s (g z)) := by
    rw [singleFlightDensity_gradient hε.ne']
    unfold flightResidual regressionScore
    simp only [div_eq_mul_inv]
    module
  simp_rw [he]
  rw [gaussian_weighted_posterior μ g hg hε]
  congr 1
  exact affinePosteriorMean_const_add μ _ _ _
    (by unfold regressionScore latentCenter; fun_prop)
    (by unfold regressionScore latentCenter; fun_prop)
    (by unfold regressionLogWeight latentCenter; fun_prop) y _

theorem gaussianFlightDensity_gradient_bound (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) {B:ℝ}
    (hB:∀z,‖regressionScore ε s (g z)‖≤B) (y:E) :
    ‖gradient (gaussianFlightDensity μ g ε s) y‖≤
      gaussianFlightDensity μ g ε s y*((ε^2)⁻¹*‖y‖+B) := by
  have hn:0≤gaussianFlightDensity μ g ε s y:=(gaussianFlightDensity_pos μ g hg hε s y).le
  have hb:=affinePosteriorMean_norm μ (fun z=>regressionScore ε s (g z))
    (fun z=>regressionScore ε s (g z)) (fun z=>regressionLogWeight ε s (g z))
    (show Continuous (fun z=>regressionScore ε s (g z)) by unfold regressionScore latentCenter; fun_prop)
    (show Continuous (fun z=>regressionScore ε s (g z)) by unfold regressionScore latentCenter; fun_prop)
    (show Continuous (fun z=>regressionLogWeight ε s (g z)) by unfold regressionLogWeight latentCenter; fun_prop)
    hB y
  have hc:(ε^2*(1+s^2))⁻¹≤(ε^2)⁻¹ := by
    apply inv_anti₀ (sq_pos_of_ne_zero hε.ne')
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg s)]
  rw [gaussianFlightDensity_gradient_formula μ g hg hε,norm_smul,Real.norm_of_nonneg hn]
  apply mul_le_mul_of_nonneg_left _ hn
  calc
    _≤‖-(ε^2*(1+s^2))⁻¹•y‖+‖affinePosteriorMean μ (fun z=>regressionScore ε s (g z))
      (fun z=>regressionScore ε s (g z)) (fun z=>regressionLogWeight ε s (g z)) y‖:=norm_add_le _ _
    _≤(ε^2)⁻¹*‖y‖+B:=by
      apply add_le_add _ hb
      rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

end PersistencePays
#print axioms PersistencePays.gaussianFlightDensity_gradient_bound
