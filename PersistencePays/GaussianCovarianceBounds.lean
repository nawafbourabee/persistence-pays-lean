import PersistencePays.PosteriorCovarianceBounds

/-! Specialization of the uniform posterior covariance estimates to the actual
Gaussian-regression law, valid at every spatial point and every time. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped InnerProductSpace NNReal
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem gaussianRegressionCovariance_bounds (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (A B:ℝ≥0)
    (hA:∀s z,‖regressionLatentMean s (g z)‖≤A)
    (hB:∀s z,‖regressionScore ε s (g z)‖≤B) (s y) :
    ‖gaussianRegressionCovariance μ g ε s y‖≤2*(A:ℝ)^2+ε^2 ∧
    ‖fderiv ℝ (gaussianRegressionCovariance μ g ε s) y‖≤6*(A:ℝ)^2*B := by
  have hF:Continuous (fun z=>regressionLatentMean s (g z)) :=
    (regressionLatentMean_contDiff 0).continuous.comp (continuous_const.prodMk hg)
  have hH:Continuous (fun z=>regressionScore ε s (g z)) :=
    (regressionScore_contDiff 0 hε).continuous.comp (continuous_const.prodMk hg)
  have hk:Continuous (fun z=>regressionLogWeight ε s (g z)) :=
    (regressionLogWeight_contDiff 0 hε).continuous.comp (continuous_const.prodMk hg)
  refine ⟨?_,affinePosteriorCovariance_fderiv_bound μ _ _ _ _ hF hH hk A B (hA s) (hB s) y⟩
  have hb:=affinePosteriorCovariance_norm μ _ _ _ (ε^2/(1+s^2)) hF hH hk A.property (hA s) y
  apply hb.trans
  apply add_le_add le_rfl
  rw [abs_of_nonneg (by positivity)]
  exact div_le_self (sq_nonneg ε) (by nlinarith [sq_nonneg s])

end PersistencePays
#print axioms PersistencePays.gaussianRegressionCovariance_bounds
