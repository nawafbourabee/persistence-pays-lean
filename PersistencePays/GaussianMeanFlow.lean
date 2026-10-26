import PersistencePays.GaussianMeanBounds

/-! Actual classical local flows of the Gaussian-mixture conditional mean.
The pushforward law is supplied separately by continuity and momentum PDEs. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped InnerProductSpace NNReal
universe u
variable {E Z:Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem gaussianDilation_derivative (s:ℝ) :
    HasDerivAt (fun t:ℝ=>Real.sqrt (1+t^2))
      (regressionBeta s*Real.sqrt (1+s^2)) s := by
  have hd:0<1+s^2 := by positivity
  have hs:0<Real.sqrt (1+s^2) := Real.sqrt_pos.mpr hd
  have hh:=(((hasDerivAt_id s).pow 2).const_add 1).sqrt hd.ne'
  convert hh using 1
  · rfl
  · unfold regressionBeta
    dsimp
    field_simp
    rw [Real.sq_sqrt hd.le]

theorem gaussianMeanField_trajectory (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (A B:ℝ≥0)
    (hA:∀s z,‖regressionLatentMean s (g z)‖≤A)
    (hB:∀s z,‖regressionScore ε s (g z)‖≤B)
    {a b:ℝ} (τ:Icc a b) (x:E) :
    ∃X:ℝ→E,X τ=x ∧∀t∈Icc a b,HasDerivWithinAt X
      (gaussianMeanField μ g ε t (X t)) (Icc a b) t := by
  apply dilated_bounded_field_trajectory (bfield:=gaussianMeanRemainder μ g ε)
    (c:=fun t=>Real.sqrt (1+t^2)) (β:=regressionBeta) τ A (2*A*B)
  · exact Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))
  · intro s
    apply (Real.le_sqrt (by norm_num : (0:ℝ)≤1) (by positivity)).mpr
    nlinarith [sq_nonneg s]
  · exact gaussianDilation_derivative
  · exact (gaussianMeanRemainder_contDiff 0 μ g hg hε).continuous
  · intro s _
    exact (gaussianMeanRemainder_bounds μ g hg hε A B hA hB s).2.1
  · intro s _
    exact (gaussianMeanRemainder_bounds μ g hg hε A B hA hB s).1

theorem gaussianMeanField_variational_flow (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (A B:ℝ≥0)
    (hA:∀s z,‖regressionLatentMean s (g z)‖≤A)
    (hB:∀s z,‖regressionScore ε s (g z)‖≤B)
    {a b:ℝ} (hab:a≤b) (ht:2*(1+2*(A:ℝ)*B)*(b-a)≤1) :
    Nonempty (VariationalFlow E (gaussianMeanField μ g ε)
      (fun t y=>fderiv ℝ (gaussianMeanField μ g ε t) y) a b) := by
  apply variational_flow_exists (K:=1+2*A*B) (M:=6*(A:ℝ)*B^2) hab (by positivity)
  · intro t _
    exact (gaussianMeanField_bounds μ g hg hε A B hA hB t).1
  · exact spatial_fderiv_continuous (gaussianMeanField_contDiff 1 μ g hg hε)
  · intro t ht x
    exact (((gaussianMeanField_contDiff 1 μ g hg hε).differentiable (by norm_num)).comp
      (differentiable_const t |>.prodMk differentiable_id) x).hasFDerivAt
  · intro t _
    exact (gaussianMeanField_bounds μ g hg hε A B hA hB t).2.1
  · intro t _ y z
    exact (gaussianMeanField_bounds μ g hg hε A B hA hB t).2.2 z y
  · exact gaussianMeanField_trajectory μ g hg hε A B hA hB
  · exact_mod_cast ht

end PersistencePays
#print axioms PersistencePays.gaussianMeanField_variational_flow
