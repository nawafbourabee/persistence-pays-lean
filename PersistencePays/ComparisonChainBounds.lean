import PersistencePays.ComparisonPath
import PersistencePays.ConditioningEntropy

/-! Actual comparison-chain consequences of the finite Gaussian path law. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- One unadjusted step from the point, followed by n comparison steps. -/
def comparisonChainLaw (g : E → E) (hg : Measurable g) (h r σ vstar : ℝ)
    (n : ℕ) (z : E×E) : Measure (E×E) :=
  (iterateKernel (gaussianSandwichKernel (comparisonVerlet g h vstar)
    (comparisonVerlet_measurePreserving g hg h vstar).measurable r σ) n ∘ₖ
      unadjustedStepKernel g hg h r σ) z

instance comparisonChainLaw_probability (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    IsProbabilityMeasure (comparisonChainLaw g hg h r σ vstar n z) := by
  unfold comparisonChainLaw
  infer_instance

theorem comparisonChainLaw_finite_moments {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    MemLp id p (comparisonChainLaw (gradient U) hg h r σ vstar n z) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hm := unadjusted_kernel_finite_moments a h r σ 1 z p hp
  rw [unadjustedEpochKernel_eq_iterate] at hm
  simp only [iterateKernel,Kernel.comp_id] at hm
  exact a.comparison_iterates_memLp (unadjustedStepKernel (gradient U) hg h r σ z)
    p hp hm h vstar r σ n

/-- Finite Gibbs entropy is proved from a point-mass start, rather than imposed
as an assumption on the initial distribution. -/
theorem comparisonChainLaw_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ vstar : ℝ) (hh : 0<h) (hσ : 0<σ) (hnorm : r^2+σ^2=1)
    (n : ℕ) (z : E×E) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    klDiv (comparisonChainLaw (gradient U) hg h r σ vstar n z) (phaseGibbs U) ≠ ∞ := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hm := unadjusted_kernel_finite_moments a h r σ 1 z 2 (by norm_num)
  rw [unadjustedEpochKernel_eq_iterate] at hm
  simp only [iterateKernel,Kernel.comp_id] at hm
  exact a.comparison_entropy_iterates (unadjustedStepKernel (gradient U) hg h r σ z)
    h vstar r σ hnorm hm (a.unadjusted_step_entropy_finite h r σ hh hσ z) n

/-- The finite conditional Gaussian entropy used in Lemma 5.8 is therefore
available for the actual comparison chain after every positive number of steps. -/
theorem comparisonChainLaw_velocity_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ vstar : ℝ) (hh : 0<h) (hσ : 0<σ) (hnorm : r^2+σ^2=1)
    (n : ℕ) (z : E×E) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    conditionalGaussianEntropy (comparisonChainLaw (gradient U) hg h r σ vstar n z)
      (stdGaussian E) 0 ≠ ∞ := by
  dsimp only
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
  exact conditional_entropy_finite_of_full _ (positionGibbs U) (stdGaussian E)
    (comparisonChainLaw_entropy_finite a h r σ vstar hh hσ hnorm n z)

/-- Quantitative comparison error for the actual chain, combining (5.2) with
the proved Gaussian finite-path exit estimate. -/
theorem comparisonChainLaw_TV_bound
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer=0) (hzero : U 0=0)
    (hh : 0≤h) (hL : h^2*L ≤ 1/64) (hv : 0≤vstar) (hLH : 0≤LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hd : 4*(Module.finrank ℝ E : ℝ) ≤ vstar^2)
    (hR : 0≤R) (z : E×E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    probabilityTV (unadjustedEpochKernel (gradient U) hg h r σ (n+1) z)
      (comparisonChainLaw (gradient U) hg h r σ vstar n z) ≤
      2*((n+1 : ℕ) : ℝ≥0∞)*
        ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-Q0))) := by
  dsimp only
  have hr : (Real.exp (-h))^2 ≤ 1 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  exact (comparison_chain_TV_bound a hstar hzero hL hr hv n z).trans
    (stopped_path_exit_bound_simple a a2 hstar hzero hh hL hv hLH hscale hd hR z hz (n+1))

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.comparisonChainLaw_entropy_finite
#print axioms PersistencePays.OBABOPath.comparisonChainLaw_velocity_entropy_finite
#print axioms PersistencePays.OBABOPath.comparisonChainLaw_TV_bound
