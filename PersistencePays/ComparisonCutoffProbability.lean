import PersistencePays.ComparisonFreshPath

/-! The cutoff event is an actual subset of the stopped-path exit. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem comparison_pre_flight_radius {U : E → ℝ} {L h r σ vstar : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hv : 0 ≤ vstar)
    (n : ℕ) (z : E×E) (b : NoiseBlock E (n+2))
    (hb : b ∈ stoppedBlockEvent U (gradient U) h r σ vstar (n+2) z) :
    ‖flightVelocity (gradient U) h (comparisonPreEndpoint (gradient U) h r σ vstar n z b)‖ ≤ vstar := by
  rw [comparison_pre_flight_agree a hstar hzero hL hr hv n z b hb]
  have hb' := hb (n+1) (by omega)
  have ht := a.normalized_noisy_flight_radius hstar hzero hL hr hv _ hb'.1 _ hb'.2
  change ‖lastFlight (gradient U) h r σ (n+1) z b‖ ≤ (0.76:ℝ)*vstar at ht
  linarith

theorem comparison_cutoff_probability {U : E → ℝ} {L h r σ vstar : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hv : 0 ≤ vstar)
    (n : ℕ) (z : E×E) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    (phaseOUKernel r σ ∘ₘ comparisonChainLaw (gradient U) hg h r σ vstar n z)
      {w | vstar < ‖flightVelocity (gradient U) h w‖} ≤
      gaussianBlock (n+2) (stoppedBlockEvent U (gradient U) h r σ vstar (n+2) z)ᶜ := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hV : Measurable (fun w : E×E => ‖flightVelocity (gradient U) h w‖) := by
    unfold flightVelocity
    fun_prop
  rw [← comparison_pre_endpoint_law (gradient U) hg h r σ vstar n z,
    Measure.map_apply (measurable_comparisonPreEndpoint (gradient U) hg h r σ vstar n z)
      (measurableSet_lt measurable_const hV)]
  apply measure_mono
  intro b hb hB
  exact (not_lt_of_ge (comparison_pre_flight_radius a hstar hzero hL hr hv n z b hB)) hb

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.comparison_cutoff_probability
