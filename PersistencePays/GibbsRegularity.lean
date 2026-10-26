import PersistencePays.Assumptions
import PersistencePays.GaussianDensity

/-! Gibbs normalization follows from (A1), without an extra integrability assumption. -/

namespace PersistencePays
noncomputable section
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem shifted_gaussian_radial_integrable {c : ℝ} (hc : 0 < c) (xstar : E) :
    Integrable (fun x : E => Real.exp (-c * ‖x - xstar‖ ^ 2)) volume := by
  exact (measurePreserving_sub_right volume xstar).integrable_comp_of_integrable
    (gaussian_radial_integrable (E := E) hc)

theorem A1.gibbs_density_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x : E) :
    Real.exp (-U x) ≤ Real.exp (-U a.minimizer) *
      Real.exp (-(m / 2) * ‖x - a.minimizer‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [a.quadratic_lower_at_minimizer x]

theorem A1.gibbs_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Integrable (fun x : E => Real.exp (-U x)) volume := by
  have hm := a.m_pos
  have hi := (shifted_gaussian_radial_integrable
    (E := E) (by positivity : 0 < m / 2) a.minimizer).const_mul (Real.exp (-U a.minimizer))
  refine hi.mono' (Real.continuous_exp.comp a.twice_contDiff.continuous.neg).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact a.gibbs_density_bound x

theorem A1.gibbs_normalizer_pos {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    0 < ∫ x : E, Real.exp (-U x) := integral_exp_pos a.gibbs_integrable

theorem A1.gibbs_isProbabilityMeasure {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    IsProbabilityMeasure ((volume : Measure E).tilted (-U)) :=
  isProbabilityMeasure_tilted a.gibbs_integrable

end
end PersistencePays

#print axioms PersistencePays.A1.gibbs_integrable
#print axioms PersistencePays.A1.gibbs_isProbabilityMeasure
