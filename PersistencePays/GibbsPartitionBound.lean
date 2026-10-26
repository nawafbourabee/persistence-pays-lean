import PersistencePays.GibbsRegularity
import PersistencePays.PhaseGibbsDensity

/-! Explicit Gaussian upper bound for the position partition function under A1. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.gibbs_normalizer_le {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    (∫ x : E, Real.exp (-U x)) ≤ Real.exp (-U a.minimizer) *
      (2 * Real.pi / m) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  have hm : 0 < m / 2 := by linarith [a.m_pos]
  have hi := shifted_gaussian_radial_integrable (E := E) hm a.minimizer
  have hb := integral_mono a.gibbs_integrable
    (hi.const_mul (Real.exp (-U a.minimizer))) a.gibbs_density_bound
  rw [integral_const_mul] at hb
  have ht : (∫ x : E, Real.exp (-(m / 2) * ‖x - a.minimizer‖ ^ 2)) =
      (∫ x : E, Real.exp (-(m / 2) * ‖x‖ ^ 2)) :=
    (measurePreserving_sub_right volume a.minimizer).integral_comp
      (show MeasurableEmbedding (fun x : E => x - a.minimizer) from
        (Homeomorph.subRight a.minimizer).measurableEmbedding)
      (fun x : E => Real.exp (-(m / 2) * ‖x‖ ^ 2))
  rw [ht, GaussianFourier.integral_rexp_neg_mul_sq_norm hm] at hb
  convert hb using 1 <;> congr 2 <;> field_simp <;> ring

theorem A1.log_gibbs_normalizer_le {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Real.log (∫ x : E, Real.exp (-U x)) ≤ -U a.minimizer +
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (2 * Real.pi / m) := by
  have hm := a.m_pos
  have hb := Real.log_le_log a.gibbs_normalizer_pos a.gibbs_normalizer_le
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_rpow (by positivity)] at hb
  exact hb

end PersistencePays
#print axioms PersistencePays.A1.gibbs_normalizer_le
#print axioms PersistencePays.A1.log_gibbs_normalizer_le
