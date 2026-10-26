import PersistencePays.GaussianQuadraticMGF
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! The exact standard Gaussian kinetic-energy expectation. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_inner_square_integrable (b : E) :
    Integrable (fun x : E => ⟪b, x⟫ ^ 2) (stdGaussian E) := by
  have hi := (innerSL ℝ b).comp_memLp' (IsGaussian.memLp_two_id (μ := stdGaussian E))
  exact hi.integrable_sq

theorem stdGaussian_inner_square (b : E) :
    ∫ x : E, ⟪b, x⟫ ^ 2 ∂stdGaussian E = ‖b‖ ^ 2 := by
  have hv := variance_dual_stdGaussian (innerSL ℝ b)
  rw [variance_of_integral_eq_zero (by fun_prop)
    (integral_strongDual_stdGaussian (innerSL ℝ b)), innerSL_apply_norm] at hv
  exact hv

theorem stdGaussian_norm_square_integrable :
    Integrable (fun x : E => ‖x‖ ^ 2) (stdGaussian E) := by
  exact IsGaussian.memLp_two_id.integrable_norm_pow'

theorem stdGaussian_norm_square :
    ∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E = (Module.finrank ℝ E : ℝ) := by
  simp_rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_right]
  rw [integral_finsetSum _ (fun i _ => stdGaussian_inner_square_integrable _)]
  simp [stdGaussian_inner_square, (stdOrthonormalBasis ℝ E).orthonormal.1]

end PersistencePays
#print axioms PersistencePays.stdGaussian_norm_square
