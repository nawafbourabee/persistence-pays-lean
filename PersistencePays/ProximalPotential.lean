import PersistencePays.ConvexSecondRegularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The proximal map is the gradient of its actual convex conjugate potential;
consequently its derivative, wherever it exists, is self-adjoint. -/
open Set Filter Asymptotics
open scoped Topology RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def proximalPotential (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z : E) : ℝ :=
  ⟪z,proximalMap f hf z⟫ - f (proximalMap f hf z) - ‖proximalMap f hf z‖^2/2

lemma proximalPotential_supports (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z : E) :
    Supports (proximalPotential f hf) z (proximalMap f hf z) := by
  intro w
  have hm := (supports_proximal_minimum (proximalMap_supports f hf w) (proximalMap f hf z))
  have hn := sq_nonneg ‖proximalMap f hf z-proximalMap f hf w‖
  have hm0 : proximalObjective f w (proximalMap f hf w) ≤
      proximalObjective f w (proximalMap f hf z) := by linarith
  dsimp [proximalObjective] at hm0
  rw [norm_sub_sq_real,norm_sub_sq_real] at hm0
  dsimp [proximalPotential]
  rw [inner_sub_right]
  nlinarith [real_inner_comm z (proximalMap f hf z),
    real_inner_comm w (proximalMap f hf w),real_inner_comm w (proximalMap f hf z)]

lemma proximalPotential_error (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z w : E) :
    |proximalPotential f hf w-proximalPotential f hf z-⟪proximalMap f hf z,w-z⟫|
      ≤ ‖w-z‖^2 := by
  have h1 := proximalPotential_supports f hf z w
  have h2 := proximalPotential_supports f hf w z
  have h3 := real_inner_le_norm (proximalMap f hf w-proximalMap f hf z) (w-z)
  have h4 := (proximalMap_lipschitz f hf).dist_le_mul w z
  simp only [NNReal.coe_one,one_mul,dist_eq_norm] at h4
  have hi : ⟪proximalMap f hf w,z-w⟫ = -⟪proximalMap f hf w,w-z⟫ := by
    simp only [inner_sub_right]
    ring
  rw [hi] at h2
  rw [inner_sub_left] at h3
  rw [abs_of_nonneg (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right h4 (norm_nonneg (w-z))]

theorem proximalPotential_hasGradientAt (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z : E) :
    HasGradientAt (proximalPotential f hf) (proximalMap f hf z) z := by
  apply hasGradientAt_iff_isLittleO.mpr
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds z hε] with w hw
  rw [Real.norm_eq_abs]
  apply (proximalPotential_error f hf z w).trans
  have hh : ‖w-z‖<ε := by simpa [Metric.mem_ball,dist_eq_norm] using hw
  nlinarith [norm_nonneg (w-z)]

theorem proximal_derivative_symmetric (f : E → ℝ) (hf : ConvexOn ℝ univ f) {z : E}
    (hz : DifferentiableAt ℝ (proximalMap f hf) z) :
    (fderiv ℝ (proximalMap f hf) z).toLinearMap.IsSymmetric := by
  let J : E →L[ℝ] (E →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  have hd : HasFDerivAt (fun w => J (proximalMap f hf w))
      (J.comp (fderiv ℝ (proximalMap f hf) z)) z :=
    J.hasFDerivAt.comp z hz.hasFDerivAt
  intro v w
  have hh := second_derivative_symmetric
    (fun y => (proximalPotential_hasGradientAt f hf y).hasFDerivAt) hd v w
  change ⟪(fderiv ℝ (proximalMap f hf) z) v,w⟫ =
    ⟪v,(fderiv ℝ (proximalMap f hf) z) w⟫
  simpa [J,real_inner_comm] using hh

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.proximal_derivative_symmetric
