import PersistencePays.ProximalPotential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Curvature information retained by the proximal regularization: its
derivative is firmly nonexpansive, and its inverse minus identity is a positive
self-adjoint operator. -/
open Set Filter
open scoped Topology RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem proximal_derivative_firm (f : E → ℝ) (hf : ConvexOn ℝ univ f) {z : E}
    (hz : DifferentiableAt ℝ (proximalMap f hf) z) (v : E) :
    ‖(fderiv ℝ (proximalMap f hf) z) v‖^2 ≤
      ⟪v,(fderiv ℝ (proximalMap f hf) z) v⟫ := by
  let P := proximalMap f hf
  let D := fderiv ℝ P z
  have hd : HasDerivAt (fun t : ℝ => P (z+t•v)) (D v) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => z+t•v) v 0 := by
      have hh := (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id (0:ℝ)).smul_const v)
      change HasDerivAt (fun t : ℝ => z+t•v) (0+(1:ℝ)•v) 0 at hh
      simpa only [zero_add,one_smul] using hh
    have hz' : HasFDerivAt P D (z+(0:ℝ)•v) := by simpa using hz.hasFDerivAt
    exact hz'.comp_hasDerivAt 0 hlin
  have ht : Tendsto (fun t : ℝ => t⁻¹ • (P (z+t•v)-P z)) (𝓝[>] 0) (𝓝 (D v)) := by
    simpa using hd.tendsto_slope_zero_right
  have hineq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖t⁻¹ • (P (z+t•v)-P z)‖^2 ≤ ⟪v,t⁻¹ • (P (z+t•v)-P z)⟫ := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    change 0<t at ht0
    have hh := proximalMap_firm f hf (z+t•v) z
    have he : (z+t•v)-z=t•v := by abel
    rw [he,inner_smul_left] at hh
    change ‖P (z+t•v)-P z‖^2 ≤ t*⟪v,P (z+t•v)-P z⟫ at hh
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht0,mul_pow,
      inner_smul_right]
    have hi : t⁻¹*t=1 := inv_mul_cancel₀ ht0.ne'
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg t⁻¹)
    have hi2 : t⁻¹^2*(t*⟪v,P (z+t•v)-P z⟫)=t⁻¹*⟪v,P (z+t•v)-P z⟫ := by
      calc
        _ = ((t⁻¹*t)*t⁻¹)*⟪v,P (z+t•v)-P z⟫ := by ring
        _ = _ := by rw [hi,one_mul]
    rwa [hi2] at hh'

  exact le_of_tendsto_of_tendsto (ht.norm.pow 2) (tendsto_const_nhds.inner ht) hineq

theorem inverse_proximal_derivative_positive
    (f : E → ℝ) (hf : ConvexOn ℝ univ f) {z : E}
    (hz : DifferentiableAt ℝ (proximalMap f hf) z)
    (hdet : (fderiv ℝ (proximalMap f hf) z).det≠0) :
    let A := (fderiv ℝ (proximalMap f hf) z).toContinuousLinearEquivOfDetNeZero hdet
    ((A.symm : E →L[ℝ] E)-ContinuousLinearMap.id ℝ E).toLinearMap.IsPositive := by
  dsimp only
  let A := (fderiv ℝ (proximalMap f hf) z).toContinuousLinearEquivOfDetNeZero hdet
  have hsym : A.toLinearEquiv.IsSymmetric := by
    intro u v
    change ⟪A u,v⟫=⟪u,A v⟫
    have hh := proximal_derivative_symmetric f hf hz u v
    change ⟪(fderiv ℝ (proximalMap f hf) z) u,v⟫=
      ⟪u,(fderiv ℝ (proximalMap f hf) z) v⟫ at hh
    simpa only [A,ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] using hh
  refine ⟨hsym.toLinearMap_symm.sub (show (LinearMap.id : E →ₗ[ℝ] E).IsSymmetric from fun _ _ => rfl),?_⟩
  intro v
  have hh := proximal_derivative_firm f hf hz (A.symm v)
  have he : (fderiv ℝ (proximalMap f hf) z) (A.symm v)=v := by
    change A (A.symm v)=v
    exact A.apply_symm_apply v
  rw [he] at hh
  change 0 ≤ ⟪A.symm v-v,v⟫
  rw [inner_sub_left,real_inner_self_eq_norm_sq]
  nlinarith [real_inner_comm v (A.symm v)]

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.inverse_proximal_derivative_positive
