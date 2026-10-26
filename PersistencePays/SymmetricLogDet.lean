import PersistencePays.GaussianCovarianceOperator
import Mathlib.LinearAlgebra.Trace

/-! The sharp logarithmic determinant versus trace inequality for an actual
positive-definite symmetric operator, proved from its spectral decomposition. -/
noncomputable section
namespace PersistencePays
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem symmetric_trace_eq_sum_eigenvalues (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric) :
    LinearMap.trace ℝ E G = ∑ i, hG.eigenvalues rfl i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (hG.eigenvectorBasis rfl).toBasis,
    hG.toMatrix_eigenvectorBasis rfl,Matrix.trace_diagonal]
  simp only [RCLike.ofReal_real_eq_id,Function.comp_apply,id_eq]

theorem symmetric_positive_det (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x≠0 → 0<⟪x,G x⟫_ℝ) : 0<LinearMap.det G := by
  classical
  rw [hG.det_eq_prod_eigenvalues rfl]
  simp only [RCLike.ofReal_real_eq_id,Function.comp_apply,id_eq]
  exact Finset.prod_pos (fun i _ => symmetric_positive_eigenvalues G hG hpos i)

theorem symmetric_logdet_le_trace (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x≠0 → 0<⟪x,G x⟫_ℝ) :
    Real.log (LinearMap.det G) ≤ LinearMap.trace ℝ E G-(Module.finrank ℝ E : ℝ) := by
  classical
  have hg := symmetric_positive_eigenvalues G hG hpos
  rw [hG.det_eq_prod_eigenvalues rfl]
  simp only [RCLike.ofReal_real_eq_id,Function.comp_apply,id_eq]
  rw [Real.log_prod (fun i _ => (hg i).ne'),symmetric_trace_eq_sum_eigenvalues G hG]
  have hh := Finset.sum_le_sum (s:=Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => Real.log_le_sub_one_of_pos (hg i))
  simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] using hh

theorem symmetric_logabsdet_le_trace (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x≠0 → 0<⟪x,G x⟫_ℝ) :
    Real.log |LinearMap.det G| ≤ LinearMap.trace ℝ E G-(Module.finrank ℝ E : ℝ) := by
  rw [abs_of_pos (symmetric_positive_det G hG hpos)]
  exact symmetric_logdet_le_trace G hG hpos

end PersistencePays
#print axioms PersistencePays.symmetric_logdet_le_trace
