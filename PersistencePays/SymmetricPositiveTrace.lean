import PersistencePays.SymmetricLogDet
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Spectral bounds for positive semidefinite operators used by the matrix
distributional divergence argument. The second factor in the trace-product
bound need only have nonnegative quadratic form, not be symmetric. -/
noncomputable section
namespace PersistencePays
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem positive_trace_nonneg (G:E→ₗ[ℝ]E) (hG:G.IsPositive) :
    0≤LinearMap.trace ℝ E G := by
  classical
  rw [LinearMap.trace_eq_sum_inner G (stdOrthonormalBasis ℝ E)]
  exact Finset.sum_nonneg (fun i _ => hG.inner_nonneg_right _)

theorem positive_trace_comp_nonneg (S G:E→ₗ[ℝ]E) (hS:S.IsPositive)
    (hG:∀ v:E,0≤⟪v,G v⟫_ℝ) : 0≤LinearMap.trace ℝ E (S.comp G) := by
  classical
  let b := hS.isSymmetric.eigenvectorBasis rfl
  rw [LinearMap.trace_comp_comm',LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_nonneg
  intro i _
  change 0≤⟪b i,G (S (b i))⟫_ℝ
  rw [hS.isSymmetric.apply_eigenvectorBasis]
  simp only [map_smul,inner_smul_right,RCLike.ofReal_real_eq_id,id_eq]
  exact mul_nonneg (hS.nonneg_eigenvalues rfl i) (hG (b i))

theorem positive_trace_comp_mono (S G H:E→ₗ[ℝ]E) (hS:S.IsPositive)
    (hGH:∀ v:E,⟪v,G v⟫_ℝ≤⟪v,H v⟫_ℝ) :
    LinearMap.trace ℝ E (S.comp G)≤LinearMap.trace ℝ E (S.comp H) := by
  have hh := positive_trace_comp_nonneg S (H-G) hS (fun v => by
    simpa only [LinearMap.sub_apply,inner_sub_right,sub_nonneg] using hGH v)
  rw [LinearMap.comp_sub,map_sub] at hh
  linarith

theorem positive_quadratic_le_trace (G:E→ₗ[ℝ]E) (hG:G.IsPositive) (x:E) :
    ⟪G x,x⟫_ℝ≤LinearMap.trace ℝ E G*‖x‖^2 := by
  classical
  let b := hG.isSymmetric.eigenvectorBasis rfl
  let lam := hG.isSymmetric.eigenvalues rfl
  have hlam (i:Fin (Module.finrank ℝ E)) : lam i≤LinearMap.trace ℝ E G := by
    rw [hG.isSymmetric.trace_eq_sum_eigenvalues rfl]
    exact Finset.single_le_sum (fun j _ => hG.nonneg_eigenvalues rfl j) (Finset.mem_univ i)
  have hc (i:Fin (Module.finrank ℝ E)) : ⟪b i,G x⟫_ℝ=lam i*⟪b i,x⟫_ℝ := by
    simpa only [b,lam,OrthonormalBasis.repr_apply_apply,RCLike.ofReal_real_eq_id,id_eq]
      using hG.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i
  have he : ⟪G x,x⟫_ℝ=∑ i,lam i*⟪b i,x⟫_ℝ^2 := by
    rw [real_inner_comm,← b.sum_inner_mul_inner x (G x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc,real_inner_comm x (b i)]
    ring
  rw [he,← b.sum_sq_inner_right x,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hlam i) (sq_nonneg _))

theorem positive_norm_le_trace (G:E→L[ℝ]E) (hG:G.toLinearMap.IsPositive) :
    ‖G‖≤LinearMap.trace ℝ E G.toLinearMap := by
  rw [G.norm_eq_iSup_rayleighQuotient hG.isSymmetric]
  apply ciSup_le
  intro x
  have ht := positive_trace_nonneg G.toLinearMap hG
  have hp : 0 ≤ ⟪G x,x⟫_ℝ := hG.inner_nonneg_left x
  have hb : ⟪G x,x⟫_ℝ ≤ LinearMap.trace ℝ E G.toLinearMap * ‖x‖^2 :=
    positive_quadratic_le_trace G.toLinearMap hG x
  by_cases hx:x=0
  · simp [hx,ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf,ht]
  · have hnorm:0<‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    change |⟪G x,x⟫_ℝ /‖x‖^2|≤_
    rw [abs_of_nonneg (div_nonneg hp hnorm.le)]
    exact (div_le_iff₀ hnorm).mpr hb

end PersistencePays
#print axioms PersistencePays.positive_trace_comp_nonneg
#print axioms PersistencePays.positive_norm_le_trace
