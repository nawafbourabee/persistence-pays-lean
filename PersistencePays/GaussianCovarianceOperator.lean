import PersistencePays.GaussianCovarianceEntropy

/-! Basis-independent form of Appendix A's fixed-matrix Gaussian duality bound.
The covariance contraction is defined by its actual centered second moment. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def covarianceContraction (μ : Measure E) (K : E →ₗ[ℝ] E) : ℝ :=
  ∫ x, ⟪x-(∫ y,y ∂μ),K (x-(∫ y,y ∂μ))⟫_ℝ ∂μ

lemma covarianceContraction_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure E) [IsProbabilityMeasure μ] (hm : MemLp id 2 μ)
    (G : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ)
    (hcoord : ∀ z i,⟪b i,G z⟫_ℝ=g i*⟪b i,z⟫_ℝ) :
    covarianceContraction μ ((LinearMap.id : E →ₗ[ℝ] E)-G) =
      ∑ i,(1-g i)*(∫ x,⟪b i,x-(∫ y,y ∂μ)⟫_ℝ^2 ∂μ) := by
  have he (z : E) : ⟪z,((LinearMap.id : E →ₗ[ℝ] E)-G) z⟫_ℝ = ∑ i,(1-g i)*⟪b i,z⟫_ℝ^2 := by
    rw [← b.sum_inner_mul_inner z (((LinearMap.id : E →ₗ[ℝ] E)-G) z)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.sub_apply,LinearMap.id_apply,inner_sub_right,hcoord,
      real_inner_comm z (b i)]
    ring
  have hi (i : ι) : Integrable (fun x => (1-g i)*⟪b i,x-(∫ y,y ∂μ)⟫_ℝ^2) μ := by
    have hh := ((inner_memLp_two μ hm (b i)).sub
      (memLp_const ⟪b i,(∫ y,y ∂μ)⟫_ℝ)).integrable_sq
    simpa only [Pi.sub_apply,inner_sub_right] using hh.const_mul (1-g i)
  unfold covarianceContraction
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul]

lemma symmetric_positive_eigenvalues (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) :
    ∀ i,0<hG.eigenvalues rfl i := by
  intro i
  have hh := hpos (hG.eigenvectorBasis rfl i) ((hG.eigenvectorBasis rfl).toBasis.ne_zero i)
  rw [hG.apply_eigenvectorBasis,inner_smul_right] at hh
  simpa using hh

lemma symmetric_average_det (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric) :
    LinearMap.det ((1/2:ℝ) • (LinearMap.id+G)) =
      ∏ i, (1+hG.eigenvalues rfl i)/2 := by
  let b := hG.eigenvectorBasis rfl
  have he : LinearMap.toMatrix b.toBasis b.toBasis ((1/2:ℝ) • (LinearMap.id+G)) =
      Matrix.diagonal (fun i => (1+hG.eigenvalues rfl i)/2) := by
    rw [map_smul,map_add,LinearMap.toMatrix_id]
    have hd := hG.toMatrix_eigenvectorBasis rfl
    change LinearMap.toMatrix b.toBasis b.toBasis G = _ at hd
    rw [hd]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal_apply]
      ring
    · simp [Matrix.diagonal_apply,hij,Matrix.one_apply]
  rw [← LinearMap.det_toMatrix b.toBasis,he,Matrix.det_diagonal]

/-- Gaussian duality for the actual probability law and a positive-definite
self-adjoint operator G. The contraction on the left is Σ:(I−G). -/
theorem gaussian_covariance_entropy (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) :
    covarianceContraction μ ((LinearMap.id : E →ₗ[ℝ] E)-G)/4 ≤
      (klDiv μ (stdGaussian E)).toReal-‖∫ x,x ∂μ‖^2/2-
        Real.log (LinearMap.det ((1/2:ℝ) • (LinearMap.id+G)))/2 := by
  let b := hG.eigenvectorBasis rfl
  let g := hG.eigenvalues rfl
  have hg : ∀ i,0<g i := symmetric_positive_eigenvalues G hG hpos
  have hcoord (z:E) (i:Fin (Module.finrank ℝ E)) : ⟪b i,G z⟫_ℝ=g i*⟪b i,z⟫_ℝ := by
    simpa only [OrthonormalBasis.repr_apply_apply,RCLike.ofReal_real_eq_id,id_eq,b,g] using hG.eigenvectorBasis_apply_self_apply rfl z i
  rw [covarianceContraction_basis μ hm G b g hcoord,symmetric_average_det G hG,
    Real.log_prod (fun i _ => (show 0<(1+g i)/2 by linarith [hg i]).ne')]
  exact basis_covariance_entropy μ hm hD b g hg

/-- The matrix logarithmic inequality, proved by the actual positive spectrum. -/
theorem symmetric_logdet_average_bound (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) :
    -2*Real.log (LinearMap.det ((1/2:ℝ) • (LinearMap.id+G))) ≤ -Real.log (LinearMap.det G) := by
  have hg := symmetric_positive_eigenvalues G hG hpos
  rw [symmetric_average_det G hG,hG.det_eq_prod_eigenvalues rfl]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [
    Real.log_prod (fun i _ => (show 0<(1+hG.eigenvalues rfl i)/2 by linarith [hg i]).ne'),
    Real.log_prod (fun i _ => (hg i).ne')]
  simpa only [Finset.sum_neg_distrib,← Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => scalar_log_covariance_bound _ (hg i))

/-- The exact covariance bound integrated in Appendix A after Gaussian duality. -/
theorem gaussian_covariance_entropy_logdet (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) :
    covarianceContraction μ ((LinearMap.id : E →ₗ[ℝ] E)-G) ≤
      4*(klDiv μ (stdGaussian E)).toReal-2*‖∫ x,x ∂μ‖^2-Real.log (LinearMap.det G) := by
  have hh := gaussian_covariance_entropy μ hm hD G hG hpos
  have hl := symmetric_logdet_average_bound G hG hpos
  linarith

end PersistencePays
#print axioms PersistencePays.gaussian_covariance_entropy
#print axioms PersistencePays.gaussian_covariance_entropy_logdet
