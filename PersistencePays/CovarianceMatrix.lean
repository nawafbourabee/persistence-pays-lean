import PersistencePays.GaussianCovarianceOperator

/-! The centered quadratic contraction equals the covariance-matrix Frobenius
product used in the manuscript, in every orthonormal coordinate system. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def covarianceMatrix (μ : Measure E) (b : OrthonormalBasis ι ℝ E) : Matrix ι ι ℝ :=
  fun i j => covarianceBilin μ (b i) (b j)

lemma quadratic_toMatrix (K : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E) (z : E) :
    ⟪z,K z⟫_ℝ = ∑ i,∑ j,
      (⟪b i,z⟫_ℝ * ⟪b j,z⟫_ℝ)*(LinearMap.toMatrix b.toBasis b.toBasis K) i j := by
  have hK : K z = ∑ j,⟪b j,z⟫_ℝ • K (b j) := by
    have hh := congrArg K (b.sum_repr' z)
    simpa only [map_sum,map_smul] using hh.symm
  rw [← b.sum_inner_mul_inner z (K z),hK]
  apply Finset.sum_congr rfl
  intro i _
  simp only [inner_sum,inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply,OrthonormalBasis.coe_toBasis,
    real_inner_comm z (b i)]
  ring

theorem covarianceContraction_eq_frobenius (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (K : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E) :
    covarianceContraction μ K =
      Matrix.trace (covarianceMatrix μ b * (LinearMap.toMatrix b.toBasis b.toBasis K).transpose) := by
  let a := ∫ x,x ∂μ
  have hi (i j : ι) : Integrable (fun x =>
      (⟪b i,x-a⟫_ℝ * ⟪b j,x-a⟫_ℝ)*(LinearMap.toMatrix b.toBasis b.toBasis K) i j) μ := by
    have hi := (inner_memLp_two μ hm (b i)).sub (memLp_const ⟪b i,a⟫_ℝ)
    have hj := (inner_memLp_two μ hm (b j)).sub (memLp_const ⟪b j,a⟫_ℝ)
    simpa only [Pi.mul_apply,Pi.sub_apply,inner_sub_right] using
      (hi.integrable_mul hj).mul_const ((LinearMap.toMatrix b.toBasis b.toBasis K) i j)
  unfold covarianceContraction
  simp_rw [quadratic_toMatrix K b]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp only [Matrix.trace,Matrix.mul_apply,Matrix.transpose_apply,covarianceMatrix]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const]
  change (∫ x,⟪b i,x-a⟫_ℝ * ⟪b j,x-a⟫_ℝ ∂μ) *
    (LinearMap.toMatrix b.toBasis b.toBasis K) i j =
    covarianceBilin μ (b i) (b j) * (LinearMap.toMatrix b.toBasis b.toBasis K) i j
  rw [covarianceBilin_apply hm]
  rfl

/-- The exact displayed matrix inequality in Appendix A. -/
theorem covariance_matrix_entropy (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) (b : OrthonormalBasis ι ℝ E) :
    Matrix.trace (covarianceMatrix μ b *
      (LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.id-G)).transpose)/4 ≤
      (klDiv μ (stdGaussian E)).toReal-‖∫ x,x ∂μ‖^2/2-
        Real.log (LinearMap.det ((1/2:ℝ) • (LinearMap.id+G)))/2 := by
  rw [← covarianceContraction_eq_frobenius μ hm]
  exact gaussian_covariance_entropy μ hm hD G hG hpos

theorem covariance_matrix_entropy_logdet (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) (b : OrthonormalBasis ι ℝ E) :
    Matrix.trace (covarianceMatrix μ b *
      (LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.id-G)).transpose) ≤
      4*(klDiv μ (stdGaussian E)).toReal-2*‖∫ x,x ∂μ‖^2-Real.log (LinearMap.det G) := by
  rw [← covarianceContraction_eq_frobenius μ hm]
  exact gaussian_covariance_entropy_logdet μ hm hD G hG hpos

end PersistencePays
#print axioms PersistencePays.covarianceContraction_eq_frobenius
#print axioms PersistencePays.covariance_matrix_entropy_logdet
