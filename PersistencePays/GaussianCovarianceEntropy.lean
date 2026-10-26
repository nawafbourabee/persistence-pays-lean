import PersistencePays.GaussianCovarianceMGF
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual Gaussian relative entropy controls all centered covariance directions
simultaneously. There is no Gaussian assumption on the tested probability law. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace
variable {S : Type*} [MeasurableSpace S]

lemma scalarCovarianceTest_integrable (μ : Measure S) [IsProbabilityMeasure μ]
    (f : S → ℝ) (hf : MemLp f 2 μ) (g a : ℝ) :
    Integrable (fun x => gaussianCovarianceTest g a (f x)) μ := by
  have hi := hf.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hs : Integrable (fun x => (f x-a)^2) μ := by
    simpa only [Pi.sub_apply] using (hf.sub (memLp_const a)).integrable_sq
  exact (((hs.const_mul ((1-g)/4)).add (hi.const_mul a)).sub
    (integrable_const (a^2/2))).add (integrable_const (Real.log ((1+g)/2)/2))

lemma scalarCovarianceTest_expectation (μ : Measure S) [IsProbabilityMeasure μ]
    (f : S → ℝ) (hf : MemLp f 2 μ) (g a : ℝ) (ha : ∫ x,f x ∂μ=a) :
    (∫ x,gaussianCovarianceTest g a (f x) ∂μ) =
      (1-g)/4*(∫ x,(f x-a)^2 ∂μ)+a^2/2+Real.log ((1+g)/2)/2 := by
  have hi := hf.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hs : Integrable (fun x => (f x-a)^2) μ := by
    simpa only [Pi.sub_apply] using (hf.sub (memLp_const a)).integrable_sq
  unfold gaussianCovarianceTest
  rw [integral_add (f:=fun x => (1-g)/4*(f x-a)^2+a*f x-a^2/2)
      (g:=fun _ => Real.log ((1+g)/2)/2) (((hs.const_mul ((1-g)/4)).add (hi.const_mul a)).sub
      (integrable_const (a^2/2))) (integrable_const _),
    integral_sub (f:=fun x => (1-g)/4*(f x-a)^2+a*f x) (g:=fun _ => a^2/2)
      ((hs.const_mul ((1-g)/4)).add (hi.const_mul a)) (integrable_const _),
    integral_add (f:=fun x => (1-g)/4*(f x-a)^2) (g:=fun x => a*f x)
      (hs.const_mul ((1-g)/4)) (hi.const_mul a),
    integral_const_mul,integral_const_mul,ha]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  ring

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma inner_memLp_two (μ : Measure E) (hm : MemLp id 2 μ) (v : E) :
    MemLp (fun x => ⟪v,x⟫_ℝ) 2 μ := by
  simpa only [Function.comp_def,id_eq,innerSL_apply_apply] using (innerSL ℝ v).comp_memLp' hm

lemma inner_mean (μ : Measure E) [IsProbabilityMeasure μ] (hm : MemLp id 2 μ) (v : E) :
    (∫ x, ⟪v,x⟫_ℝ ∂μ) = ⟪v,(∫ x,x ∂μ)⟫_ℝ := by
  simpa only [innerSL_apply_apply,id_eq] using
    (innerSL ℝ v).integral_comp_comm (hm.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2))

/-- The exact Gaussian entropy-covariance inequality in any orthonormal basis.
The centered squares are the actual diagonal entries of the covariance. -/
theorem basis_covariance_entropy (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ) (hg : ∀ i,0<g i) :
    let a := ∫ x,x ∂μ
    (∑ i,(1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ))/4 ≤
      (klDiv μ (stdGaussian E)).toReal-‖a‖^2/2-(∑ i,Real.log ((1+g i)/2))/2 := by
  dsimp only
  let a := ∫ x,x ∂μ
  have hi (i : ι) : Integrable (fun x => gaussianCovarianceTest (g i) ⟪b i,a⟫_ℝ ⟪b i,x⟫_ℝ) μ :=
    scalarCovarianceTest_integrable μ _ (inner_memLp_two μ hm (b i)) _ _
  have hF : Integrable (basisCovarianceTest b g a) μ := integrable_finsetSum _ (fun i _ => hi i)
  have hb := integral_le_klDiv_of_exp_integral_le_one μ (stdGaussian E) hD
    (basisCovarianceTest b g a) hF (basis_covariance_test_integrable b g hg a)
    (basis_covariance_test_normalized b g hg a).le
  unfold basisCovarianceTest at hb
  rw [integral_finsetSum _ (fun i _ => hi i)] at hb
  have he (i : ι) := scalarCovarianceTest_expectation μ (fun x => ⟪b i,x⟫_ℝ)
    (inner_memLp_two μ hm (b i)) (g i) ⟪b i,a⟫_ℝ (inner_mean μ hm (b i))
  simp_rw [he] at hb
  have hr (i : ι) : (1-g i)/4*(∫ x,(⟪b i,x⟫_ℝ-⟪b i,a⟫_ℝ)^2 ∂μ) =
      ((1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ))/4 := by
    simp only [inner_sub_right]
    ring
  simp_rw [hr] at hb
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_div,
    ← Finset.sum_div,← Finset.sum_div,b.sum_sq_inner_right] at hb
  change (∑ i,(1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ))/4 ≤ _
  linarith

/-- The scalar arithmetic-geometric mean step, with exact logarithmic constants. -/
theorem scalar_log_covariance_bound (g : ℝ) (hg : 0<g) :
    -2*Real.log ((1+g)/2) ≤ -Real.log g := by
  have hp : 0<(1+g)/2 := by linarith
  have hsq : g ≤ ((1+g)/2)^2 := by nlinarith [sq_nonneg (g-1)]
  have hl := Real.log_le_log hg hsq
  rw [Real.log_pow] at hl
  norm_num at hl
  linarith

/-- The simplified covariance bound used after Gaussian duality in Appendix A. -/
theorem basis_covariance_entropy_log (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ) (hg : ∀ i,0<g i) :
    let a := ∫ x,x ∂μ
    (∑ i,(1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ)) ≤
      4*(klDiv μ (stdGaussian E)).toReal-2*‖a‖^2-(∑ i,Real.log (g i)) := by
  have hb := basis_covariance_entropy μ hm hD b g hg
  dsimp only at hb ⊢
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => scalar_log_covariance_bound (g i) (hg i))
  simp only [Finset.sum_neg_distrib,← Finset.mul_sum] at hl
  linarith

end PersistencePays
#print axioms PersistencePays.basis_covariance_entropy
#print axioms PersistencePays.basis_covariance_entropy_log
