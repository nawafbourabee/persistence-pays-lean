import PersistencePays.GaussianQuadraticMGF
import PersistencePays.Pinsker
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Exact normalized Gaussian quadratic tests used for the covariance term in
Appendix A. The mean is included in the test, avoiding an assumed centering law. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace

lemma stdGaussian_real : stdGaussian ℝ = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian,charFun_gaussianReal]
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, zero_add, one_mul,
    NNReal.coe_one, Real.norm_eq_abs]
  congr 1
  rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  norm_num
  ring

def gaussianCovarianceTest (g a x : ℝ) : ℝ :=
  (1-g)/4*(x-a)^2+a*x-a^2/2+Real.log ((1+g)/2)/2

theorem gaussianCovarianceTest_expand (g a x : ℝ) :
    gaussianCovarianceTest g a x =
      ((1+g)*a/2)*x+((1-g)/2)/2*x^2+
        (-(1+g)*a^2/4+Real.log ((1+g)/2)/2) := by
  unfold gaussianCovarianceTest
  ring

theorem gaussianCovarianceTest_exp (g a x : ℝ) :
    Real.exp (gaussianCovarianceTest g a x) =
      Real.exp (⟪((1+g)*a/2 : ℝ),x⟫_ℝ+((1-g)/2)/2*‖x‖^2)*
        Real.exp (-(1+g)*a^2/4+Real.log ((1+g)/2)/2) := by
  rw [gaussianCovarianceTest_expand,Real.exp_add]
  simp only [Real.norm_eq_abs,sq_abs,RCLike.inner_apply,conj_trivial]
  congr 2
  ring

theorem scalar_covariance_test_integrable (g a : ℝ) (hg : 0<g) :
    Integrable (fun x => Real.exp (gaussianCovarianceTest g a x)) (gaussianReal 0 1) := by
  rw [← stdGaussian_real]
  simp_rw [gaussianCovarianceTest_exp]
  exact (stdGaussian_quadratic_exp_integrable (E:=ℝ) ((1-g)/2)
    (by linarith) ((1+g)*a/2)).mul_const _

theorem scalar_covariance_test_normalized (g a : ℝ) (hg : 0<g) :
    (∫ x, Real.exp (gaussianCovarianceTest g a x) ∂gaussianReal 0 1)=1 := by
  rw [← stdGaussian_real]
  simp_rw [gaussianCovarianceTest_exp]
  rw [integral_mul_const,stdGaussian_quadratic_mgf_exp _ (by linarith),← Real.exp_add]
  have hd : 1-(1-g)/2=(1+g)/2 := by ring
  have hgne : 1+g ≠ 0 := by linarith
  rw [hd]
  norm_num only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs, sq_abs]
  convert Real.exp_zero using 1
  congr 1
  field_simp
  ring

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def basisCovarianceTest (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ) (a x : E) : ℝ :=
  ∑ i, gaussianCovarianceTest (g i) ⟪b i,a⟫_ℝ ⟪b i,x⟫_ℝ

theorem basisCovarianceTest_measurable (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ) (a : E) :
    Measurable (basisCovarianceTest b g a) := by
  unfold basisCovarianceTest gaussianCovarianceTest
  fun_prop

theorem basisCovarianceTest_reconstruct (b : OrthonormalBasis ι ℝ E)
    (g : ι → ℝ) (a : E) (x : ι → ℝ) :
    Real.exp (basisCovarianceTest b g a (∑ i, x i • b i)) =
      ∏ i, Real.exp (gaussianCovarianceTest (g i) ⟪b i,a⟫_ℝ (x i)) := by
  unfold basisCovarianceTest
  rw [Real.exp_sum]
  congr 1
  funext i
  congr 2
  simp [inner_sum,inner_smul_right,b.orthonormal.inner_right_fintype]

theorem basis_covariance_test_integrable (b : OrthonormalBasis ι ℝ E)
    (g : ι → ℝ) (hg : ∀ i,0<g i) (a : E) :
    Integrable (fun x => Real.exp (basisCovarianceTest b g a x)) (stdGaussian E) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  apply (integrable_map_measure ((basisCovarianceTest_measurable b g a).exp.aestronglyMeasurable)
    (show Measurable (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).aemeasurable).mpr
  simp_rw [Function.comp_def,basisCovarianceTest_reconstruct]
  exact Integrable.fintype_prod (fun i => scalar_covariance_test_integrable (g i) _ (hg i))

theorem basis_covariance_test_normalized (b : OrthonormalBasis ι ℝ E)
    (g : ι → ℝ) (hg : ∀ i,0<g i) (a : E) :
    (∫ x, Real.exp (basisCovarianceTest b g a x) ∂stdGaussian E)=1 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,integral_map
    (show Measurable (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).aemeasurable
    ((basisCovarianceTest_measurable b g a).exp.aestronglyMeasurable)]
  simp_rw [basisCovarianceTest_reconstruct]
  rw [integral_fintype_prod_eq_prod (fun (i : ι) (x : ℝ) =>
    Real.exp (gaussianCovarianceTest (g i) ⟪b i,a⟫_ℝ x))]
  simp_rw [scalar_covariance_test_normalized _ _ (hg _)]
  simp

end PersistencePays
#print axioms PersistencePays.basis_covariance_test_normalized
