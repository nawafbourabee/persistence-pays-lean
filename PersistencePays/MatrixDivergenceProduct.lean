import PersistencePays.CompactMatrixIBP
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Exact product rule for the matrix divergence used in Appendix A. -/
noncomputable section
namespace PersistencePays
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem matrixDivergence_smul {χ : E → ℝ} {S : E → E →L[ℝ] E}
    (hχ : ContDiff ℝ 1 χ) (hS : ContDiff ℝ 1 S) (x : E) :
    matrixDivergence (fun y => χ y • S y) x =
      χ x • matrixDivergence S x + S x (gradient χ x) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hd := (hχ.differentiable one_ne_zero x).hasFDerivAt.smul
    (hS.differentiable one_ne_zero x).hasFDerivAt
  have he (v:E) : (fderiv ℝ (fun y => χ y • S y) x v) v =
      (fderiv ℝ χ x v) • S x v + χ x • (fderiv ℝ S x v) v := by
    change (fderiv ℝ (χ • S) x v) v = _
    rw [hd.fderiv]
    simp [add_comm]
  have hsum : (∑ i, (fderiv ℝ χ x (b i)) • S x (b i)) = S x (gradient χ x) := by
    conv_rhs => rw [← b.sum_repr (gradient χ x),map_sum]
    simp only [map_smul,b.repr_apply_apply,inner_gradient_right,RCLike.conj_to_real]
  simp only [matrixDivergence,he,Finset.sum_add_distrib,← Finset.smul_sum]
  change (∑ i, (fderiv ℝ χ x (b i)) • S x (b i)) +
    χ x • (∑ i, (fderiv ℝ S x (b i)) (b i)) = _
  rw [hsum]
  exact add_comm _ _

end PersistencePays
#print axioms PersistencePays.matrixDivergence_smul
