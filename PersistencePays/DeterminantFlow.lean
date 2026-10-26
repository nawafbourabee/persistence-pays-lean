import PersistencePays.VariationalFlow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Trace

/-! Jacobi's determinant formula for an actual variational trajectory,
proved by differentiation of the determinant's multilinear row map. -/
noncomputable section
namespace PersistencePays
open scoped BigOperators
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _:ι=>ι→ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

theorem determinantMultilinear_linearDeriv (J A:Matrix ι ι ℝ) :
    (determinantMultilinear (ι:=ι)).linearDeriv J (A*J)=Matrix.trace A*Matrix.det J := by
  change ((determinantMultilinear (ι:=ι)).linearDeriv (fun i=>J i) (fun i=>(A*J) i))=_
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  have he (i:ι) : Function.update J i ((A*J) i)=
      Matrix.updateRow J i (∑k,A i k • J k) := by
    congr 1
    funext j
    simp [Matrix.mul_apply,Finset.sum_apply]
  simp_rw [he]
  change (∑i, Matrix.det (Matrix.updateRow J i (∑k,A i k • J k)))=_
  simp_rw [Matrix.det_updateRow_sum,smul_eq_mul]
  rw [←Finset.sum_mul]
  rfl

theorem matrix_variational_det {J:ℝ→Matrix ι ι ℝ} {A:Matrix ι ι ℝ}
    {s:Set ℝ} {t:ℝ} (hJ:HasDerivWithinAt J (A*J t) s t) :
    HasDerivWithinAt (fun u=>Matrix.det (J u)) (Matrix.trace A*Matrix.det (J t)) s t := by
  have hd := (determinantMultilinear (ι:=ι)).hasFDerivAt (J t)
  have hc := hd.comp_hasDerivWithinAt t hJ
  change HasDerivWithinAt (fun u=>Matrix.det (J u))
    ((determinantMultilinear (ι:=ι)).linearDeriv (J t) (A*J t)) s t at hc
  rwa [determinantMultilinear_linearDeriv] at hc

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Jacobi's identity in variational form, valid even when the operator is singular. -/
theorem operator_variational_det {J:ℝ→E→L[ℝ]E} {A:E→L[ℝ]E}
    {s:Set ℝ} {t:ℝ} (hJ:HasDerivWithinAt J (A.comp (J t)) s t) :
    HasDerivWithinAt (fun u=>(J u).det)
      (LinearMap.trace ℝ E A.toLinearMap*(J t).det) s t := by
  classical
  let b := Module.finBasis ℝ E
  let C : (E→L[ℝ]E) →L[ℝ] (Fin (Module.finrank ℝ E)→
      Fin (Module.finrank ℝ E)→ℝ) :=
    ((LinearMap.toMatrix b b).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap
  have hC : HasDerivWithinAt (fun u=>C (J u)) (C (A.comp (J t))) s t :=
    (C.hasFDerivAt (x:=J t)).comp_hasDerivWithinAt t hJ
  have hmul : C (A.comp (J t))=
      @HMul.hMul (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
        _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (C A) (C (J t)) := by
    change LinearMap.toMatrix b b (A.toLinearMap.comp (J t).toLinearMap)=_
    exact LinearMap.toMatrix_comp b b b _ _
  rw [hmul] at hC
  have hd := matrix_variational_det hC
  change HasDerivWithinAt
    (fun u=>Matrix.det (LinearMap.toMatrix b b (J u).toLinearMap))
    (Matrix.trace (LinearMap.toMatrix b b A.toLinearMap)*
      Matrix.det (LinearMap.toMatrix b b (J t).toLinearMap)) s t at hd
  simpa only [LinearMap.det_toMatrix,
    ←LinearMap.trace_eq_matrix_trace ℝ b] using hd

end PersistencePays
#print axioms PersistencePays.operator_variational_det
#print axioms PersistencePays.matrix_variational_det
