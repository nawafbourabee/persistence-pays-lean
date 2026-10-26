import PersistencePays.DeterminantFlow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace PersistencePays
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The continuity equation conserves density times the actual flow Jacobian. -/
theorem VariationalFlow.density_jacobian {m:ℝ→E→E} {Dm:ℝ→E→E→L[ℝ]E}
    {a b:ℝ} (flow:VariationalFlow E m Dm a b) (hab:a≤b)
    (n:ℝ×E→ℝ) (hn:∀t∈Icc a b,∀x,DifferentiableAt ℝ n (t,x))
    (hpde:∀t∈Icc a b,∀x,
      fderiv ℝ n (t,x) (1,m t x)=
        -n (t,x)*LinearMap.trace ℝ E (Dm t x).toLinearMap)
    {t:ℝ} (ht:t∈Icc a b) (x:E) :
    n (t,flow.toFun t x)*(flow.jacobian t x).det=n (a,x) := by
  have hd (u:ℝ) (hu:u∈Icc a b) :
      HasDerivWithinAt (fun s=>n (s,flow.toFun s x)*(flow.jacobian s x).det)
        0 (Icc a b) u := by
    have hp := (hasDerivWithinAt_id u (Icc a b)).prodMk
      (flow.time_derivative u hu x)
    have hnd := (hn u hu (flow.toFun u x)).hasFDerivAt.comp_hasDerivWithinAt u hp
    rw [hpde u hu (flow.toFun u x)] at hnd
    have hdet := operator_variational_det (flow.variational_equation u hu x)
    convert hnd.mul hdet using 1 <;> first | rfl | (simp only [Function.comp_apply,id_eq]; ring)
  have hbnd := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le (C:=0)
    hd (fun u hu=>by simp) ⟨le_rfl,hab⟩ ht
  have heq : n (t,flow.toFun t x)*(flow.jacobian t x).det=
      n (a,flow.toFun a x)*(flow.jacobian a x).det := by
    apply sub_eq_zero.mp
    exact norm_eq_zero.mp (le_antisymm (by simpa using hbnd) (norm_nonneg _))
  have hi : (ContinuousLinearMap.id ℝ E).det=1 := LinearMap.det_id
  simpa only [flow.initial,flow.jacobian_initial,hi,mul_one] using heq

/-- Positive transported density forces the variational determinant to remain positive. -/
theorem VariationalFlow.jacobian_det_pos {m:ℝ→E→E} {Dm:ℝ→E→E→L[ℝ]E}
    {a b:ℝ} (flow:VariationalFlow E m Dm a b) (hab:a≤b)
    (n:ℝ×E→ℝ) (hn:∀t∈Icc a b,∀x,DifferentiableAt ℝ n (t,x))
    (hpos:∀t∈Icc a b,∀x,0<n (t,x))
    (hpde:∀t∈Icc a b,∀x,
      fderiv ℝ n (t,x) (1,m t x)=
        -n (t,x)*LinearMap.trace ℝ E (Dm t x).toLinearMap)
    {t:ℝ} (ht:t∈Icc a b) (x:E) : 0<(flow.jacobian t x).det := by
  have heq := flow.density_jacobian hab n hn hpde ht x
  exact (mul_pos_iff_of_pos_left (hpos t ht (flow.toFun t x))).mp
    (heq ▸ hpos a ⟨le_rfl,hab⟩ x)

end PersistencePays
#print axioms PersistencePays.VariationalFlow.density_jacobian
#print axioms PersistencePays.VariationalFlow.jacobian_det_pos
