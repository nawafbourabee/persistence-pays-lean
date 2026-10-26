import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! A direct operator-norm bound for the derivative of a scalar-functional
 tensor product, without a coordinate or dimension factor. -/
noncomputable section
namespace PersistencePays
variable {P V:Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def tensorDerivative (r:P→L[ℝ]ℝ) (v:V) (Dr:P→L[ℝ]P→L[ℝ]ℝ) (Dv:P→L[ℝ]V) :
    P→L[ℝ]P→L[ℝ]V :=
  (ContinuousLinearMap.smulRightL ℝ P V).precompR P r Dv+
  (ContinuousLinearMap.smulRightL ℝ P V).precompL P Dr v

theorem tensorDerivative_norm_le (r:P→L[ℝ]ℝ) (v:V)
    (Dr:P→L[ℝ]P→L[ℝ]ℝ) (Dv:P→L[ℝ]V) :
    ‖tensorDerivative r v Dr Dv‖≤‖r‖*‖Dv‖+‖Dr‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖r.smulRight (Dv x)+(Dr x).smulRight v‖≤_
  calc
    _ ≤ ‖r.smulRight (Dv x)‖+‖(Dr x).smulRight v‖:=norm_add_le _ _
    _ = ‖r‖*‖Dv x‖+‖Dr x‖*‖v‖:=by rw [ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ ‖r‖*(‖Dv‖*‖x‖)+(‖Dr‖*‖x‖)*‖v‖:=add_le_add
      (mul_le_mul_of_nonneg_left (Dv.le_opNorm x) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Dr.le_opNorm x) (norm_nonneg _))
    _ = _:=by ring

theorem tensor_hasFDerivAt {r:P→P→L[ℝ]ℝ} {v:P→V}
    {Dr:P→L[ℝ]P→L[ℝ]ℝ} {Dv:P→L[ℝ]V} {x:P}
    (hr:HasFDerivAt r Dr x) (hv:HasFDerivAt v Dv x) :
    HasFDerivAt (fun y=>(r y).smulRight (v y)) (tensorDerivative (r x) (v x) Dr Dv) x :=
  (ContinuousLinearMap.smulRightL ℝ P V).hasFDerivAt_of_bilinear hr hv

end PersistencePays
#print axioms PersistencePays.tensorDerivative_norm_le
