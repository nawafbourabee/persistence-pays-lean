import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! First and second derivative growth of a smooth coefficient times a
linear parameter. This preserves the polynomial degree in that parameter. -/
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PersistencePays
universe u
variable {P E F V:Type u}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


#synth SeminormedAddCommGroup (P →L[ℝ] F)
#synth Norm (P →L[ℝ] F)
#synth Norm (P →L[ℝ] V)
#synth Norm ((P →L[ℝ] F) →L[ℝ] P →L[ℝ] V)
#synth NormedAddCommGroup (P →L[ℝ] F)
#synth NormedSpace ℝ (P →L[ℝ] F)
#synth SeminormedAddCommGroup ((P →L[ℝ] F) →L[ℝ] P →L[ℝ] V)
#synth NormedSpace ℝ ((P →L[ℝ] F) →L[ℝ] P →L[ℝ] V)
local instance : SeminormedAddCommGroup ((P →L[ℝ] F) →L[ℝ] P →L[ℝ] V) := inferInstance
local instance : NormedSpace ℝ ((P →L[ℝ] F) →L[ℝ] P →L[ℝ] V) := inferInstance
#synth Norm (E →L[ℝ] (P →L[ℝ] F) →L[ℝ] P →L[ℝ] V)
variable (B:E→L[ℝ]F→L[ℝ]V)
#check B.precompR P
#check ‖(B.precompR P : E →L[ℝ] (P →L[ℝ] F) →L[ℝ] P →L[ℝ] V)‖
end PersistencePays
