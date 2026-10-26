import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! First and second derivative growth of a smooth coefficient times a
linear parameter. This preserves the polynomial degree in that parameter. -/
noncomputable section
namespace PersistencePays
variable {P E F V:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem bilinear_fderiv_bound (B:E→L[ℝ]F→L[ℝ]V)
    {κ:ℝ} (hκ:0≤κ) (hB:∀u v,‖B u v‖≤κ*‖u‖*‖v‖)
    {f:P→E} {g:P→F} {x:P} (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y=>B (f y) (g y)) x‖≤
      κ*(‖f x‖*‖fderiv ℝ g x‖+‖fderiv ℝ f x‖*‖g x‖) := by
  rw [B.fderiv_of_bilinear hf hg]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖B (f x) (fderiv ℝ g x v)+B (fderiv ℝ f x v) (g x)‖≤_
  calc
    _ ≤ ‖B (f x) (fderiv ℝ g x v)‖+‖B (fderiv ℝ f x v) (g x)‖ := norm_add_le _ _
    _ ≤ κ*‖f x‖*‖fderiv ℝ g x v‖+κ*‖fderiv ℝ f x v‖*‖g x‖ := add_le_add (hB _ _) (hB _ _)
    _ ≤ κ*‖f x‖*(‖fderiv ℝ g x‖*‖v‖)+κ*(‖fderiv ℝ f x‖*‖v‖)*‖g x‖ := by
      gcongr
      · exact (fderiv ℝ g x).le_opNorm v
      · exact (fderiv ℝ f x).le_opNorm v
    _ = _ := by ring

theorem bilinear_fderiv_norm_bound (B:E→L[ℝ]F→L[ℝ]V)
    {f:P→E} {g:P→F} {x:P} (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y=>B (f y) (g y)) x‖≤
      ‖B‖*(‖f x‖*‖fderiv ℝ g x‖+‖fderiv ℝ f x‖*‖g x‖) :=
  bilinear_fderiv_bound B (κ:=‖B‖) (norm_nonneg B) B.le_opNorm₂ hf hg

theorem bilinear_second_linear_norm_bound (B:E→L[ℝ]F→L[ℝ]V) (L:P→L[ℝ]F)
    {f:P→E} (hf:Differentiable ℝ f) {x:P}
    (hdf:DifferentiableAt ℝ (fderiv ℝ f) x) :
    ‖fderiv ℝ (fderiv ℝ (fun y=>B (f y) (L y))) x‖≤
      ‖B‖*(2*‖fderiv ℝ f x‖*‖L‖+‖fderiv ℝ (fderiv ℝ f) x‖*‖L x‖) := by
  let G:P→P→L[ℝ]V:=fun y=>B.precompR P (f y) L
  let H:P→P→L[ℝ]V:=fun y=>B.precompL P (fderiv ℝ f y) (L y)
  have hG:DifferentiableAt ℝ G x:=
    ((B.precompR P).hasFDerivAt_of_bilinear (hf x).hasFDerivAt
      (hasFDerivAt_const (𝕜:=ℝ) L x)).differentiableAt
  have hH:DifferentiableAt ℝ H x:=
    ((B.precompL P).hasFDerivAt_of_bilinear hdf.hasFDerivAt L.hasFDerivAt).differentiableAt
  have heq:fderiv ℝ (fun y=>B (f y) (L y))=fun y=>G y+H y := by
    funext y
    rw [B.fderiv_of_bilinear (hf y) L.differentiableAt,L.fderiv]
  have bR:∀u v,‖B.precompR P u v‖≤‖B‖*‖u‖*‖v‖ := by
    intro u v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    exact (B.le_opNorm₂ u (v w)).trans (by
      calc
        _ ≤ ‖B‖*‖u‖*(‖v‖*‖w‖) := mul_le_mul_of_nonneg_left (v.le_opNorm w) (by positivity)
        _ = _ := by ring)
  have bL:∀u v,‖B.precompL P u v‖≤‖B‖*‖u‖*‖v‖ := by
    intro u v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    exact (B.le_opNorm₂ (u w) v).trans (by
      calc
        _ ≤ ‖B‖*(‖u‖*‖w‖)*‖v‖ := by gcongr; exact u.le_opNorm w
        _ = _ := by ring)
  have hnG:=bilinear_fderiv_bound (B.precompR P) (norm_nonneg B) bR
    (f:=f) (g:=fun _=>L) (x:=x) (hf x) (differentiableAt_const (c:=L))
  have hnH:=bilinear_fderiv_bound (B.precompL P) (norm_nonneg B) bL hdf L.differentiableAt
  have hc:fderiv ℝ (fun _:P=>L) x=0 := (hasFDerivAt_const (𝕜:=ℝ) L x).fderiv
  rw [hc] at hnG
  simp only [norm_zero,mul_zero,zero_add] at hnG
  rw [L.fderiv] at hnH
  rw [heq]
  change ‖fderiv ℝ (G+H) x‖≤_
  rw [fderiv_add hG hH]
  calc
    _ ≤ ‖fderiv ℝ G x‖+‖fderiv ℝ H x‖ := by
      convert norm_add_le (fderiv ℝ G x) (fderiv ℝ H x) using 1
    _ ≤ ‖B‖*(‖fderiv ℝ f x‖*‖L‖)+
        ‖B‖*(‖fderiv ℝ f x‖*‖L‖+‖fderiv ℝ (fderiv ℝ f) x‖*‖L x‖) := add_le_add hnG hnH
    _ = _ := by ring
end PersistencePays
#print axioms PersistencePays.bilinear_second_linear_norm_bound
