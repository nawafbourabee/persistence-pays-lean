import PersistencePays.BilinearDerivativeBounds
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Operator.Prod

noncomputable section
namespace PersistencePays
variable {P E F:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_linear_pullback_norm (L:P→L[ℝ]E) {f:E→F} {x:P}
    (hf:DifferentiableAt ℝ f (L x)) :
    ‖fderiv ℝ (fun y=>f (L y)) x‖≤‖fderiv ℝ f (L x)‖*‖L‖ := by
  change ‖fderiv ℝ (f ∘ L) x‖≤_
  rw [fderiv_comp x hf L.differentiableAt,L.fderiv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem second_fderiv_linear_pullback_norm (L:P→L[ℝ]E) {f:E→F}
    (hf:Differentiable ℝ f) {x:P}
    (hdf:DifferentiableAt ℝ (fderiv ℝ f) (L x)) :
    ‖fderiv ℝ (fderiv ℝ (fun y=>f (L y))) x‖≤
      ‖fderiv ℝ (fderiv ℝ f) (L x)‖*‖L‖^2 := by
  let B:(E→L[ℝ]F)→L[ℝ](P→L[ℝ]E)→L[ℝ]P→L[ℝ]F:=ContinuousLinearMap.compL ℝ P E F
  have hb:∀u v,‖B u v‖≤(1:ℝ)*‖u‖*‖v‖:=by
    intro u v
    simpa [B] using ContinuousLinearMap.opNorm_comp_le u v
  have heq:fderiv ℝ (fun y=>f (L y))=fun y=>B (fderiv ℝ f (L y)) L := by
    funext y
    exact fderiv_comp y (hf _) L.differentiableAt |>.trans (by rw [L.fderiv]; rfl)
  have hg:DifferentiableAt ℝ (fun y=>fderiv ℝ f (L y)) x:=hdf.comp x L.differentiableAt
  have hn:=bilinear_fderiv_bound B (by norm_num : (0:ℝ)≤1) hb
    (f:=fun y=>fderiv ℝ f (L y)) (g:=fun _=>L) (x:=x) hg (differentiableAt_const L)
  have hc:fderiv ℝ (fun _:P=>L) x=0 := (hasFDerivAt_const (𝕜:=ℝ) L x).fderiv
  rw [hc] at hn
  simp only [norm_zero,mul_zero,zero_add,one_mul] at hn
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ (fun y=>fderiv ℝ f (L y)) x‖*‖L‖ := hn
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) (L x)‖*‖L‖)*‖L‖ :=
      mul_le_mul_of_nonneg_right (fderiv_linear_pullback_norm L hdf) (norm_nonneg _)
    _ = _ := by ring
end PersistencePays
#print axioms PersistencePays.second_fderiv_linear_pullback_norm
