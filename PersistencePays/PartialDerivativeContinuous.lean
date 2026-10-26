import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Continuity of the spatial derivative of a jointly C¹ time-dependent field. -/
noncomputable section
namespace PersistencePays
variable {E V:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem spatial_fderiv_eq {f:ℝ→E→V} (hf:Differentiable ℝ f.uncurry) (t:ℝ) (x:E) :
    fderiv ℝ (f t) x=(fderiv ℝ f.uncurry (t,x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hp:HasFDerivAt (fun y:E=>(t,y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const (𝕜:=ℝ) t x).prodMk (hasFDerivAt_id (𝕜:=ℝ) x)
  exact ((hf (t,x)).hasFDerivAt.comp x hp).fderiv

theorem spatial_fderiv_continuous {f:ℝ→E→V} (hf:ContDiff ℝ 1 f.uncurry) :
    Continuous (fun p:ℝ×E=>fderiv ℝ (f p.1) p.2) := by
  have heq:(fun p:ℝ×E=>fderiv ℝ (f p.1) p.2)=
      (fun p=>(fderiv ℝ f.uncurry p).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    funext p
    exact spatial_fderiv_eq (hf.differentiable (by norm_num)) p.1 p.2
  rw [heq]
  exact (ContinuousLinearMap.compL ℝ E (ℝ×E) V).continuous₂.comp₂
    (hf.continuous_fderiv (by norm_num)) continuous_const

end PersistencePays
#print axioms PersistencePays.spatial_fderiv_continuous
