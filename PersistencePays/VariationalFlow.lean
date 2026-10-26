import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Interface for an actual classical flow and its spatial variational
 equation. Every field is a deterministic differential or inverse property;
 no pushforward identity or continuity-equation uniqueness is assumed. -/
noncomputable section
namespace PersistencePays
open Set
variable (E:Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure VariationalFlow (m:ℝ→E→E) (Dm:ℝ→E→E→L[ℝ]E) (a b:ℝ) where
  toFun : ℝ→E→E
  jacobian : ℝ→E→E→L[ℝ]E
  initial : ∀x,toFun a x=x
  jacobian_initial : ∀x,jacobian a x=ContinuousLinearMap.id ℝ E
  field_derivative : ∀t∈Icc a b,∀x,HasFDerivAt (m t) (Dm t x) x
  time_derivative : ∀t∈Icc a b,∀x,
    HasDerivWithinAt (fun s=>toFun s x) (m t (toFun t x)) (Icc a b) t
  variational_equation : ∀t∈Icc a b,∀x,
    HasDerivWithinAt (fun s=>jacobian s x)
      ((Dm t (toFun t x)).comp (jacobian t x)) (Icc a b) t
  spatial_derivative : ∀t∈Icc a b,∀x,HasFDerivAt (toFun t) (jacobian t x) x
  bijective : ∀t∈Icc a b,Function.Bijective (toFun t)

end PersistencePays
