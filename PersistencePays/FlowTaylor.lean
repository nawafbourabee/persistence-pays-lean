import PersistencePays.FlowDensityTransport
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! Third-order trajectory control from actual derivatives, in either time direction. -/
noncomputable section
namespace PersistencePays
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem third_order_trajectory_remainder {f v a e:ℝ→E} {θ K:ℝ} (hK:0≤K)
    (hf:∀t∈uIcc 0 θ,HasDerivWithinAt f (v t) (uIcc 0 θ) t)
    (hv:∀t∈uIcc 0 θ,HasDerivWithinAt v (a t) (uIcc 0 θ) t)
    (ha:∀t∈uIcc 0 θ,HasDerivWithinAt a (e t) (uIcc 0 θ) t)
    (he:∀t∈uIcc 0 θ,‖e t‖≤K) :
    ‖f θ-f 0-θ • v 0-(θ^2/2) • a 0‖≤K*|θ|^3 := by
  have hz : (0:ℝ)∈uIcc 0 θ := left_mem_uIcc
  have hθ : θ∈uIcc 0 θ := right_mem_uIcc
  have huabs {u:ℝ} (hu:u∈uIcc 0 θ) : |u|≤|θ| := by
    simpa using abs_sub_left_of_mem_uIcc hu
  have hab (u:ℝ) (hu:u∈uIcc 0 θ) : ‖a u-a 0‖≤K*|θ| := by
    have h := (convex_uIcc 0 θ).norm_image_sub_le_of_norm_hasDerivWithin_le ha he hz hu
    have h' : ‖a u-a 0‖≤K*|u| := by simpa [Real.norm_eq_abs] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (huabs hu) hK)
  let r1 : ℝ→E := fun t=>v t-v 0-t • a 0
  have hr1 (u:ℝ) (hu:u∈uIcc 0 θ) :
      HasDerivWithinAt r1 (a u-a 0) (uIcc 0 θ) u := by
    have hh := ((hv u hu).sub_const (v 0)).sub
      ((hasDerivWithinAt_id u (uIcc 0 θ)).smul_const (a 0))
    change HasDerivWithinAt r1 (a u-1 • a 0) (uIcc 0 θ) u at hh
    simpa only [one_smul] using hh
  have hr1b (u:ℝ) (hu:u∈uIcc 0 θ) : ‖r1 u‖≤K*|θ|^2 := by
    have h := (convex_uIcc 0 θ).norm_image_sub_le_of_norm_hasDerivWithin_le
      hr1 hab hz hu
    have h' : ‖r1 u‖≤(K*|θ|)*|u| := by simpa [r1,Real.norm_eq_abs] using h
    calc
      ‖r1 u‖ ≤ (K*|θ|)*|u| := h'
      _ ≤ (K*|θ|)*|θ| := mul_le_mul_of_nonneg_left (huabs hu) (mul_nonneg hK (abs_nonneg _))
      _ = K*|θ|^2 := by ring
  let r : ℝ→E := fun t=>f t-f 0-t • v 0-(t^2/2) • a 0
  have hr (u:ℝ) (hu:u∈uIcc 0 θ) : HasDerivWithinAt r (r1 u) (uIcc 0 θ) u := by
    have hp : HasDerivWithinAt (fun z:ℝ=>z^2/2) u (uIcc 0 θ) u := by
      convert ((hasDerivWithinAt_id u (uIcc 0 θ)).pow 2).div_const 2 using 1 <;>
        first | rfl | (norm_num <;> ring)
    have hh := (((hf u hu).sub_const (f 0)).sub
        ((hasDerivWithinAt_id u (uIcc 0 θ)).smul_const (v 0))).sub
        (hp.smul_const (a 0))
    change HasDerivWithinAt r (v u-1 • v 0-u • a 0) (uIcc 0 θ) u at hh
    simpa only [one_smul,r1] using hh
  have h := (convex_uIcc 0 θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hr hr1b hz hθ
  simpa [r,Real.norm_eq_abs,pow_succ,mul_assoc] using h

end PersistencePays
#print axioms PersistencePays.third_order_trajectory_remainder
