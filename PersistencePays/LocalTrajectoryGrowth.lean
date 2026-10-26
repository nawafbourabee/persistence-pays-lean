import PersistencePays.FlowTaylor
import Mathlib.Topology.Order.Compact

/-! Uniform local growth for an actual trajectory in either time direction.
A compact-interval maximum and a short-time absorption suffice. -/
noncomputable section
namespace PersistencePays
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_trajectory_growth {X D:ℝ→E} {θ C:ℝ} (hC:0≤C)
    (hθ:C*|θ|≤1/2)
    (hX:∀u∈uIcc 0 θ,HasDerivWithinAt X (D u) (uIcc 0 θ) u)
    (hD:∀u∈uIcc 0 θ,‖D u‖≤C*(1+‖X u‖)) :
    ∀u∈uIcc 0 θ,1+‖X u‖≤2*(1+‖X 0‖) := by
  have hc:ContinuousOn X (uIcc 0 θ):=fun u hu=>(hX u hu).continuousWithinAt
  obtain ⟨r,hr,hmax⟩:=isCompact_uIcc.exists_isMaxOn ⟨0,left_mem_uIcc⟩ hc.norm
  have hd:∀u∈uIcc 0 θ,‖D u‖≤C*(1+‖X r‖):=fun u hu=>
    (hD u hu).trans (mul_le_mul_of_nonneg_left (by have hh:‖X u‖≤‖X r‖:=hmax hu; linarith) hC)
  have hm:‖X r-X 0‖≤C*(1+‖X r‖)*|r|:=by
    simpa only [sub_zero,Real.norm_eq_abs] using
      (convex_uIcc 0 θ).norm_image_sub_le_of_norm_hasDerivWithin_le hX hd left_mem_uIcc hr
  have hrabs:|r|≤|θ|:=by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have hn:‖X r‖≤‖X r-X 0‖+‖X 0‖:=by
    simpa only [sub_add_cancel] using norm_add_le (X r-X 0) (X 0)
  have htime:C*(1+‖X r‖)*|θ|≤(1+‖X r‖)/2:=by
    nlinarith [mul_le_mul_of_nonneg_right hθ (by positivity : 0≤1+‖X r‖)]
  have hm':‖X r-X 0‖≤(1+‖X r‖)/2 :=
    hm.trans ((mul_le_mul_of_nonneg_left hrabs (by positivity)).trans htime)
  intro u hu
  have hux:‖X u‖≤‖X r‖:=hmax hu
  linarith

end PersistencePays
#print axioms PersistencePays.local_trajectory_growth
