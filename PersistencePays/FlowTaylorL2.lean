import PersistencePays.FlowTaylor
import Mathlib.MeasureTheory.Function.L2Space

/-! Cubic mean-square Taylor control from any square-integrable envelope for the jerk. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω} [IsFiniteMeasure μ]

theorem third_order_trajectory_L2 {f v a e:ℝ→Ω→E} {θ B:ℝ} {K:Ω→ℝ}
    (hK:MemLp K 2 μ) (hKpos:∀x,0≤K x)
    (hf:∀x,∀t∈uIcc 0 θ,HasDerivWithinAt (fun u=>f u x) (v t x) (uIcc 0 θ) t)
    (hv:∀x,∀t∈uIcc 0 θ,HasDerivWithinAt (fun u=>v u x) (a t x) (uIcc 0 θ) t)
    (ha:∀x,∀t∈uIcc 0 θ,HasDerivWithinAt (fun u=>a u x) (e t x) (uIcc 0 θ) t)
    (he:∀x,∀t∈uIcc 0 θ,‖e t x‖≤K x)
    (hm:AEStronglyMeasurable (fun x=>f θ x-f 0 x-θ • v 0 x-(θ^2/2) • a 0 x) μ)
    (hKB:∫x,|K x|^2 ∂μ≤B^2) :
    MemLp (fun x=>f θ x-f 0 x-θ • v 0 x-(θ^2/2) • a 0 x) 2 μ ∧
    (∫x,‖f θ x-f 0 x-θ • v 0 x-(θ^2/2) • a 0 x‖^2 ∂μ)≤(B*|θ|^3)^2 := by
  let r := fun x=>f θ x-f 0 x-θ • v 0 x-(θ^2/2) • a 0 x
  have hb (x:Ω) : ‖r x‖≤|θ|^3*K x := by
    simpa only [r,mul_comm] using third_order_trajectory_remainder
      (hKpos x) (hf x) (hv x) (ha x) (he x)
  have hr : MemLp r 2 μ := (hK.const_smul (|θ|^3)).mono' hm
    (Filter.Eventually.of_forall hb)
  refine ⟨hr,?_⟩
  have hKi : Integrable (fun x=>|K x|^2) μ := by
    simpa only [Real.norm_eq_abs] using hK.integrable_norm_pow'
  have hp : (∫x,‖r x‖^2 ∂μ)≤∫x,|θ|^6*|K x|^2 ∂μ := by
    apply integral_mono hr.integrable_norm_pow' (hKi.const_mul _)
    intro x
    have hs := (sq_le_sq₀ (norm_nonneg (r x)) (mul_nonneg (pow_nonneg (abs_nonneg _) 3) (hKpos x))).mpr (hb x)
    convert hs using 1
    change |θ|^6*|K x|^2=(|θ|^3*K x)^2
    rw [sq_abs]
    ring
  rw [integral_const_mul] at hp
  have hk := mul_le_mul_of_nonneg_left hKB (pow_nonneg (abs_nonneg θ) 6)
  calc
    (∫x,‖r x‖^2 ∂μ) ≤ |θ|^6*(∫x,|K x|^2 ∂μ) := hp
    _ ≤ |θ|^6*B^2 := hk
    _ = (B*|θ|^3)^2 := by ring

end PersistencePays
#print axioms PersistencePays.third_order_trajectory_L2
