import PersistencePays.MeanFlowMaterial
import PersistencePays.LocalTrajectoryGrowth
import PersistencePays.UniformFreeMoments
import PersistencePays.RelativeFlowTransport

/-! Cubic L² control of the actual signed characteristic endpoint map. The
polynomial envelope is integrated under its true initial position law. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace PersistencePays
open MeasureTheory Set
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance meanTaylorProdNorm : NormedAddCommGroup (ℝ×E) := inferInstance
local instance meanTaylorProdSpace : NormedSpace ℝ (ℝ×E) := inferInstance
local instance meanTaylorOperatorNorm : NormedAddCommGroup ((ℝ×E)→L[ℝ]E) := inferInstance

theorem signed_meanFlow_taylor {F:ℝ×E→E} (hF:ContDiff ℝ 2 F)
    (ν:Measure E) [IsProbabilityMeasure ν] (hν:MemLp id 8 ν)
    {s θ C B:ℝ} (hC:1≤C) (hθ:C*|θ|≤1/2)
    (hbound:∀u∈uIcc 0 θ,∀y:E,
      ‖F (s+u,y)‖≤C*(1+‖y‖) ∧
      ‖fderiv ℝ F (s+u,y)‖≤C*(1+‖y‖) ∧
      ‖fderiv ℝ (fderiv ℝ F) (s+u,y)‖≤C*(1+‖y‖)^2)
    (X:ℝ→E→E) (hX0:∀x,X 0 x=x)
    (hXm:Measurable (X θ))
    (hXd:∀x,∀u∈uIcc 0 θ,HasDerivWithinAt (fun v=>X v x)
      (F (s+u,X u x)) (uIcc 0 θ) u)
    (hB:(32*C^3)^2*(∫x,(1+‖x‖)^8 ∂ν)≤B^2) :
    ∃r:E→E,MemLp r 2 ν ∧
      (∀x,X θ x=x+θ • F (s,x)+(θ^2/2) • materialAcceleration F (s,x)+r x) ∧
      (∫x,‖r x‖^2 ∂ν)≤(B*|θ|^3)^2 := by
  let K:E→ℝ:=fun x=>32*C^3*(1+‖x‖)^4
  have hC0:0≤C:=by linarith
  have hK:MemLp K 2 ν := by
    exact (polynomialEnvelope_memLp_two ν 4 hν).const_mul (32*C^3)
  have hKB:(∫x,|K x|^2 ∂ν)≤B^2 := by
    have he:(fun x=>|K x|^2)=(fun x:E=>(32*C^3)^2*(1+‖x‖)^8):=by
      funext x
      dsimp only [K]
      rw [sq_abs,mul_pow,←pow_mul]
    rw [he,integral_const_mul]
    exact hB
  have hxgrow (x:E) (u:ℝ) (hu:u∈uIcc 0 θ):1+‖X u x‖≤2*(1+‖x‖):=by
    have hh:=local_trajectory_growth hC0 hθ (hXd x)
      (fun v hv=>(hbound v hv (X v x)).1) u hu
    simpa only [hX0] using hh
  have hv (x:E) (u:ℝ) (hu:u∈uIcc 0 θ):
      HasDerivWithinAt (fun v=>F (s+v,X v x))
        (materialAcceleration F (s+u,X u x)) (uIcc 0 θ) u :=
    (meanFlow_material_derivatives hF (hXd x u hu)).1
  have ha (x:E) (u:ℝ) (hu:u∈uIcc 0 θ):
      HasDerivWithinAt (fun v=>materialAcceleration F (s+v,X v x))
        (materialJerk F (s+u,X u x)) (uIcc 0 θ) u :=
    (meanFlow_material_derivatives hF (hXd x u hu)).2
  have he (x:E) (u:ℝ) (hu:u∈uIcc 0 θ):‖materialJerk F (s+u,X u x)‖≤K x:=by
    have hb:=hbound u hu (X u x)
    have hh:=(material_growth hC (s+u,X u x) hb.1 hb.2.1 hb.2.2).2
    apply hh.trans
    calc
      _≤2*C^3*(2*(1+‖x‖))^4:=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hxgrow x u hu) 4) (by positivity)
      _=K x:=by dsimp [K]; ring
  have hFsm:Measurable (fun x:E=>F (s,x)):=hF.continuous.measurable.comp (by fun_prop)
  have hasm:Measurable (fun x:E=>materialAcceleration F (s,x)):=
    (materialAcceleration_contDiff hF).continuous.measurable.comp (by fun_prop)
  have hm:AEStronglyMeasurable (fun x=>X θ x-X 0 x-θ • F (s+0,X 0 x)-
      (θ^2/2) • materialAcceleration F (s+0,X 0 x)) ν:=by
    simp only [hX0,add_zero]
    exact ((hXm.sub measurable_id).sub (hFsm.const_smul θ)).sub
      (hasm.const_smul (θ^2/2)) |>.aestronglyMeasurable
  obtain ⟨hr,hri⟩:=third_order_trajectory_L2 (μ:=ν) (f:=X)
    (v:=fun u x=>F (s+u,X u x))
    (a:=fun u x=>materialAcceleration F (s+u,X u x))
    (e:=fun u x=>materialJerk F (s+u,X u x))
    hK (fun x=>by dsimp [K]; positivity) hXd hv ha he hm hKB
  simp only [hX0,add_zero] at hr hri
  refine ⟨fun x=>X θ x-x-θ • F (s,x)-(θ^2/2) • materialAcceleration F (s,x),hr,?_,hri⟩
  intro x
  module

end PersistencePays
#print axioms PersistencePays.signed_meanFlow_taylor
