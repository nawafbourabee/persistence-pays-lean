import PersistencePays.FlowTaylorL2
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual material acceleration and jerk of a smooth conditional-mean flow.
Only polynomial growth of the actual first two joint derivatives is needed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace PersistencePays
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance meanMaterialProdNorm : NormedAddCommGroup (ℝ×E) := inferInstance
local instance meanMaterialProdSpace : NormedSpace ℝ (ℝ×E) := inferInstance
local instance meanMaterialOperatorNorm : NormedAddCommGroup ((ℝ×E)→L[ℝ]E) := inferInstance

def materialAcceleration (F:ℝ×E→E) (p:ℝ×E):E := fderiv ℝ F p (1,F p)
def materialJerk (F:ℝ×E→E) (p:ℝ×E):E :=
  fderiv ℝ (fderiv ℝ F) p (1,F p) (1,F p)+
    fderiv ℝ F p (0,materialAcceleration F p)

theorem materialAcceleration_contDiff {F:ℝ×E→E} (hF:ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (materialAcceleration F) :=
  (hF.fderiv_right (m:=1) (by norm_num)).clm_apply
    (contDiff_const.prodMk (hF.of_le (by norm_num)))

theorem meanFlow_material_derivatives {F:ℝ×E→E} (hF:ContDiff ℝ 2 F)
    {X:ℝ→E} {I:Set ℝ} {s u:ℝ}
    (hX:HasDerivWithinAt X (F (s+u,X u)) I u) :
    HasDerivWithinAt (fun v=>F (s+v,X v)) (materialAcceleration F (s+u,X u)) I u ∧
    HasDerivWithinAt (fun v=>materialAcceleration F (s+v,X v))
      (materialJerk F (s+u,X u)) I u := by
  have hp:HasDerivWithinAt (fun v=>(s+v,X v)) (1,F (s+u,X u)) I u :=
    ((hasDerivWithinAt_id u I).const_add s).prodMk hX
  have hd:=((hF.differentiable (by norm_num)) (s+u,X u)).hasFDerivAt.comp_hasDerivWithinAt u hp
  refine ⟨hd,?_⟩
  have hDf:Differentiable ℝ (fderiv ℝ F):=
    (hF.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hD:HasDerivWithinAt (fun v=>fderiv ℝ F (s+v,X v))
      (fderiv ℝ (fderiv ℝ F) (s+u,X u) (1,F (s+u,X u))) I u :=
    (hDf (s+u,X u)).hasFDerivAt.comp_hasDerivWithinAt u hp
  exact hD.clm_apply ((hasDerivWithinAt_const u I (1:ℝ)).prodMk hd)

theorem materialAcceleration_eq_time_spatial {F:ℝ×E→E}
    (hF:Differentiable ℝ F) (s:ℝ) (y:E) :
    materialAcceleration F (s,y)=deriv (fun t=>F (t,y)) s+
      fderiv ℝ (fun x=>F (s,x)) y (F (s,y)) := by
  have ht:HasDerivAt (fun t=>F (t,y)) (fderiv ℝ F (s,y) (1,0)) s:=
    (hF (s,y)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
  have hx:HasFDerivAt (fun x=>F (s,x))
      ((fderiv ℝ F (s,y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y:=
    (hF (s,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜:=ℝ) s y).prodMk (hasFDerivAt_id y))
  rw [ht.deriv,hx.fderiv,ContinuousLinearMap.comp_apply]
  change fderiv ℝ F (s,y) (1,F (s,y))=
    fderiv ℝ F (s,y) (1,0)+fderiv ℝ F (s,y) (0,F (s,y))
  rw [←map_add]
  congr 1
  ext <;> simp

theorem material_growth {F:ℝ×E→E} {C:ℝ} (hC:1≤C) (p:ℝ×E)
    (h0:‖F p‖≤C*(1+‖p.2‖))
    (h1:‖fderiv ℝ F p‖≤C*(1+‖p.2‖))
    (h2:‖fderiv ℝ (fderiv ℝ F) p‖≤C*(1+‖p.2‖)^2) :
    ‖materialAcceleration F p‖≤C^2*(1+‖p.2‖)^2 ∧
    ‖materialJerk F p‖≤2*C^3*(1+‖p.2‖)^4 := by
  have hC0:0≤C:=by linarith
  have hR:1≤1+‖p.2‖:=by linarith [norm_nonneg p.2]
  have hlift:‖((1:ℝ),F p)‖≤C*(1+‖p.2‖):=by
    rw [Prod.norm_def,norm_one]
    exact max_le (by nlinarith) h0
  have ha:‖materialAcceleration F p‖≤C^2*(1+‖p.2‖)^2:=by
    apply ((fderiv ℝ F p).le_opNorm _).trans
    exact (mul_le_mul h1 hlift (norm_nonneg _) (by positivity)).trans_eq (by ring)
  refine ⟨ha,?_⟩
  have hb:‖fderiv ℝ (fderiv ℝ F) p (1,F p) (1,F p)‖≤C^3*(1+‖p.2‖)^4:=by
    calc
      _≤‖fderiv ℝ (fderiv ℝ F) p (1,F p)‖*‖((1:ℝ),F p)‖:=ContinuousLinearMap.le_opNorm _ _
      _≤(‖fderiv ℝ (fderiv ℝ F) p‖*‖((1:ℝ),F p)‖)*‖((1:ℝ),F p)‖:=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _≤((C*(1+‖p.2‖)^2)*(C*(1+‖p.2‖)))*(C*(1+‖p.2‖)):=
        mul_le_mul (mul_le_mul h2 hlift (norm_nonneg _) (by positivity)) hlift
          (norm_nonneg _) (by positivity)
      _=_:=by ring
  have hc:‖fderiv ℝ F p (0,materialAcceleration F p)‖≤C^3*(1+‖p.2‖)^3:=by
    calc
      _≤‖fderiv ℝ F p‖*‖(0,materialAcceleration F p)‖:=ContinuousLinearMap.le_opNorm _ _
      _=‖fderiv ℝ F p‖*‖materialAcceleration F p‖:=by
        rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      _≤(C*(1+‖p.2‖))*(C^2*(1+‖p.2‖)^2):=
        mul_le_mul h1 ha (norm_nonneg _) (by positivity)
      _=_:=by ring
  have hp:C^3*(1+‖p.2‖)^3≤C^3*(1+‖p.2‖)^4:=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by norm_num)) (by positivity)
  exact (norm_add_le _ _).trans ((add_le_add hb (hc.trans hp)).trans_eq (by ring))

end PersistencePays
#print axioms PersistencePays.meanFlow_material_derivatives
#print axioms PersistencePays.material_growth
