import PersistencePays.MonotoneDivergence
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Mollification retains the favorable singular-Hessian sign: the derivative
of the mollified monotone field dominates the mollification of its actual
almost-everywhere derivative in every quadratic direction. -/
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology RealInnerProductSpace Convolution
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def quadraticEvaluation (v : E) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)

@[simp] lemma quadraticEvaluation_apply (v : E) (A : E →L[ℝ] E) :
    quadraticEvaluation v A = ⟪v,A v⟫ := rfl

lemma convolution_quadratic {η : E → ℝ} {G : E → E →L[ℝ] E}
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hG : LocallyIntegrable G volume) (x v : E) :
    ⟪v,((η ⋆[lsmul ℝ ℝ,volume] G) x) v⟫ =
      ∫ y,η (x-y)*⟪v,G y v⟫ := by
  have hi := (hηc.convolutionExists_left (lsmul ℝ ℝ) hη hG x).integrable_swap
  have hh := (quadraticEvaluation v).integral_comp_comm hi
  rw [convolution_eq_swap]
  simpa only [quadraticEvaluation_apply,lsmul_apply,coe_smul',Pi.smul_apply,
    inner_smul_right] using hh.symm

lemma mollified_derivative_quadratic {η : E → ℝ} {T : E → E}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hT : LocallyIntegrable T volume) (x v : E) :
    ⟪v,(fderiv ℝ (η ⋆[lsmul ℝ ℝ,volume] T) x) v⟫ =
      ∫ y,(fderiv ℝ η (x-y) v)*⟪v,T y⟫ := by
  have hd := hηc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hη hT x
  rw [hd.fderiv,convolution_eq_swap]
  have hi := ((hηc.fderiv ℝ).convolutionExists_left ((lsmul ℝ ℝ).precompL E)
    (hη.continuous_fderiv one_ne_zero) hT x).integrable_swap
  have hh := (quadraticEvaluation v).integral_comp_comm hi
  simpa only [quadraticEvaluation_apply,precompL_apply,lsmul_apply,
    inner_smul_right] using hh.symm

theorem mollified_derivative_dominates
    {T : E → E} {G : E → E →L[ℝ] E} {s : Set E}
    (hT : LocallyIntegrable T volume) (hGi : LocallyIntegrable G volume)
    (hs : volume sᶜ=0)
    (hmono : ∀ x∈s,∀ y∈s,0≤⟪T y-T x,y-x⟫)
    (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,∀ v:E,0≤⟪v,G x v⟫)
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hη0 : ∀ x,0≤η x) (x v : E) :
    ⟪v,((η ⋆[lsmul ℝ ℝ,volume] G) x) v⟫ ≤
      ⟪v,(fderiv ℝ (η ⋆[lsmul ℝ ℝ,volume] T) x) v⟫ := by
  let w : E → ℝ := fun y => η (x-y)
  have hw : ContDiff ℝ 1 w := hη.comp (contDiff_const.sub contDiff_id)
  have hwc : HasCompactSupport w := hηc.comp_homeomorph (Homeomorph.subLeft x)
  have hwd : ∀ y,fderiv ℝ w y v = -(fderiv ℝ η (x-y) v) := by
    intro y
    have hh := (hη.differentiable one_ne_zero (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt w ((fderiv ℝ η (x-y)).comp
      (0-ContinuousLinearMap.id ℝ E)) y at hh
    rw [hh.fderiv]
    simp only [comp_apply,sub_apply,zero_apply,id_apply,map_neg,zero_sub,neg_apply]
  have hh := (compact_monotone_directional_divergence
    hT hs hmono hG hd hpos hw hwc (fun y => hη0 (x-y)) v).2
  rw [convolution_quadratic hη.continuous hηc hGi,
    mollified_derivative_quadratic hη hηc hT]
  simpa only [w,hwd,neg_mul,integral_neg,neg_neg] using hh

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.mollified_derivative_dominates
