import PersistencePays.ConvexGradientBound
import PersistencePays.MollifiedDerivative

/-! An explicit sequence of smooth compact mollifiers. Pairing the mollified
convex gradient against a compact continuous field converges to the original
pairing; the domination uses local convex bounds, not translated weighted
moments. -/
open Set Filter MeasureTheory ContinuousLinearMap Metric
open scoped Topology RealInnerProductSpace Convolution ContDiff
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def shrinkingBump (n : ℕ) : ContDiffBump (0:E) :=
  ⟨((n:ℝ)+1)⁻¹,2*((n:ℝ)+1)⁻¹,by positivity,by
    have : 0<((n:ℝ)+1)⁻¹ := by positivity
    linarith⟩

def smoothKernel (n : ℕ) : E → ℝ := (shrinkingBump (E:=E) n).normed volume

def mollify (n : ℕ) (T : E → E) : E → E :=
  smoothKernel n ⋆[lsmul ℝ ℝ,volume] T

theorem smoothKernel_contDiff (n : ℕ) : ContDiff ℝ ∞ (smoothKernel (E:=E) n) :=
  (shrinkingBump n).contDiff_normed

theorem smoothKernel_compact (n : ℕ) : HasCompactSupport (smoothKernel (E:=E) n) :=
  (shrinkingBump n).hasCompactSupport_normed

theorem smoothKernel_nonneg (n : ℕ) (x : E) : 0≤smoothKernel n x :=
  (shrinkingBump n).nonneg_normed x

theorem smoothKernel_integral (n : ℕ) : ∫ x:E,smoothKernel n x=1 :=
  (shrinkingBump n).integral_normed

theorem shrinkingBump_rOut_le (n : ℕ) : (shrinkingBump (E:=E) n).rOut≤2 := by
  change 2*((n:ℝ)+1)⁻¹≤2
  have hh : ((n:ℝ)+1)⁻¹≤1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  linarith

theorem shrinkingBump_rOut_tendsto :
    Tendsto (fun n => (shrinkingBump (E:=E) n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump,one_div,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2

theorem mollify_contDiff {T:E→E} (hT : LocallyIntegrable T volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollify n T) :=
  (smoothKernel_compact n).contDiff_convolution_left (lsmul ℝ ℝ)
    (smoothKernel_contDiff n) hT

theorem mollify_tendsto_ae {T:E→E} (hT : LocallyIntegrable T volume) :
    ∀ᵐ x ∂volume,Tendsto (fun n => mollify n T x) atTop (𝓝 (T x)) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingBump_rOut_tendsto (Eventually.of_forall (fun _ => le_rfl)) hT

theorem norm_mollify_le {T:E→E} (hT : LocallyIntegrable T volume)
    {R C:ℝ} (hC : 0≤C)
    (hb : ∀ᵐ y ∂volume,‖y‖≤R+2 → ‖T y‖≤C)
    (n : ℕ) {x:E} (hx : ‖x‖≤R) : ‖mollify n T x‖≤C := by
  have hi := ((smoothKernel_compact (E:=E) n).convolutionExists_left (lsmul ℝ ℝ)
    (smoothKernel_contDiff n).continuous hT x).integrable_swap
  have hk : Integrable (fun y:E => smoothKernel n (x-y)*C) volume :=
    (((smoothKernel_contDiff n).continuous.integrable_of_hasCompactSupport
      (smoothKernel_compact n)).comp_sub_left x).mul_const C
  unfold mollify
  rw [convolution_eq_swap]
  calc
    _ ≤ ∫ y,‖(lsmul ℝ ℝ) (smoothKernel n (x-y)) (T y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y,smoothKernel n (x-y)*C := by
      apply integral_mono_ae hi.norm hk
      filter_upwards [hb] with y hy
      simp only [lsmul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (smoothKernel_nonneg n (x-y))]
      by_cases hz : smoothKernel n (x-y)=0
      · simp only [hz,zero_mul,le_refl]
      · have hs : x-y∈Function.support (smoothKernel (E:=E) n) := hz
        change x-y∈Function.support ((shrinkingBump n).normed volume) at hs
        rw [(shrinkingBump n).support_normed_eq] at hs
        have hs' : ‖x-y‖<(shrinkingBump (E:=E) n).rOut := by
          simpa only [mem_ball,dist_zero_right] using hs
        have hdist : ‖x-y‖≤2 := hs'.le.trans (shrinkingBump_rOut_le n)
        have hny : ‖y‖≤R+2 := by
          have ht := norm_sub_le x (x-y)
          rw [sub_sub_cancel] at ht
          linarith
        exact mul_le_mul_of_nonneg_left (hy hny) (smoothKernel_nonneg n (x-y))
    _ = C := by
      rw [integral_mul_const,integral_sub_left_eq_self,smoothKernel_integral,one_mul]

theorem compact_pairing_mollify_tendsto {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {T : E → E} (he : T =ᵐ[volume] gradient φ)
    {B : E → E} (hB : Continuous B) (hBc : HasCompactSupport B) :
    Tendsto (fun n => ∫ x,⟪B x,mollify n T x⟫) atTop (𝓝 (∫ x,⟪B x,T x⟫)) := by
  have hT := (convex_gradient_locallyIntegrable hφ).congr he.symm
  obtain ⟨R,hR⟩ := hBc.isCompact.isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := convex_gradient_bound_ball hφ (R+2)
  have hbound : ∀ᵐ y ∂volume,‖y‖≤R+2 → ‖T y‖≤(C:ℝ) := by
    filter_upwards [he] with y hy
    rw [hy]
    exact hC y
  apply tendsto_integral_of_dominated_convergence (fun x => ‖B x‖*(C:ℝ))
    (fun n => (hB.inner (mollify_contDiff hT n).continuous).aestronglyMeasurable)
    ((hB.integrable_of_hasCompactSupport hBc).norm.mul_const _)
  · intro n
    filter_upwards with x
    by_cases hx : x∈tsupport B
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (norm_mollify_le hT C.coe_nonneg hbound n (hR x hx))
          (norm_nonneg _))
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp only [hz,inner_zero_left,norm_zero,zero_mul,le_refl]
  · filter_upwards [mollify_tendsto_ae hT] with x hx
    exact tendsto_const_nhds.inner hx

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.compact_pairing_mollify_tendsto
