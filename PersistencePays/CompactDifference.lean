import PersistencePays.ConvexHessian
import PersistencePays.CyclicGraph
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Group.Integral

/-! Compact test functions allow finite-difference integration by parts with
only local integrability of the other factor. No translated Gibbs moments are
assumed. -/
open Set Filter MeasureTheory Metric
open scoped Topology RealInnerProductSpace NNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_compact_difference_tendsto {w f : E → ℝ} {C : ℝ≥0}
    (hw : LipschitzWith C w) (hwc : HasCompactSupport w)
    (hwd : Differentiable ℝ w) (hf : LocallyIntegrable f volume) (v : E) :
    Tendsto (fun t : ℝ => ∫ x, (t⁻¹*(w (x+t•v)-w x))*f x)
      (𝓝[>] 0) (𝓝 (∫ x,(fderiv ℝ w x v)*f x)) := by
  let K := cthickening ‖v‖ (tsupport w)
  have hK : IsCompact K := hwc.isCompact.cthickening
  apply tendsto_integral_filter_of_dominated_convergence
    (K.indicator (fun x => ((C:ℝ)*‖v‖)*‖f x‖))
  · filter_upwards with t
    exact (aestronglyMeasurable_const.mul
      ((hw.continuous.measurable.comp (measurable_id.add_const _)).aestronglyMeasurable.sub
        hw.continuous.aestronglyMeasurable)).mul hf.aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      calc
        ‖(t⁻¹*(w (x+t•v)-w x))*f x‖ =
            (t⁻¹*‖w (x+t•v)-w x‖)*‖f x‖ := by
          simp [norm_mul,ht.1.le]
        _ ≤ (t⁻¹*((C:ℝ)*‖(x+t•v)-x‖))*‖f x‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hw.norm_sub_le _ _) (inv_nonneg.mpr ht.1.le))
            (norm_nonneg _)
        _ = ((C:ℝ)*‖v‖)*‖f x‖ := by
          simp [field,norm_smul,abs_of_pos ht.1,ht.1.ne']
    · have A : w x=0 := by
        rw [← Function.notMem_support]
        contrapose hx
        exact self_subset_cthickening _ (subset_tsupport _ hx)
      have B : w (x+t•v)=0 := by
        rw [← Function.notMem_support]
        contrapose hx
        apply mem_cthickening_of_dist_le _ _ ‖v‖ (tsupport w) (subset_tsupport _ hx)
        simp only [dist_eq_norm,sub_add_cancel_left,norm_neg,norm_smul,
          Real.norm_eq_abs,abs_of_pos ht.1]
        exact mul_le_of_le_one_left (norm_nonneg v) ht.2
      simp only [B,A,sub_self,mul_zero,zero_mul,norm_zero]
      exact indicator_nonneg (fun y _ => by positivity) _
  · rw [integrable_indicator_iff hK.measurableSet]
    exact ((hf.integrableOn_isCompact hK).norm.const_mul _)
  · filter_upwards with x
    have hd : HasDerivAt (fun t : ℝ => w (x+t•v)) (fderiv ℝ w x v) 0 := by
      have hl : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
        have hh := (hasDerivAt_const (0:ℝ) x).add
          ((hasDerivAt_id (0:ℝ)).smul_const v)
        change HasDerivAt (fun t : ℝ => x+t•v) (0+(1:ℝ)•v) 0 at hh
        simpa only [zero_add,one_smul] using hh
      have hh : HasFDerivAt w (fderiv ℝ w x) (x+(0:ℝ)•v) := by
        simpa only [zero_smul,add_zero] using (hwd x).hasFDerivAt
      exact hh.comp_hasDerivAt 0 hl
    simpa [smul_eq_mul] using hd.tendsto_slope_zero_right.mul_const (f x)

theorem compact_difference_integration_by_parts {w f : E → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hf : LocallyIntegrable f volume) (a : E) :
    Integrable (fun x => (f (x+a)-f x)*w x) volume ∧
    (∫ x,(f (x+a)-f x)*w x) = ∫ x,(w (x-a)-w x)*f x := by
  have hi : Integrable (fun x => w x*f x) volume :=
    hf.integrable_smul_left_of_hasCompactSupport hw hwc
  have hcw : HasCompactSupport (fun x => w (x-a)) := by
    have hh := hwc.comp_homeomorph (Homeomorph.addRight (-a))
    change HasCompactSupport (fun x => w (x+ -a)) at hh
    simpa only [sub_eq_add_neg] using hh
  have hi' : Integrable (fun x => w (x-a)*f x) volume := by
    exact hf.integrable_smul_left_of_hasCompactSupport
      (show Continuous (fun x => w (x-a)) from hw.comp (continuous_id.sub continuous_const)) hcw
  have hit : Integrable (fun x => w x*f (x+a)) volume := by
    have hh := (measurePreserving_add_right volume a).integrable_comp_of_integrable hi'
    simpa only [Function.comp_def,add_sub_cancel_right] using hh
  have he : (∫ x,w x*f (x+a)) = ∫ x,w (x-a)*f x := by
    simpa using (integral_add_right_eq_self (fun x => w (x-a)*f x) a)
  refine ⟨(hit.sub hi).congr (by filter_upwards with x; dsimp; ring),?_⟩
  calc
    _ = ∫ x,(w x*f (x+a)-w x*f x) := by apply integral_congr_ae; filter_upwards with x; ring
    _ = (∫ x,w x*f (x+a))-(∫ x,w x*f x) := integral_sub hit hi
    _ = (∫ x,w (x-a)*f x)-(∫ x,w x*f x) := by rw [he]
    _ = _ := by rw [← integral_sub hi' hi]; apply integral_congr_ae; filter_upwards with x; ring

theorem directional_quotient_tendsto {T : E → E} {G : E →L[ℝ] E}
    {s : Set E} {x v : E} (hT : HasFDerivWithinAt T G s x)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n,a n≠0)
    (hs : ∀ n,x+a n•v∈s) :
    Tendsto (fun n => (a n)⁻¹ • (T (x+a n•v)-T x)) atTop (𝓝 (G v)) := by
  let D : Set ℝ := {t | x+t•v∈s}
  have hl : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    have hh := (hasDerivAt_const (0:ℝ) x).add
      ((hasDerivAt_id (0:ℝ)).smul_const v)
    change HasDerivAt (fun t : ℝ => x+t•v) (0+(1:ℝ)•v) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hd : HasDerivWithinAt (fun t : ℝ => T (x+t•v)) (G v) D 0 := by
    have hT' : HasFDerivWithinAt T G s (x+(0:ℝ)•v) := by simpa using hT
    exact hT'.comp_hasDerivWithinAt 0 hl.hasDerivWithinAt (fun _ ht => ht)
  have ht : Tendsto a atTop (𝓝[D\{0}] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha,.of_forall (fun n => ⟨hs n,ha0 n⟩)⟩
  simpa [slope,Function.comp_def] using
    (hasDerivWithinAt_iff_tendsto_slope.mp hd).comp ht

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.integral_compact_difference_tendsto
