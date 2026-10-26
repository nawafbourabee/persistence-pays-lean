import PersistencePays.EntropyDual
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Continuous bounded approximation for entropy-dual tests. -/
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace PersistencePays
noncomputable section

lemma exp_abs_sub_le {x y C : ℝ} (hx : x ≤ C) (hy : y ≤ C) :
    |exp x-exp y| ≤ exp C * |x-y| := by
  wlog hxy : x ≤ y generalizing x y
  · have hh := this hy hx (le_of_not_ge hxy)
    simpa only [abs_sub_comm] using hh
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (x-y)) (exp_pos y).le
  have he : exp y * exp (x-y) = exp x := by rw [← exp_add]; congr 1; ring
  rw [he] at h
  have hmul := mul_le_mul_of_nonneg_right (exp_le_exp.mpr hy) (sub_nonneg.mpr hxy)
  rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_exp.mpr hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
  nlinarith

def realClip (C x : ℝ) : ℝ := max (-C) (min C x)

lemma realClip_bounds {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : -C ≤ realClip C x ∧ realClip C x ≤ C :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma realClip_error {C x : ℝ} (hx : |x| ≤ C) (y : ℝ) :
    |x-realClip C y| ≤ |x-y| := by
  have hb := abs_le.mp hx
  have hC : 0 ≤ C := (abs_nonneg x).trans hx
  by_cases hy : y < -C
  · have hc : realClip C y = -C := by
      unfold realClip
      rw [min_eq_right (by linarith), max_eq_left hy.le]
    rw [hc, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · by_cases hy' : C < y
    · have hc : realClip C y = C := by unfold realClip; rw [min_eq_left hy'.le, max_eq_right (by linarith)]
      rw [hc, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · simp only [realClip, min_eq_right (le_of_not_gt hy'), max_eq_right (le_of_not_gt hy)]
      exact le_rfl

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

lemma boundedContinuous_isBoundedMeasurable (f : S →ᵇ ℝ) : IsBoundedMeasurable f :=
  ⟨f.continuous.measurable, ‖f‖, fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩

def clippedContinuous (C : ℝ) (hC : 0 ≤ C) (g : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => realClip C (g x))
    (continuous_const.max (continuous_const.min g.continuous)) C
    (fun x => by rw [Real.norm_eq_abs]; exact abs_le.mpr (realClip_bounds hC _))

def expBoundedContinuous (g : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => exp (g x))
    (continuous_exp.comp g.continuous) (exp ‖g‖)
    (fun x => by rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)];
                 exact exp_le_exp.mpr ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)))

/-- Every bounded measurable dual test can be approximated from below in its
value by a bounded continuous test, simultaneously for both measures. -/
theorem entropyDual_continuous_approx [NormalSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [(μ+ν).WeaklyRegular] {f : S → ℝ} (hf : IsBoundedMeasurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : S →ᵇ ℝ, entropyDual μ ν f ≤ entropyDual μ ν g + ε := by
  obtain ⟨C,hC⟩ := hf.2
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x₀)
  let δ := ε / (1 + exp C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g,hg,hgi⟩ := (hf.integrable (μ+ν)).exists_boundedContinuous_integral_sub_le hδ
  let k := clippedContinuous C hC0 g
  have hk := boundedContinuous_isBoundedMeasurable k
  have hke (x : S) : |f x-k x| ≤ |f x-g x| := realClip_error (hC x) (g x)
  have hki (x : S) : |k x| ≤ C := abs_le.mpr (realClip_bounds hC0 _)
  have hsum : (∫ x, |f x-k x| ∂(μ+ν)) ≤ δ := by
    have hm := integral_mono ((hf.integrable (μ+ν)).sub (hk.integrable (μ+ν))).norm
      ((hf.integrable (μ+ν)).sub hgi).norm (fun x => hke x)
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hm.trans hg
  have heiμ : Integrable (fun x => |f x-k x|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hf.integrable μ).sub (hk.integrable μ)).norm
  have heiν : Integrable (fun x => |f x-k x|) ν := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hf.integrable ν).sub (hk.integrable ν)).norm
  rw [integral_add_measure heiμ heiν] at hsum
  have hμ0 : 0 ≤ ∫ x, |f x-k x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have hν0 : 0 ≤ ∫ x, |f x-k x| ∂ν := integral_nonneg (fun _ => abs_nonneg _)
  have hm : (∫ x, f x ∂μ) - (∫ x, k x ∂μ) ≤ ∫ x, |f x-k x| ∂μ := by
    rw [← integral_sub (hf.integrable μ) (hk.integrable μ)]
    exact (le_abs_self _).trans abs_integral_le_integral_abs
  have hex : (∫ x, exp (k x) ∂ν) - (∫ x, exp (f x) ∂ν) ≤
      exp C * (∫ x, |f x-k x| ∂ν) := by
    have ha : (∫ x, exp (k x) ∂ν) - (∫ x, exp (f x) ∂ν) ≤
        ∫ x, |exp (k x)-exp (f x)| ∂ν := by
      rw [← integral_sub (hk.exp_integrable ν) (hf.exp_integrable ν)]
      exact (le_abs_self _).trans abs_integral_le_integral_abs
    have hi : Integrable (fun x => |exp (k x)-exp (f x)|) ν :=
      ((hk.exp_integrable ν).sub (hf.exp_integrable ν)).norm
    have hj : Integrable (fun x => exp C * |f x-k x|) ν :=
      (((hf.integrable ν).sub (hk.integrable ν)).norm).const_mul _
    have hb := integral_mono hi hj (fun x => by
      simpa only [abs_sub_comm (k x) (f x)] using
        exp_abs_sub_le ((le_abs_self _).trans (hki x)) ((le_abs_self _).trans (hC x)))
    exact ha.trans (by simpa only [integral_const_mul] using hb)
  refine ⟨k, ?_⟩
  have heq : (1+exp C)*δ = ε := by dsimp [δ]; field_simp
  unfold entropyDual
  have h1 : (∫ x, |f x-k x| ∂μ) ≤ δ := by linarith
  have h2 : (∫ x, |f x-k x| ∂ν) ≤ δ := by linarith
  nlinarith [exp_pos C]

end
end PersistencePays
#print axioms PersistencePays.exp_abs_sub_le

#print axioms PersistencePays.entropyDual_continuous_approx
