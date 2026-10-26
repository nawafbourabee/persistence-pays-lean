import PersistencePays.OptimalPlanExistence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Weak convergence and convergence of a continuous dominating moment imply
convergence of its continuous dominated observables. This is proved directly
from lower semicontinuity of the two nonnegative functions `g ± f`; no uniform
integrability or Wasserstein convergence hypothesis is assumed. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Filter Topology
open scoped ENNReal
variable {S ι : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  {l : Filter ι} {μs : ι → ProbabilityMeasure S} {μ : ProbabilityMeasure S}

lemma weak_eventually_integral_gt (hweak : Tendsto μs l (𝓝 μ))
    {f : S → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ i, Integrable f (μs i : Measure S))
    (hfμ : Integrable f (μ : Measure S))
    {a : ℝ} (ha : a < ∫ x, f x ∂(μ : Measure S)) :
    ∀ᶠ i in l, a < ∫ x, f x ∂(μs i : Measure S) := by
  by_cases ha0 : 0 ≤ a
  · have heq := ofReal_integral_eq_lintegral_ofReal hfμ (.of_forall hf0)
    have ht : ENNReal.ofReal a < ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure S) := by
      rw [← heq]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).2 ha
    have he := hweak.eventually
      ((QuadraticTransport.cost_lowerSemicontinuous f hf) μ _ ht)
    filter_upwards [he] with i hi
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi i) (.of_forall hf0)] at hi
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).1 hi
  · exact .of_forall (fun i => lt_of_lt_of_le (lt_of_not_ge ha0)
      (integral_nonneg hf0))

theorem weak_integral_tendsto_of_continuous_dominator
    (hweak : Tendsto μs l (𝓝 μ)) {f g : S → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hbound : ∀ x, ‖f x‖ ≤ g x)
    (hgi : ∀ i, Integrable g (μs i : Measure S))
    (hgμ : Integrable g (μ : Measure S))
    (hgm : Tendsto (fun i => ∫ x, g x ∂(μs i : Measure S)) l
      (𝓝 (∫ x, g x ∂(μ : Measure S)))) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure S)) l
      (𝓝 (∫ x, f x ∂(μ : Measure S))) := by
  have hfi : ∀ i, Integrable f (μs i : Measure S) := fun i =>
    (hgi i).mono' hf.aestronglyMeasurable (.of_forall hbound)
  have hfμ : Integrable f (μ : Measure S) :=
    hgμ.mono' hf.aestronglyMeasurable (.of_forall hbound)
  have hplus : ∀ x, 0 ≤ g x + f x := by
    intro x
    have h := hbound x
    rw [Real.norm_eq_abs] at h
    have hh := (abs_le.mp h).1
    linarith
  have hminus : ∀ x, 0 ≤ g x - f x := by
    intro x
    have h := hbound x
    rw [Real.norm_eq_abs] at h
    have hh := (abs_le.mp h).2
    linarith
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hp := weak_eventually_integral_gt hweak (hg.add hf) hplus
    (fun i => (hgi i).add (hfi i)) (hgμ.add hfμ)
    (a := (∫ x, g x ∂(μ : Measure S))+(∫ x, f x ∂(μ : Measure S))-ε/2)
    (by simp only [Pi.add_apply]; rw [integral_add hgμ hfμ]; linarith)
  have hn := weak_eventually_integral_gt hweak (hg.sub hf) hminus
    (fun i => (hgi i).sub (hfi i)) (hgμ.sub hfμ)
    (a := (∫ x, g x ∂(μ : Measure S))-(∫ x, f x ∂(μ : Measure S))-ε/2)
    (by simp only [Pi.sub_apply]; rw [integral_sub hgμ hfμ]; linarith)
  have hm := hgm.eventually (gt_mem_nhds
    (show (∫ x, g x ∂(μ : Measure S)) < (∫ x, g x ∂(μ : Measure S))+ε/2 by linarith))
  filter_upwards [hp, hn, hm] with i hi hj hk
  simp only [Pi.add_apply] at hi
  simp only [Pi.sub_apply] at hj
  rw [integral_add (hgi i) (hfi i)] at hi
  rw [integral_sub (hgi i) (hfi i)] at hj
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem weak_integral_tendsto_of_moment
    (hweak : Tendsto μs l (𝓝 μ)) {f w : S → ℝ}
    (hf : Continuous f) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C*(1+w x))
    (hwi : ∀ i, Integrable w (μs i : Measure S))
    (hwμ : Integrable w (μ : Measure S))
    (hwm : Tendsto (fun i => ∫ x, w x ∂(μs i : Measure S)) l
      (𝓝 (∫ x, w x ∂(μ : Measure S)))) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure S)) l
      (𝓝 (∫ x, f x ∂(μ : Measure S))) := by
  apply weak_integral_tendsto_of_continuous_dominator hweak hf
    (continuous_const.mul (continuous_const.add hw)) hbound
    (fun i => ((integrable_const 1).add (hwi i)).const_mul C)
    (((integrable_const 1).add hwμ).const_mul C)
  have heq : ∀ (ν : ProbabilityMeasure S), Integrable w (ν : Measure S) →
      (∫ x, C*(1+w x) ∂(ν : Measure S)) = C*(1+∫ x, w x ∂(ν : Measure S)) := by
    intro ν hi
    rw [integral_const_mul, integral_add (integrable_const 1) hi]
    simp
  simp only [Pi.mul_apply, Pi.add_apply]
  simpa only [heq _ (hwi _), heq _ hwμ] using
    (tendsto_const_nhds.mul (tendsto_const_nhds.add hwm) :
      Tendsto (fun i => C*(1+∫ x, w x ∂(μs i : Measure S))) l
        (𝓝 (C*(1+∫ x, w x ∂(μ : Measure S)))))

end PersistencePays
#print axioms PersistencePays.weak_integral_tendsto_of_continuous_dominator
#print axioms PersistencePays.weak_integral_tendsto_of_moment
