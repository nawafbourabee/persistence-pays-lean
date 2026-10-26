import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! Removing compact cutoffs from a one-sided nonnegative integral estimate.
Fatou proves global integrability; it is not a premise. This retains the
favorable sign of a distributional Hessian when passing to the full space. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Filter Topology
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

theorem nonnegative_fatou_integral_bound {f : S → ℝ} {fn : ℕ → S → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ᵐ x ∂μ,0≤f x)
    (hfn : ∀ n, Integrable (fn n) μ) (hfn0 : ∀ n,∀ᵐ x ∂μ,0≤fn n x)
    (hlim : ∀ᵐ x ∂μ,Tendsto (fun n => fn n x) atTop (𝓝 (f x)))
    {b : ℕ → ℝ} {B : ℝ} (hb : ∀ n,(∫ x,fn n x ∂μ)≤b n)
    (hB : Tendsto b atTop (𝓝 B)) : Integrable f μ ∧ (∫ x,f x ∂μ)≤B := by
  have hBn : 0≤B := ge_of_tendsto hB (.of_forall (fun n =>
    (integral_nonneg_of_ae (hfn0 n)).trans (hb n)))
  have hfat := lintegral_liminf_le' (μ:=μ) (u:=atTop)
    (fun n => (hfn n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have he : (∫⁻ x,liminf (fun n => ENNReal.ofReal (fn n x)) atTop ∂μ) =
      ∫⁻ x,ENNReal.ofReal (f x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hlim] with x hx
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq
  rw [he] at hfat
  have hmono : liminf (fun n => ∫⁻ x,ENNReal.ofReal (fn n x) ∂μ) atTop ≤
      liminf (fun n => ENNReal.ofReal (b n)) atTop := by
    exact liminf_le_liminf (Filter.Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hfn n) (hfn0 n)]
      exact ENNReal.ofReal_le_ofReal (hb n)))
  have hlast := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hB).liminf_eq
  have hfin : ∫⁻ x,ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal B :=
    hfat.trans (hmono.trans_eq hlast)
  have hi := (lintegral_ofReal_ne_top_iff_integrable hf hf0).mp
    (ne_of_lt (hfin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hf0] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff hBn).mp hfin

theorem integral_bound_of_cutoffs {a b : S → ℝ} {χ : ℕ → S → ℝ}
    (ha : AEStronglyMeasurable a μ) (ha0 : ∀ᵐ x ∂μ,0≤a x)
    (hb : Integrable b μ) (hχ : ∀ n,AEStronglyMeasurable (χ n) μ)
    (hχ01 : ∀ n,∀ᵐ x ∂μ,χ n x∈Set.Icc (0:ℝ) 1)
    (hχlim : ∀ᵐ x ∂μ,Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hi : ∀ n,Integrable (fun x => χ n x*a x) μ)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hloc : ∀ n,(∫ x,χ n x*a x ∂μ)≤(∫ x,χ n x*b x ∂μ)+e n) :
    Integrable a μ ∧ (∫ x,a x ∂μ)≤∫ x,b x ∂μ := by
  have hdom : Tendsto (fun n => ∫ x,χ n x*b x ∂μ) atTop (𝓝 (∫ x,b x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖b x‖)
      (fun n => (hχ n).mul hb.aestronglyMeasurable) hb.norm
    · intro n
      filter_upwards [hχ01 n] with x hx
      simp only [Pi.mul_apply]
      rw [norm_mul,Real.norm_of_nonneg hx.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hx.2
    · filter_upwards [hχlim] with x hx
      simpa only [one_mul,Pi.mul_apply] using hx.mul_const (b x)
  apply nonnegative_fatou_integral_bound ha ha0 hi
    (fun n => (hχ01 n).and ha0 |>.mono (fun _ hx => mul_nonneg hx.1.1 hx.2))
    _ hloc
  · simpa only [add_zero] using hdom.add he
  · filter_upwards [hχlim] with x hx
    simpa only [one_mul] using hx.mul_const (a x)

end PersistencePays
#print axioms PersistencePays.nonnegative_fatou_integral_bound
#print axioms PersistencePays.integral_bound_of_cutoffs
