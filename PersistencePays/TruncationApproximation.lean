import PersistencePays.ConditionalLawEntropy
import PersistencePays.QuadraticTransport
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual normalized restrictions, with weak, moment and entropy convergence.
The sets exhaust almost everywhere; no convergence of the conditional laws is assumed. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {S : Type*} [MeasurableSpace S]

def conditionedProbability (μ : ProbabilityMeasure S) (A : Set S)
    (hpos : (μ : Measure S) A ≠ 0) : ProbabilityMeasure S :=
  ⟨ProbabilityTheory.cond (μ : Measure S) A,cond_isProbabilityMeasure hpos⟩

@[simp] theorem conditionedProbability_coe (μ : ProbabilityMeasure S) (A : Set S)
    (hpos : (μ : Measure S) A ≠ 0) :
    (conditionedProbability μ A hpos : Measure S) = ProbabilityTheory.cond (μ : Measure S) A := rfl

theorem conditionedProbability_integral (μ : ProbabilityMeasure S) (A : Set S)
    (hpos : (μ : Measure S) A ≠ 0) (f : S → ℝ) :
    (∫ x, f x ∂(conditionedProbability μ A hpos : Measure S)) =
      ((μ : Measure S) A).toReal⁻¹ * ∫ x in A, f x ∂(μ : Measure S) := by
  simp only [conditionedProbability_coe, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul]

theorem integrable_conditionedProbability (μ : ProbabilityMeasure S) (A : Set S)
    (hpos : (μ : Measure S) A ≠ 0) {f : S → ℝ} (hf : Integrable f (μ : Measure S)) :
    Integrable f (conditionedProbability μ A hpos : Measure S) :=
  hf.restrict.smul_measure (by simp [hpos])

theorem memLp_conditionedProbability {F : Type*} [NormedAddCommGroup F]
    (μ : ProbabilityMeasure S) (A : Set S) (hpos : (μ : Measure S) A ≠ 0)
    {f : S → F} {p : ℝ≥0∞} (hf : MemLp f p (μ : Measure S)) :
    MemLp f p (conditionedProbability μ A hpos : Measure S) :=
  (hf.restrict A).smul_measure (by simp [hpos])

theorem exhausting_set_integral_tendsto (μ : Measure S) (A : ℕ → Set S)
    (hA : ∀ n, MeasurableSet (A n))
    (hex : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ A n)
    {f : S → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x in A n, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  simp_rw [← integral_indicator (hA _)]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => hf.aestronglyMeasurable.indicator (hA n)) hf.norm
  · intro n
    exact Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _)
  · filter_upwards [hex] with x hx
    apply tendsto_const_nhds.congr'
    exact hx.mono (fun n hn => (indicator_of_mem hn f).symm)

theorem exhausting_set_mass_tendsto (μ : ProbabilityMeasure S) (A : ℕ → Set S)
    (hA : ∀ n, MeasurableSet (A n))
    (hex : ∀ᵐ x ∂(μ : Measure S), ∀ᶠ n in atTop, x ∈ A n) :
    Tendsto (fun n => ((μ : Measure S) (A n)).toReal) atTop (𝓝 1) := by
  have hh := exhausting_set_integral_tendsto (μ : Measure S) A hA hex (integrable_const (1:ℝ))
  simpa only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, mul_one, measure_univ, ENNReal.toReal_one] using hh

theorem conditioned_integral_tendsto (μ : ProbabilityMeasure S) (A : ℕ → Set S)
    (hA : ∀ n, MeasurableSet (A n))
    (hpos : ∀ n, (μ : Measure S) (A n) ≠ 0)
    (hex : ∀ᵐ x ∂(μ : Measure S), ∀ᶠ n in atTop, x ∈ A n)
    {f : S → ℝ} (hf : Integrable f (μ : Measure S)) :
    Tendsto (fun n => ∫ x, f x ∂(conditionedProbability μ (A n) (hpos n) : Measure S))
      atTop (𝓝 (∫ x, f x ∂(μ : Measure S))) := by
  simp_rw [conditionedProbability_integral]
  have hh := ((exhausting_set_mass_tendsto μ A hA hex).inv₀ (by norm_num)).mul
    (exhausting_set_integral_tendsto (μ : Measure S) A hA hex hf)
  simpa using hh

theorem conditioned_klDiv_tendsto (μ ν : ProbabilityMeasure S) (A : ℕ → Set S)
    (hA : ∀ n, MeasurableSet (A n))
    (hpos : ∀ n, (μ : Measure S) (A n) ≠ 0)
    (hex : ∀ᵐ x ∂(μ : Measure S), ∀ᶠ n in atTop, x ∈ A n)
    (hK : klDiv (μ : Measure S) (ν : Measure S) ≠ ∞) :
    Tendsto (fun n => (klDiv (conditionedProbability μ (A n) (hpos n) : Measure S)
      (ν : Measure S)).toReal) atTop (𝓝 (klDiv (μ : Measure S) (ν : Measure S)).toReal) := by
  have hm := exhausting_set_mass_tendsto μ A hA hex
  have hi := exhausting_set_integral_tendsto (μ : Measure S) A hA hex (klDiv_ne_top_iff.mp hK).2
  have hlog := Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0) |>.tendsto.comp hm
  have he (n : ℕ) : (klDiv (conditionedProbability μ (A n) (hpos n) : Measure S)
      (ν : Measure S)).toReal =
      ((μ : Measure S) (A n)).toReal⁻¹*(∫ x in A n, llr (μ : Measure S) (ν : Measure S) x ∂(μ : Measure S))-
        Real.log (((μ : Measure S) (A n)).toReal) := by
    have hh := (conditional_klDiv (μ : Measure S) (ν : Measure S) hK (A n) (hA n) (hpos n)).2
    have hp : ((μ : Measure S) (A n)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hpos n,measure_ne_top _ _⟩
    change _ = _ at hh
    apply mul_left_cancel₀ hp
    rw [conditionedProbability_coe, hh]
    field_simp
  simp_rw [he]
  have hh := ((hm.inv₀ (by norm_num)).mul hi).sub hlog
  rw [toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp hK).1 (by simp)]
  simpa using hh

section Topology
variable [TopologicalSpace S] [BorelSpace S]

theorem conditionedProbability_tendsto (μ : ProbabilityMeasure S) (A : ℕ → Set S)
    (hA : ∀ n, MeasurableSet (A n))
    (hpos : ∀ n, (μ : Measure S) (A n) ≠ 0)
    (hex : ∀ᵐ x ∂(μ : Measure S), ∀ᶠ n in atTop, x ∈ A n) :
    Tendsto (fun n => conditionedProbability μ (A n) (hpos n)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact conditioned_integral_tendsto μ A hA hpos hex (f.integrable (μ := (μ : Measure S)))

end Topology
end PersistencePays
#print axioms PersistencePays.conditionedProbability_tendsto
#print axioms PersistencePays.conditioned_klDiv_tendsto
