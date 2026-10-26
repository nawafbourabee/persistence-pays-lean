import PersistencePays.QuadraticTransport
import Mathlib.MeasureTheory.Constructions.Pi

/-! Finite uniform mixtures of measurable pushforwards. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory Set
open scoped ENNReal
variable {ι Ω S T : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

def averageMap (μ : Measure Ω) (F : ι → Ω → S) : Measure S :=
  ((Fintype.card ι : ℝ≥0∞)⁻¹) • ∑ i, μ.map (F i)

theorem averageMap_apply (μ : Measure Ω) (F : ι → Ω → S)
    (hF : ∀ i, Measurable (F i)) (A : Set S) (hA : MeasurableSet A) :
    averageMap μ F A = ((Fintype.card ι : ℝ≥0∞)⁻¹) * ∑ i, μ ((F i) ⁻¹' A) := by
  simp only [averageMap, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    Measure.map_apply (hF _) hA]

theorem averageMap_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ι → Ω → S) (hF : ∀ i, Measurable (F i)) : IsProbabilityMeasure (averageMap μ F) := by
  constructor
  rw [averageMap_apply μ F hF univ MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

theorem averageMap_map (μ : Measure Ω) (F : ι → Ω → S) (hF : ∀ i, Measurable (F i))
    (g : S → T) (hg : Measurable g) :
    (averageMap μ F).map g = averageMap μ (fun i => g ∘ F i) := by
  ext A hA
  rw [Measure.map_apply hg hA,
    averageMap_apply μ F hF _ (hg hA), averageMap_apply μ _ (fun i => hg.comp (hF i)) _ hA]
  rfl

theorem averageMap_eq_of_measure_preserving (μ : Measure Ω) (ν : Measure S)
    (F : ι → Ω → S) (hF : ∀ i, MeasurePreserving (F i) μ ν) : averageMap μ F = ν := by
  have hc : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext A hA
  rw [averageMap_apply μ F (fun i => (hF i).measurable) A hA]
  simp_rw [← Measure.map_apply (hF _).measurable hA, (hF _).map_eq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc (by simp), one_mul]

theorem averageMap_lintegral (μ : Measure Ω) (F : ι → Ω → S) (hF : ∀ i, Measurable (F i))
    (f : S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂averageMap μ F) = ((Fintype.card ι : ℝ≥0∞)⁻¹)*
      ∫⁻ x, ∑ i, f (F i x) ∂μ := by
  simp only [averageMap, lintegral_smul_measure, smul_eq_mul, lintegral_finsetSum_measure]
  simp_rw [lintegral_map hf (hF _)]
  rw [lintegral_finsetSum (f:=fun i x => f (F i x)) Finset.univ (fun i _ => hf.comp (hF i))]


theorem averageMap_eq_of_sum (μ : Measure Ω) (F G : ι → Ω → S)
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (he : ∀ (φ : S → ℝ≥0∞) (x : Ω), ∑ i, φ (F i x) = ∑ i, φ (G i x)) :
    averageMap μ F = averageMap μ G := by
  ext A hA
  have hφ : Measurable (A.indicator (1 : S → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    averageMap_lintegral μ F hF _ hφ, averageMap_lintegral μ G hG _ hφ]
  congr 1
  exact lintegral_congr (he _)

end PersistencePays.QuadraticTransport
