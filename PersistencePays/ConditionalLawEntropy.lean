import PersistencePays.ConditionalEntropy
import Mathlib.Probability.ConditionalProbability

/-! Exact entropy of a probability law conditioned on a measurable event. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem llr_restrict_left_ae (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (A : Set S) (hA : MeasurableSet A) :
    llr (μ.restrict A) ν =ᵐ[μ.restrict A] llr μ ν := by
  have ha : μ.restrict A ≪ ν := (Measure.restrict_le_self.absolutelyContinuous).trans hac
  filter_upwards [ha.ae_le (Measure.rnDeriv_restrict μ ν hA), ae_restrict_mem hA] with x hx hxA
  simp only [llr_def, hx, indicator_of_mem hxA]

theorem llr_cond_ae (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (A : Set S) (hA : MeasurableSet A) (hpos : μ A ≠ 0) :
    llr (cond μ A) ν =ᵐ[cond μ A] fun x => llr μ ν x - Real.log ((μ A).toReal) := by
  have ha : μ.restrict A ≪ ν := (Measure.restrict_le_self.absolutelyContinuous).trans hac
  have hs := llr_smul_left ha (μ A)⁻¹ (by simp [measure_ne_top μ A]) (by simp [hpos])
  have hr := llr_restrict_left_ae μ ν hac A hA
  have he : llr (cond μ A) ν =ᵐ[μ.restrict A] fun x => llr μ ν x-Real.log ((μ A).toReal) := by
    filter_upwards [hs,hr] with x hx hrx
    simpa only [ProbabilityTheory.cond, hrx, ENNReal.toReal_inv, Real.log_inv, sub_eq_add_neg] using hx
  have hsm : ProbabilityTheory.cond μ A ≪ μ.restrict A :=
    (Measure.AbsolutelyContinuous.refl (μ.restrict A)).smul_left _
  exact hsm.ae_le he

/-- Finiteness after conditioning is proved, rather than assumed. -/
theorem conditional_klDiv (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A) (hpos : μ A ≠ 0) :
    klDiv (cond μ A) ν ≠ ∞ ∧
      (μ A).toReal * (klDiv (cond μ A) ν).toReal =
        (∫ x in A, llr μ ν x ∂μ) - (μ A).toReal*Real.log ((μ A).toReal) := by
  letI : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure hpos
  have hac := (klDiv_ne_top_iff.mp hD).1
  have hi := (klDiv_ne_top_iff.mp hD).2
  have hca : cond μ A ≪ ν :=
    ((Measure.restrict_le_self.absolutelyContinuous).trans hac).smul_left _
  have hcondi : Integrable (llr μ ν) (cond μ A) :=
    hi.restrict.smul_measure (by simp [hpos])
  have hlog := llr_cond_ae μ ν hac A hA hpos
  have hlogi : Integrable (llr (cond μ A) ν) (cond μ A) :=
    (hcondi.sub (integrable_const _)).congr hlog.symm
  refine ⟨klDiv_ne_top hca hlogi, ?_⟩
  rw [toReal_klDiv_of_measure_eq hca (by simp), integral_congr_ae hlog,
    integral_sub hcondi (integrable_const _), integral_const, probReal_univ, one_smul]
  have hm : (μ A).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top μ A⟩
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  field_simp
  <;> ring

/-- The entropy cost of recording a two-set partition is exactly the binary entropy. -/
theorem conditional_klDiv_partition (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A)
    (hpos : μ A ≠ 0) (hcomp : μ Aᶜ ≠ 0) :
    (μ A).toReal*(klDiv (cond μ A) ν).toReal+
      (μ Aᶜ).toReal*(klDiv (cond μ Aᶜ) ν).toReal =
      (klDiv μ ν).toReal-
        (μ A).toReal*Real.log ((μ A).toReal)-
        (μ Aᶜ).toReal*Real.log ((μ Aᶜ).toReal) := by
  rw [(conditional_klDiv μ ν hD A hA hpos).2,
    (conditional_klDiv μ ν hD Aᶜ hA.compl hcomp).2,
    toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp hD).1 (by simp)]
  have hi := integral_add_compl hA (klDiv_ne_top_iff.mp hD).2
  linarith


theorem conditional_klDiv_self (μ : Measure S) [IsProbabilityMeasure μ]
    (A : Set S) (hA : MeasurableSet A) (hpos : μ A ≠ 0) :
    klDiv (ProbabilityTheory.cond μ A) μ ≠ ∞ ∧
      (klDiv (ProbabilityTheory.cond μ A) μ).toReal = -Real.log ((μ A).toReal) := by
  have hh := conditional_klDiv μ μ (by simp) A hA hpos
  have hz : (∫ x in A, llr μ μ x ∂μ) = 0 := by
    rw [integral_congr_ae (Measure.restrict_le_self.absolutelyContinuous.ae_le (llr_self μ))]
    simp
  rw [hz] at hh
  refine ⟨hh.1, ?_⟩
  have hm : (μ A).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top μ A⟩
  apply mul_left_cancel₀ hm
  linarith [hh.2]

theorem probability_complement_toReal (μ : Measure S) [IsProbabilityMeasure μ]
    (A : Set S) (hA : MeasurableSet A) : (μ Aᶜ).toReal = 1-(μ A).toReal := by
  have hh := congrArg ENNReal.toReal (measure_add_measure_compl hA (μ:=μ))
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), measure_univ,
    ENNReal.toReal_one] at hh
  linarith

end PersistencePays
#print axioms PersistencePays.conditional_klDiv_partition
