import PersistencePays.DensityEntropy
import SLT.GaussianLSI.Entropy

/-! The entropy used by the checked tensorization library is identified with
actual relative entropy of probability measures. -/
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {S : Type*} [MeasurableSpace S]

theorem entropy_rnDeriv_eq_klDiv (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) :
    LogSobolev.entropy ν (fun x => (μ.rnDeriv ν x).toReal) = (klDiv μ ν).toReal := by
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hD
  have hm : (∫ x, (μ.rnDeriv ν x).toReal ∂ν) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hac
  have hl : Integrable (fun x => (μ.rnDeriv ν x).toReal *
      log ((μ.rnDeriv ν x).toReal)) ν := (integrable_rnDeriv_mul_log_iff hac).2 hi
  rw [LogSobolev.entropy, hm, log_one, mul_zero, sub_zero]
  rw [toReal_klDiv_eq_integral_klFun hac]
  unfold klFun
  have hla : Integrable (fun x => (μ.rnDeriv ν x).toReal * log ((μ.rnDeriv ν x).toReal) + 1) ν :=
    hl.add (integrable_const 1)
  have hri : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν := Measure.integrable_toReal_rnDeriv
  rw [integral_sub hla hri,
    integral_add hl (integrable_const 1), integral_const, hm]
  simp

theorem rnDeriv_entropy_data (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hD : klDiv μ ν ≠ ∞) :
    Measurable (fun x => (μ.rnDeriv ν x).toReal) ∧
    (∀ x, 0 ≤ (μ.rnDeriv ν x).toReal) ∧
    Integrable (fun x => (μ.rnDeriv ν x).toReal) ν ∧
    Integrable (fun x => (μ.rnDeriv ν x).toReal * log ((μ.rnDeriv ν x).toReal)) ν ∧
    (∫ x, (μ.rnDeriv ν x).toReal ∂ν) = 1 ∧
    ν.withDensity (fun x => ENNReal.ofReal (μ.rnDeriv ν x).toReal) = μ := by
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hD
  refine ⟨by fun_prop, fun _ => ENNReal.toReal_nonneg,
    Measure.integrable_toReal_rnDeriv, (integrable_rnDeriv_mul_log_iff hac).2 hi, ?_, ?_⟩
  · simpa using Measure.integral_toReal_rnDeriv hac
  · calc
      _ = ν.withDensity (μ.rnDeriv ν) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
        exact ENNReal.ofReal_toReal hx.ne
      _ = μ := Measure.withDensity_rnDeriv_eq μ ν hac

theorem entropy_density_eq_klDiv (ν : Measure S) [IsProbabilityMeasure ν]
    (f : S → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hi : Integrable f ν) (hl : Integrable (fun x => f x * log (f x)) ν)
    [IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (f x)))] :
    klDiv (ν.withDensity (fun x => ENNReal.ofReal (f x))) ν ≠ ∞ ∧
    LogSobolev.entropy ν f =
      (klDiv (ν.withDensity (fun x => ENNReal.ofReal (f x))) ν).toReal := by
  let μ := ν.withDensity (fun x => ENNReal.ofReal (f x))
  have hac : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hr : (fun x => (μ.rnDeriv ν x).toReal) =ᵐ[ν] f := by
    filter_upwards [Measure.rnDeriv_withDensity ν hf.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (hn x)]
  have hrlog : (fun x => (μ.rnDeriv ν x).toReal * log ((μ.rnDeriv ν x).toReal)) =ᵐ[ν]
      (fun x => f x * log (f x)) := by filter_upwards [hr] with x hx; rw [hx]
  have hD : klDiv μ ν ≠ ∞ := klDiv_ne_top hac
    ((integrable_rnDeriv_mul_log_iff hac).1 (hl.congr hrlog.symm))
  refine ⟨hD, ?_⟩
  rw [← entropy_rnDeriv_eq_klDiv μ ν hD]
  unfold LogSobolev.entropy
  rw [integral_congr_ae hr, integral_congr_ae hrlog]

end
end PersistencePays
#print axioms PersistencePays.rnDeriv_entropy_data
#print axioms PersistencePays.entropy_density_eq_klDiv
