import PersistencePays.DensityEntropy

/-! Exact entropy change under a positive change of reference density. -/
open MeasureTheory InformationTheory Real
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {S : Type*} [MeasurableSpace S]

/-- Tilting the reference by `exp(-D)` adds the expectation of `D` to relative
entropy. Normalization is represented by the probability-measure instance. -/
theorem entropy_reference_change (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (D : S → ℝ) (hD : Measurable D) (hDi : Integrable D μ)
    [IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (exp (-D x))))]
    (hK : klDiv μ ν ≠ ∞) :
    klDiv μ (ν.withDensity (fun x => ENNReal.ofReal (exp (-D x)))) ≠ ∞ ∧
      (klDiv μ (ν.withDensity (fun x => ENNReal.ofReal (exp (-D x))))).toReal =
        (klDiv μ ν).toReal + ∫ x, D x ∂μ := by
  let r := μ.rnDeriv ν
  let s : S → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (-D x))
  let η := ν.withDensity s
  have hr : Measurable r := Measure.measurable_rnDeriv _ _
  have hs : Measurable s := by fun_prop
  have hs0 (x : S) : s x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (exp_pos _))
  have hsf (x : S) : s x ≠ ∞ := ENNReal.ofReal_ne_top
  have hμν := (klDiv_ne_top_iff.mp hK).1
  have hrep : ν.withDensity r = μ := Measure.withDensity_rnDeriv_eq _ _ hμν
  have he : η.withDensity (fun x => r x / s x) = μ := by
    rw [withDensity_ratio ν r s hr hs (Filter.Eventually.of_forall hsf)
      (Filter.Eventually.of_forall (fun x hx => (hs0 x hx).elim)), hrep]
  have ha : μ ≪ η := by
    rw [← he]
    exact withDensity_absolutelyContinuous _ _
  have hRN : μ.rnDeriv η =ᵐ[η] (fun x => r x / s x) := by
    rw [← he]
    exact Measure.rnDeriv_withDensity _ (show Measurable (fun x => r x / s x) from hr.div hs)
  have hlog : llr μ η =ᵐ[μ] (fun x => llr μ ν x + D x) := by
    filter_upwards [ha.ae_le hRN, Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_ne_top μ ν)] with x hx hpos hfin
    unfold llr
    rw [hx, ENNReal.toReal_div]
    have hrpos : 0 < (r x).toReal := ENNReal.toReal_pos (ne_of_gt hpos) hfin
    have hsval : (s x).toReal = exp (-D x) := ENNReal.toReal_ofReal (exp_pos _).le
    rw [hsval, log_div hrpos.ne' (exp_pos _).ne', log_exp]
    simp [r]
  have hi : Integrable (llr μ η) μ :=
    (((klDiv_ne_top_iff.mp hK).2).add hDi).congr hlog.symm
  refine ⟨klDiv_ne_top ha hi, ?_⟩
  rw [toReal_klDiv_of_measure_eq ha (by simp),
    toReal_klDiv_of_measure_eq hμν (by simp), integral_congr_ae hlog,
    integral_add (klDiv_ne_top_iff.mp hK).2 hDi]

end
end PersistencePays
#print axioms PersistencePays.entropy_reference_change
