import PersistencePays.EntropyReferenceChange
import PersistencePays.TransportReferences
import Mathlib.MeasureTheory.Measure.Tilted

/-! Exact relative-entropy change under a measure-preserving bijection. -/
open MeasureTheory InformationTheory Real
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {S : Type*} [MeasurableSpace S]

lemma map_inverse_of_measurePreserving (ξ : Measure S) (e : S ≃ᵐ S)
    (he : MeasurePreserving e ξ ξ) : ξ.map e.symm = ξ := by
  calc
    ξ.map e.symm = (ξ.map e).map e.symm := by rw [he.map_eq]
    _ = ξ := by
      rw [Measure.map_map e.symm.measurable e.measurable]
      have hid : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
      rw [hid, Measure.map_id]

lemma gibbs_reference_change_map (ξ : Measure S) [NeZero ξ]
    (H : S → ℝ) (hH : Measurable H) (hI : Integrable (fun x => exp (-H x)) ξ)
    (e : S ≃ᵐ S) (he : MeasurePreserving e ξ ξ) :
    (ξ.tilted (-H)).withDensity (fun x => ENNReal.ofReal (exp (-(H (e x) - H x)))) =
      (ξ.tilted (-H)).map e.symm := by
  let Z : ℝ := ∫ x, exp (-H x) ∂ξ
  have hZ : 0 < Z := integral_exp_pos hI
  let w : S → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (-H x) / Z)
  let v : S → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (-(H (e x) - H x)))
  have hw : Measurable w := by fun_prop
  have hv : Measurable v := by fun_prop
  change (ξ.withDensity w).withDensity v = (ξ.withDensity w).map e.symm
  rw [← withDensity_mul ξ hw hv, map_density_equiv e.symm ξ w hw,
    map_inverse_of_measurePreserving ξ e he]
  apply withDensity_congr_ae
  filter_upwards with x
  change ENNReal.ofReal (exp (-H x) / Z) * ENNReal.ofReal (exp (-(H (e x)-H x))) =
    ENNReal.ofReal (exp (-H (e x)) / Z)
  rw [← ENNReal.ofReal_mul (div_nonneg (exp_nonneg _) hZ.le)]
  congr 1
  calc
    _ = (exp (-H x) * exp (-(H (e x)-H x))) / Z := by ring
    _ = _ := by rw [← exp_add]; congr 2; ring

/-- Lemma 4.4 in a general reference-measure form. The energy-error integrability
is explicit; no differential entropy subtraction is used. -/
theorem volume_preserving_entropy_change (ξ : Measure S) [NeZero ξ]
    (H : S → ℝ) (hH : Measurable H) (hI : Integrable (fun x => exp (-H x)) ξ)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (e : S ≃ᵐ S) (he : MeasurePreserving e ξ ξ)
    (hK : klDiv μ (ξ.tilted (-H)) ≠ ∞)
    (hD : Integrable (fun x => H (e x) - H x) μ) :
    klDiv (μ.map e) (ξ.tilted (-H)) ≠ ∞ ∧
      (klDiv (μ.map e) (ξ.tilted (-H))).toReal =
        (klDiv μ (ξ.tilted (-H))).toReal + ∫ x, (H (e x) - H x) ∂μ := by
  let ν := ξ.tilted (-H)
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hI
  have hmap := gibbs_reference_change_map ξ H hH hI e he
  letI : IsProbabilityMeasure (ν.map e.symm) :=
    Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  letI : IsProbabilityMeasure
      (ν.withDensity (fun x => ENNReal.ofReal (exp (-(H (e x)-H x))))) := by
    rw [hmap]
    infer_instance
  have hchange := entropy_reference_change μ ν (fun x => H (e x)-H x)
    ((hH.comp e.measurable).sub hH) hD hK
  have hKmap := klDiv_map_measurableEquiv e μ (ν.map e.symm)
  have hinv : (ν.map e.symm).map e = ν := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    have hi : e ∘ e.symm = id := by funext x; exact e.apply_symm_apply x
    rw [hi, Measure.map_id]
  rw [hinv] at hKmap
  rw [hmap] at hchange
  rw [← hKmap] at hchange
  exact hchange

end
end PersistencePays
#print axioms PersistencePays.volume_preserving_entropy_change
