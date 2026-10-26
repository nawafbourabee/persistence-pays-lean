import PersistencePays.ScalingEntropy

/-! Exact entropy change for an arbitrary input law under a constant-Jacobian
bijection. The input is not assumed to be a reference Gibbs law. -/
noncomputable section
namespace PersistencePays
open MeasureTheory InformationTheory
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem scaled_volume_entropy_change (ξ : Measure S) [NeZero ξ]
    (H : S → ℝ) (hH : Measurable H) (hI : Integrable (fun x => Real.exp (-H x)) ξ)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (e : S ≃ᵐ S) (c : ℝ) (hc : 0<c)
    (he : ξ.map e = ENNReal.ofReal c • ξ)
    (hK : klDiv μ (ξ.tilted (-H)) ≠ ∞)
    (hD : Integrable (fun x => H (e x)-H x) μ) :
    klDiv (μ.map e) (ξ.tilted (-H)) ≠ ∞ ∧
      (klDiv (μ.map e) (ξ.tilted (-H))).toReal =
        (klDiv μ (ξ.tilted (-H))).toReal + (∫ x, (H (e x)-H x) ∂μ)+Real.log c := by
  let ν := ξ.tilted (-H)
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hI
  let D : S → ℝ := fun x => H (e x)-H x+Real.log c
  have hm : Measurable D := by fun_prop
  have hi : Integrable D μ := hD.add (integrable_const _)
  have href := scaled_gibbs_reference ξ H H hH hH hI hI e c hc he
  have href' : ν.withDensity (fun x => ENNReal.ofReal (Real.exp (-D x))) = ν.map e.symm := by
    simpa only [add_sub_cancel_right] using href
  letI : IsProbabilityMeasure (ν.map e.symm) := Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (-D x)))) := by
    rw [href']; infer_instance
  have hh := entropy_reference_change μ ν D hm hi hK
  have hmap := klDiv_map_measurableEquiv e μ (ν.map e.symm)
  have hinv : (ν.map e.symm).map e = ν := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    simpa using (Measure.map_id (μ := ν))
  rw [hinv] at hmap
  rw [href',← hmap] at hh
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  have hdi : (∫ x, D x ∂μ) = (∫ x, (H (e x)-H x) ∂μ)+Real.log c := by
    rw [show D = fun x => (H (e x)-H x)+Real.log c from rfl,integral_add hD (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hdi]
  ring

end PersistencePays
#print axioms PersistencePays.scaled_volume_entropy_change
