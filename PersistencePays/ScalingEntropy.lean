import PersistencePays.VolumeEntropy
import PersistencePays.GibbsProduct

/-! Exact relative entropy under a bijection with constant volume Jacobian. -/
noncomputable section
namespace PersistencePays
open MeasureTheory InformationTheory
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem map_inverse_scaled (ξ : Measure S) (e : S ≃ᵐ S)
    (c : ℝ) (hc : 0 < c) (he : ξ.map e = ENNReal.ofReal c • ξ) :
    ξ.map e.symm = ENNReal.ofReal c⁻¹ • ξ := by
  have hi : (ξ.map e).map e.symm = ξ := by
    rw [Measure.map_map e.symm.measurable e.measurable]
    simpa using (Measure.map_id ξ)
  rw [he, Measure.map_smul] at hi
  calc
    ξ.map e.symm = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) • ξ.map e.symm := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne',
        ENNReal.ofReal_one, one_smul]
    _ = ENNReal.ofReal c⁻¹ • ξ := by rw [mul_smul, hi]

theorem scaled_gibbs_reference (ξ : Measure S) [NeZero ξ]
    (F H : S → ℝ) (hF : Measurable F) (hH : Measurable H)
    (hFI : Integrable (fun x => Real.exp (-F x)) ξ)
    (hHI : Integrable (fun x => Real.exp (-H x)) ξ)
    (e : S ≃ᵐ S) (c : ℝ) (hc : 0 < c)
    (he : ξ.map e = ENNReal.ofReal c • ξ) :
    (ξ.tilted (-F)).withDensity (fun x => ENNReal.ofReal (Real.exp
      (-(H (e x) - F x + Real.log (∫ y, Real.exp (-H y) ∂ξ) -
        Real.log (∫ y, Real.exp (-F y) ∂ξ) + Real.log c)))) =
      (ξ.tilted (-H)).map e.symm := by
  let ZF := ∫ y, Real.exp (-F y) ∂ξ
  let ZH := ∫ y, Real.exp (-H y) ∂ξ
  have hZF : 0 < ZF := integral_exp_pos hFI
  have hZH : 0 < ZH := integral_exp_pos hHI
  let w : S → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-F x) / ZF)
  let wH : S → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-H x) / ZH)
  let D : S → ℝ := fun x => H (e x) - F x + Real.log ZH - Real.log ZF + Real.log c
  have hw : Measurable w := by fun_prop
  have hwH : Measurable wH := by fun_prop
  have hD : Measurable (fun x => ENNReal.ofReal (Real.exp (-D x))) := by fun_prop
  change (ξ.withDensity w).withDensity (fun x => ENNReal.ofReal (Real.exp (-D x))) =
    (ξ.withDensity wH).map e.symm
  rw [← withDensity_mul ξ hw hD, map_density_equiv e.symm ξ wH hwH,
    map_inverse_scaled ξ e c hc he, withDensity_smul_measure]
  have hm : Measurable (fun y => wH (e y)) := hwH.comp e.measurable
  simp only [MeasurableEquiv.symm_symm]
  rw [← withDensity_smul _ hm]
  apply withDensity_congr_ae
  filter_upwards with x
  change ENNReal.ofReal (Real.exp (-F x) / ZF) * ENNReal.ofReal (Real.exp (-D x)) =
    ENNReal.ofReal c⁻¹ * ENNReal.ofReal (Real.exp (-H (e x)) / ZH)
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_nonneg _) hZF.le),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  congr 1
  have hex : Real.exp (-D x) =
      Real.exp (-H (e x)) * Real.exp (F x) * ZH⁻¹ * ZF * c⁻¹ := by
    dsimp [D]
    rw [show -(H (e x) - F x + Real.log ZH - Real.log ZF + Real.log c) =
      -H (e x) + F x + -Real.log ZH + Real.log ZF + -Real.log c by ring]
    simp only [Real.exp_add, Real.exp_neg, Real.exp_log hZH, Real.exp_log hZF,
      Real.exp_log hc]
  rw [hex]
  have hcancel : Real.exp (-F x) * Real.exp (F x) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  nlinarith [hcancel]

theorem scaled_gibbs_entropy (ξ : Measure S) [NeZero ξ]
    (F H : S → ℝ) (hF : Measurable F) (hH : Measurable H)
    (hFI : Integrable (fun x => Real.exp (-F x)) ξ)
    (hHI : Integrable (fun x => Real.exp (-H x)) ξ)
    (e : S ≃ᵐ S) (c : ℝ) (hc : 0 < c)
    (he : ξ.map e = ENNReal.ofReal c • ξ)
    (hD : Integrable (fun x => H (e x)-F x) (ξ.tilted (-F))) :
    klDiv ((ξ.tilted (-F)).map e) (ξ.tilted (-H)) ≠ ∞ ∧
      (klDiv ((ξ.tilted (-F)).map e) (ξ.tilted (-H))).toReal =
        (∫ x, (H (e x)-F x) ∂ξ.tilted (-F)) +
          Real.log (∫ y, Real.exp (-H y) ∂ξ) -
          Real.log (∫ y, Real.exp (-F y) ∂ξ) + Real.log c := by
  let μ := ξ.tilted (-F)
  let ν := ξ.tilted (-H)
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hFI
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hHI
  let D : S → ℝ := fun x => H (e x) - F x + Real.log (∫ y, Real.exp (-H y) ∂ξ) -
      Real.log (∫ y, Real.exp (-F y) ∂ξ) + Real.log c
  have hm : Measurable D := by fun_prop
  have hi : Integrable D μ := ((hD.add (integrable_const _)).sub
    (integrable_const _)).add (integrable_const _)
  have href := scaled_gibbs_reference ξ F H hF hH hFI hHI e c hc he
  change μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-D x))) = ν.map e.symm at href
  letI : IsProbabilityMeasure (ν.map e.symm) :=
    Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  letI : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-D x)))) := by
    rw [href]; infer_instance
  have hchange := entropy_reference_change μ μ D hm hi (by simp)
  have hmap := klDiv_map_measurableEquiv e μ (ν.map e.symm)
  have hinv : (ν.map e.symm).map e = ν := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    simpa using (Measure.map_id ν)
  rw [hinv] at hmap
  rw [href, ← hmap] at hchange
  refine ⟨hchange.1, ?_⟩
  rw [hchange.2]
  simp only [klDiv_self, ENNReal.toReal_zero, zero_add]
  let C := Real.log (∫ y, Real.exp (-H y) ∂ξ) -
    Real.log (∫ y, Real.exp (-F y) ∂ξ) + Real.log c
  have heq : D = fun x => (H (e x)-F x) + C := by
    funext x
    dsimp [D, C]
    ring
  rw [heq, integral_add hD (integrable_const C)]
  simp only [integral_const]
  have hmass : (ξ.tilted (-F)).real Set.univ = 1 := by change μ.real Set.univ = 1; simp
  rw [hmass, one_smul]
  dsimp [C]
  ring

end PersistencePays
#print axioms PersistencePays.scaled_gibbs_entropy
