import PersistencePays.ScalingEntropy
import PersistencePays.PositionBoltzmannEntropy
import PersistencePays.FiniteMoments

/-! Finite entropy is unchanged as a condition when switching between integrable
Gibbs references whose potential difference is integrable under the actual law. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem gibbs_reference_entropy_change (ξ : Measure S) [NeZero ξ]
    (F H : S → ℝ) (hF : Measurable F) (hH : Measurable H)
    (hFI : Integrable (fun x => Real.exp (-F x)) ξ)
    (hHI : Integrable (fun x => Real.exp (-H x)) ξ)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (hD : Integrable (fun x => H x-F x) μ)
    (hK : klDiv μ (ξ.tilted (-F)) ≠ ∞) :
    klDiv μ (ξ.tilted (-H)) ≠ ∞ ∧
    (klDiv μ (ξ.tilted (-H))).toReal = (klDiv μ (ξ.tilted (-F))).toReal +
      (∫ x, (H x-F x) ∂μ) + Real.log (∫ x, Real.exp (-H x) ∂ξ) -
        Real.log (∫ x, Real.exp (-F x) ∂ξ) := by
  let D : S → ℝ := fun x => H x-F x + Real.log (∫ y, Real.exp (-H y) ∂ξ) -
    Real.log (∫ y, Real.exp (-F y) ∂ξ)
  have hm : Measurable D := by fun_prop
  have hi : Integrable D μ := (hD.add (integrable_const _)).sub (integrable_const _)
  have href := scaled_gibbs_reference ξ F H hF hH hFI hHI (MeasurableEquiv.refl S)
    1 (by norm_num) (by change ξ.map id = _; simp)
  have he : (ξ.tilted (-F)).withDensity (fun x => ENNReal.ofReal (Real.exp (-D x))) =
      ξ.tilted (-H) := by
    simpa only [MeasurableEquiv.refl_apply, MeasurableEquiv.symm_refl, Real.log_one, add_zero,
      show (MeasurableEquiv.refl S : S → S) = id from rfl, Measure.map_id] using href
  letI : IsProbabilityMeasure (ξ.tilted (-F)) := isProbabilityMeasure_tilted hFI
  letI : IsProbabilityMeasure (ξ.tilted (-H)) := isProbabilityMeasure_tilted hHI
  letI : IsProbabilityMeasure ((ξ.tilted (-F)).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-D x)))) := by rw [he]; infer_instance
  have hh := entropy_reference_change μ (ξ.tilted (-F)) D hm hi hK
  rw [he] at hh
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  unfold D
  have hsum : Integrable (fun x => H x-F x+Real.log (∫ y, Real.exp (-H y) ∂ξ)) μ :=
    hD.add (integrable_const _)
  rw [integral_sub hsum (integrable_const _), integral_add hD (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.gaussian_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (positionGibbs U) ≠ ∞) : klDiv μ (stdGaussian E) ≠ ∞ := by
  have hUi : Integrable U μ := a.potential_integrable hμ
  have hHi : Integrable (kineticPotential : E → ℝ) μ := hμ.norm.integrable_sq.div_const 2
  have hh := (gibbs_reference_entropy_change volume U kineticPotential
    a.twice_contDiff.continuous.measurable (by unfold kineticPotential; fun_prop)
    a.gibbs_integrable kinetic_gibbs_integrable μ (hHi.sub hUi) hK).1
  simpa only [← stdGaussian_eq_kinetic_tilted] using hh

end PersistencePays
#print axioms PersistencePays.A1.gaussian_entropy_finite
