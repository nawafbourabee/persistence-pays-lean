import PersistencePays.ThresholdMeasure
import PersistencePays.GaussianDensity
import Mathlib.Probability.Distributions.Exponential

/-! Identification of the invariant extended measure with the stated product law. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

instance expMeasure_one_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem expMeasure_one_density :
    expMeasure 1 =
      ((volume : Measure ℝ).withDensity (fun l => ENNReal.ofReal (Real.exp (-l)))).restrict
        (Ioi 0) := by
  have hmeas : Measurable (fun l : ℝ => ENNReal.ofReal (Real.exp (-l))) := by fun_prop
  rw [restrict_withDensity measurableSet_Ioi,
    ← withDensity_indicator measurableSet_Ioi]
  change volume.withDensity (gammaPDF 1 1) = _
  apply withDensity_congr_ae
  have hz : ∀ᵐ l : ℝ ∂volume, l ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hz] with l hl
  have hpdf : gammaPDF 1 1 l = exponentialPDF 1 l := rfl
  rw [hpdf, exponentialPDF_eq]
  by_cases hp : 0 < l
  · simp [Set.indicator, hp, hp.le]
  · have hn : l < 0 := lt_of_le_of_ne (le_of_not_gt hp) hl
    simp [Set.indicator, hp, not_le.mpr hn]

theorem extendedGibbs_eq_product {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (H : α → ℝ) (hH : Measurable H) :
    extendedGibbs μ H =
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x)))).prod (expMeasure 1) := by
  rw [expMeasure_one_density]
  have hH' : Measurable (fun x => ENNReal.ofReal (Real.exp (-H x))) := hH.neg.exp.ennreal_ofReal
  have hl : Measurable (fun l : ℝ => ENNReal.ofReal (Real.exp (-l))) := by fun_prop
  have hp := prod_withDensity (μ := μ) (ν := (volume : Measure ℝ)) hH' hl
  have he : (fun z : α × ℝ => ENNReal.ofReal (Real.exp (-H z.1)) *
      ENNReal.ofReal (Real.exp (-z.2))) =
      (fun z => ENNReal.ofReal (Real.exp (-(H z.1 + z.2)))) := by
    funext z
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  rw [he] at hp
  have hs : {z : α × ℝ | 0 < z.2} = (univ : Set α) ×ˢ Ioi 0 := by ext z; simp
  unfold extendedGibbs
  rw [hs, ← hp, ← Measure.prod_restrict, Measure.restrict_univ]

theorem tilted_eq_smul_gibbs {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NeZero μ] (H : α → ℝ) (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (-H x)) μ) :
    μ.tilted (-H) =
      (ENNReal.ofReal (∫ x, Real.exp (-H x) ∂μ))⁻¹ •
        μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x))) := by
  have hZ : 0 < ∫ x, Real.exp (-H x) ∂μ := integral_exp_pos hi
  rw [Measure.tilted]
  have he : (fun x => ENNReal.ofReal (Real.exp (-H x) / ∫ y, Real.exp (-H y) ∂μ)) =
      (fun x => (ENNReal.ofReal (∫ y, Real.exp (-H y) ∂μ))⁻¹ *
        ENNReal.ofReal (Real.exp (-H x))) := by
    funext x
    rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]
  change μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x) / ∫ y, Real.exp (-H y) ∂μ)) = _
  rw [he]
  exact withDensity_smul _ (hH.neg.exp.ennreal_ofReal)

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def positionGibbs (U : E → ℝ) : Measure E := volume.tilted (-U)

instance positionGibbs_finite (U : E → ℝ) : IsFiniteMeasure (positionGibbs U) := by
  unfold positionGibbs
  infer_instance

def phaseGibbs (U : E → ℝ) : Measure (E × E) :=
  (positionGibbs U).prod (stdGaussian E)

instance phaseGibbs_finite (U : E → ℝ) : IsFiniteMeasure (phaseGibbs U) := by
  unfold phaseGibbs
  infer_instance

def extendedTarget (U : E → ℝ) : Measure ((E × E) × ℝ) :=
  (phaseGibbs U).prod (expMeasure 1)

instance extendedTarget_finite (U : E → ℝ) : IsFiniteMeasure (extendedTarget U) := by
  unfold extendedTarget
  infer_instance

theorem phase_gibbs_density_product (U : E → ℝ) (hU : Measurable U) :
    ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))).prod
      ((volume : Measure E).withDensity (fun v => ENNReal.ofReal (Real.exp (-kineticPotential v)))) =
      ((volume : Measure E).prod volume).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-phaseEnergy U z))) := by
  rw [prod_withDensity
    (f := fun x => ENNReal.ofReal (Real.exp (-U x)))
    (g := fun v : E => ENNReal.ofReal (Real.exp (-kineticPotential v)))
    (by fun_prop) (by unfold kineticPotential; fun_prop)]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, phaseEnergy_eq_norm]
  congr 2
  dsimp [kineticPotential]
  ring

theorem extendedTarget_eq_smul_extendedGibbs (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) :
    extendedTarget U =
      ((ENNReal.ofReal (∫ x, Real.exp (-U x)))⁻¹ *
        (ENNReal.ofReal (∫ v : E, Real.exp (-kineticPotential v)))⁻¹) •
      extendedGibbs ((volume : Measure E).prod volume) (phaseEnergy U) := by
  rw [extendedGibbs_eq_product _ _ (phaseEnergy_measurable U hU)]
  unfold extendedTarget phaseGibbs positionGibbs
  rw [stdGaussian_eq_kinetic_tilted, tilted_eq_smul_gibbs volume U hU hi,
    tilted_eq_smul_gibbs volume kineticPotential (by unfold kineticPotential; fun_prop)
      kinetic_gibbs_integrable,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    phase_gibbs_density_product U hU, Measure.prod_smul_left]

/-- Invariance of the actual adjusted deterministic stage for the normalized
position-Gibbs × standard-Gaussian × Exp(1) law. Integrability is an explicit
normalization premise here, to be discharged from A1 separately. -/
theorem verlet_adjusted_preserves_target (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h))
      (extendedTarget U) (extendedTarget U) := by
  rw [extendedTarget_eq_smul_extendedGibbs U hU hi]
  exact (verlet_adjusted_preserves_extendedGibbs U hU g hg h).smul_measure _

end Euclidean

end PersistencePays

#print axioms PersistencePays.extendedGibbs_eq_product
#print axioms PersistencePays.tilted_eq_smul_gibbs
#print axioms PersistencePays.verlet_adjusted_preserves_target
