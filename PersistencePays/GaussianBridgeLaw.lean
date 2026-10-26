import PersistencePays.AffineGaussianBridge
import PersistencePays.GaussianDensity

/-! Identification of the bridge density with actual Gaussian probability laws. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PersistencePays

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_eq_heatDensity :
    stdGaussian E = (volume : Measure E).withDensity (heatDensity 1) := by
  rw [stdGaussian_eq_kinetic_tilted, Measure.tilted]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hZ : (∫ v : E, Real.exp (-kineticPotential v)) =
      (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    convert h using 1
    · congr 1
      funext v
      unfold kineticPotential
      congr 1
      ring
    · congr 1
      ring
  simp only [Pi.neg_apply]
  rw [hZ]
  unfold heatDensity heatReal heatConstant kineticPotential
  congr 1
  rw [mul_one, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  ring

theorem map_density_equiv {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (e : S ≃ᵐ T) (μ : Measure S) (w : S → ℝ≥0∞) (hw : Measurable w) :
    Measure.map e (μ.withDensity w) = (Measure.map e μ).withDensity (fun y => w (e.symm y)) := by
  ext A hA
  have hi : Measurable (fun y => w (e.symm y)) := hw.comp e.symm.measurable
  rw [Measure.map_apply e.measurable hA, withDensity_apply w (e.measurable hA),
    withDensity_apply _ hA, setLIntegral_map hA hi e.measurable]
  simp only [MeasurableEquiv.symm_apply_apply]

def gaussianAffineEquiv (e : E ≃L[ℝ] E) (b : E) : E ≃ᵐ E where
  toFun := fun x => e x + b
  invFun := fun y => e.symm (y - b)
  left_inv := by intro x; simp
  right_inv := by intro y; simp
  measurable_toFun := e.continuous.measurable.add_const b
  measurable_invFun := e.symm.continuous.measurable.comp (measurable_id.sub_const b)

theorem map_volume_gaussianAffineEquiv (e : E ≃L[ℝ] E) (b : E) :
    Measure.map (gaussianAffineEquiv e b) (volume : Measure E) = inverseJacobian e • volume := by
  change Measure.map ((fun x : E => x + b) ∘ e) volume = _
  have ht : Measurable (fun x : E => x + b) := measurable_id.add_const b
  rw [← Measure.map_map ht e.continuous.measurable,
    map_volume_linearEquiv e, Measure.map_smul,
    (measurePreserving_add_right (volume : Measure E) b).map_eq]

/-- The explicit density used in the bridge theorem is exactly the law of
    `A Z + b` for `Z` a standard Gaussian and `A=e` invertible. -/
theorem affineGaussianDensity_eq_map_stdGaussian (e : E ≃L[ℝ] E) (b : E) :
    (volume : Measure E).withDensity (affineGaussianDensity e b) =
      Measure.map (fun x => e x + b) (stdGaussian E) := by
  rw [stdGaussian_eq_heatDensity]
  change _ = Measure.map (gaussianAffineEquiv e b)
    ((volume : Measure E).withDensity (heatDensity 1))
  have hi : Measurable (fun y => heatDensity 1 ((gaussianAffineEquiv e b).symm y)) :=
    (measurable_heatDensity 1).comp (gaussianAffineEquiv e b).symm.measurable
  rw [map_density_equiv _ _ _ (measurable_heatDensity 1),
    map_volume_gaussianAffineEquiv e b, withDensity_smul_measure,
    ← withDensity_smul _ hi]
  rfl

end PersistencePays

#print axioms PersistencePays.affineGaussianDensity_eq_map_stdGaussian
