import PersistencePays.GaussianTarget
import PersistencePays.GaussianProductBound

noncomputable section
namespace PersistencePays.GaussianLowerBound
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The exact half-mass identity used for the two-warm initial law. -/
theorem standardGaussian_half_mass : (gaussianReal 0 1) (Iic 0) = (1/2 : ℝ≥0∞) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hsym : (gaussianReal 0 1).real (Ici 0) = (gaussianReal 0 1).real (Iic 0) := by
    have hm := congrArg (fun μ : Measure ℝ => μ.real (Iic 0))
      (gaussianReal_map_neg (μ := 0) (v := 1))
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic] at hm
    simpa using hm
  have hboundary : (gaussianReal 0 1).real (Iio 0) = (gaussianReal 0 1).real (Iic 0) := by
    exact congrArg ENNReal.toReal (measure_congr Iio_ae_eq_Iic)
  have hh := measureReal_add_measureReal_compl (μ := gaussianReal 0 1)
    (s := Iio (0:ℝ)) measurableSet_Iio
  rw [compl_Iio, probReal_univ, hsym, hboundary] at hh
  have hr : (gaussianReal 0 1).real (Iic 0) = (1/2 : ℝ) := by linarith
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
  simpa only [Measure.real, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hr

def softHalfspace (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n+1))) := {x | x 0 ≤ 0}

theorem softHalfspace_measurable (n : ℕ) : MeasurableSet (softHalfspace n) := by
  unfold softHalfspace
  exact measurableSet_le (by fun_prop) measurable_const

theorem diagonal_half_mass (n : ℕ) (a : Fin (n+1) → ℝ) (ha : ∀ i, 0<a i) :
    positionGibbs (diagonalPotential a) (softHalfspace n) = (1/2 : ℝ≥0∞) := by
  have hp : phaseGibbs (diagonalPotential a) ((softHalfspace n) ×ˢ univ) =
      positionGibbs (diagonalPotential a) (softHalfspace n) := by
    simp [phaseGibbs, Measure.prod_prod]
  rw [← hp, diagonal_phaseGibbs a ha,
    Measure.map_apply (diagonalPhaseMap_measurable a)
      ((softHalfspace_measurable n).prod MeasurableSet.univ)]
  have he : diagonalPhaseMap a ⁻¹' ((softHalfspace n) ×ˢ univ) =
      (fun z : Fin (n+1) → ℝ×ℝ => (z 0).1) ⁻¹' Iic (0:ℝ) := by
    ext z
    simp only [mem_preimage, mem_prod, mem_univ, and_true, softHalfspace,
      mem_setOf_eq, mem_Iic]
    change (z 0).1 / Real.sqrt (a 0) ≤ 0 ↔ (z 0).1 ≤ 0
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (ha 0)), zero_mul]
  rw [he]
  have hm : (productGaussianPair (n+1)).map (fun z => (z 0).1) = gaussianReal 0 1 := by
    rw [show (fun z : Fin (n+1) → ℝ×ℝ => (z 0).1) =
      (Prod.fst : ℝ×ℝ → ℝ) ∘ (fun z : Fin (n+1) → ℝ×ℝ => z 0) by rfl, ← Measure.map_map measurable_fst (measurable_pi_apply 0)]
    change ((Measure.pi (fun _ : Fin (n+1) => scalarGaussianPair)).map (Function.eval 0)).map Prod.fst = _
    rw [(measurePreserving_eval (fun _ : Fin (n+1) => scalarGaussianPair) 0).map_eq]
    simp [scalarGaussianPair, Measure.map_fst_prod]
  calc
    _ = (productGaussianPair (n+1)).map (fun z => (z 0).1) (Iic 0) :=
      (Measure.map_apply (by fun_prop) measurableSet_Iic).symm
    _ = _ := by rw [hm, standardGaussian_half_mass]

end PersistencePays.GaussianLowerBound
#print axioms PersistencePays.GaussianLowerBound.diagonal_half_mass
