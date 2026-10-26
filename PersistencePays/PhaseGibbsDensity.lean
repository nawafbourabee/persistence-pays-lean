import PersistencePays.GibbsProduct
import PersistencePays.GaussianSecondMoment

/-! The phase-space Gibbs density and its actual normalizing integral. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem phase_gibbs_integrable (U : E → ℝ)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) :
    Integrable (fun z => Real.exp (-phaseEnergy U z)) ((volume : Measure E).prod volume) := by
  convert hi.mul_prod (kinetic_gibbs_integrable (E := E)) using 1
  funext z
  rw [← Real.exp_add, phaseEnergy_eq_norm]
  congr 1
  dsimp [kineticPotential]
  ring

theorem phase_gibbs_normalizer (U : E → ℝ) :
    (∫ z, Real.exp (-phaseEnergy U z) ∂((volume : Measure E).prod volume)) =
      (∫ x, Real.exp (-U x)) * (∫ v : E, Real.exp (-kineticPotential v)) := by
  have he : (fun z : E × E => Real.exp (-phaseEnergy U z)) =
      fun z => Real.exp (-U z.1) * Real.exp (-kineticPotential z.2) := by
    funext z
    rw [← Real.exp_add, phaseEnergy_eq_norm]
    congr 1
    dsimp [kineticPotential]
    ring
  rw [he, integral_prod_mul (fun x : E => Real.exp (-U x))
    (fun v : E => Real.exp (-kineticPotential v))]

theorem phaseGibbs_eq_tilted (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) :
    phaseGibbs U = ((volume : Measure E).prod volume).tilted (-phaseEnergy U) := by
  rw [tilted_eq_smul_gibbs _ _ (phaseEnergy_measurable U hU) (phase_gibbs_integrable U hi),
    phase_gibbs_normalizer]
  unfold phaseGibbs positionGibbs
  rw [stdGaussian_eq_kinetic_tilted, tilted_eq_smul_gibbs volume U hU hi,
    tilted_eq_smul_gibbs volume kineticPotential (by unfold kineticPotential; fun_prop)
      kinetic_gibbs_integrable, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    phase_gibbs_density_product U hU,
    ENNReal.ofReal_mul (integral_exp_pos hi).le,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]

theorem gaussianPair_eq_tilted :
    (stdGaussian E).prod (stdGaussian E) =
      ((volume : Measure E).prod volume).tilted (-phaseEnergy kineticPotential) := by
  rw [← phaseGibbs_eq_tilted kineticPotential (by unfold kineticPotential; fun_prop)
    kinetic_gibbs_integrable]
  simp only [phaseGibbs, positionGibbs, ← stdGaussian_eq_kinetic_tilted]

theorem kinetic_normalizer_real :
    (∫ v : E, Real.exp (-kineticPotential v)) =
      (2*Real.pi)^((Module.finrank ℝ E : ℝ)/2) := by
  convert GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E)
    (show (0 : ℝ) < 1/2 by norm_num) using 1
  · congr 1
    funext v
    congr 1
    dsimp [kineticPotential]
    ring
  · congr 1
    ring

theorem gaussianPair_energy_integrable :
    Integrable (phaseEnergy (kineticPotential : E → ℝ))
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hi : Integrable (kineticPotential : E → ℝ) (stdGaussian E) :=
    stdGaussian_norm_square_integrable.div_const 2
  have he : phaseEnergy (kineticPotential : E → ℝ) = fun z => kineticPotential z.1 + kineticPotential z.2 := by
    funext z
    rw [phaseEnergy_eq_norm]
    rfl
  rw [he]
  exact (hi.comp_fst (stdGaussian E)).add (hi.comp_snd (stdGaussian E))

theorem gaussianPair_energy :
    (∫ z : E × E, phaseEnergy kineticPotential z ∂(stdGaussian E).prod (stdGaussian E)) =
      (Module.finrank ℝ E : ℝ) := by
  have hi : Integrable (kineticPotential : E → ℝ) (stdGaussian E) :=
    stdGaussian_norm_square_integrable.div_const 2
  have he : phaseEnergy (kineticPotential : E → ℝ) = fun z => kineticPotential z.1 + kineticPotential z.2 := by
    funext z
    rw [phaseEnergy_eq_norm]
    rfl
  rw [he, integral_add (hi.comp_fst _) (hi.comp_snd _)]
  simp only [integral_fun_fst, integral_fun_snd, probReal_univ, one_smul]
  unfold kineticPotential
  rw [integral_div, stdGaussian_norm_square]
  ring

end PersistencePays
#print axioms PersistencePays.phaseGibbs_eq_tilted
#print axioms PersistencePays.gaussianPair_energy
