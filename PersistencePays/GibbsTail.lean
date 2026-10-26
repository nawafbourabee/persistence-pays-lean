import PersistencePays.GibbsRegularity
import PersistencePays.GibbsProduct
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The exponential energy bound underlying Lemma 5.4. -/

namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem A1.midpoint_minimizer_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x : E) :
    U ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a.minimizer) ≤
      (U x + U a.minimizer) / 2 := by
  have hm := a.m_pos
  let y := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a.minimizer
  have hx := a.strong_lower_bound y x
  have hs := a.strong_lower_bound y a.minimizer
  have hc : ⟪gradient U y, x - y⟫_ℝ + ⟪gradient U y, a.minimizer - y⟫_ℝ = 0 := by
    rw [← inner_add_right]
    have he : x - y + (a.minimizer - y) = 0 := by dsimp [y]; module
    rw [he, inner_zero_right]
  have hnx : 0 ≤ m / 2 * ‖x - y‖ ^ 2 := by positivity
  have hns : 0 ≤ m / 2 * ‖a.minimizer - y‖ ^ 2 := by positivity
  change U y ≤ _
  linarith

theorem A1.half_gibbs_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Integrable (fun x => Real.exp (-U x / 2)) volume := by
  have hm := a.m_pos
  have hi := (shifted_gaussian_radial_integrable
    (E := E) (by positivity : 0 < m / 4) a.minimizer).const_mul
      (Real.exp (-U a.minimizer / 2))
  have hU := a.twice_contDiff.continuous
  refine hi.mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [a.quadratic_lower_at_minimizer x]

theorem A1.half_gibbs_normalizer_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    (∫ x : E, Real.exp (-U x / 2)) ≤
      Real.exp (U a.minimizer / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
        (∫ x : E, Real.exp (-U x)) := by
  let f : E → ℝ := fun y => Real.exp (-U (y + (1 / 2 : ℝ) • a.minimizer))
  have hf : Integrable f volume :=
    (measurePreserving_add_right volume ((1 / 2 : ℝ) • a.minimizer)).integrable_comp_of_integrable
      a.gibbs_integrable
  have hi := (hf.comp_smul (by norm_num : (1 / 2 : ℝ) ≠ 0)).const_mul
    (Real.exp (U a.minimizer / 2))
  calc
    (∫ x : E, Real.exp (-U x / 2)) ≤
      ∫ x : E, Real.exp (U a.minimizer / 2) * f ((1 / 2 : ℝ) • x) := by
        apply integral_mono a.half_gibbs_integrable hi
        intro x
        dsimp [f]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith [a.midpoint_minimizer_bound x]
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume f (1 / 2)
        (hR := by norm_num)]
      simp only [one_div, inv_pow, inv_inv, smul_eq_mul]
      rw [show (∫ x, f x) = ∫ x, Real.exp (-U x) from
        integral_add_right_eq_self (fun x => Real.exp (-U x)) ((1 / 2 : ℝ) • a.minimizer)]
      ring

theorem A1.position_energy_mgf_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    (∫ x, Real.exp ((U x - U a.minimizer) / 2) ∂positionGibbs U) ≤
      (2 : ℝ) ^ Module.finrank ℝ E := by
  unfold positionGibbs
  rw [integral_exp_tilted]
  have he : (fun x : E => Real.exp (((-U) + fun y => (U y - U a.minimizer) / 2) x)) =
      fun x => Real.exp (-U a.minimizer / 2) * Real.exp (-U x / 2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rw [he, integral_const_mul]
  apply (div_le_iff₀ a.gibbs_normalizer_pos).mpr
  calc
    _ ≤ Real.exp (-U a.minimizer / 2) *
        (Real.exp (U a.minimizer / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
          (∫ x : E, Real.exp (-U x))) :=
      mul_le_mul_of_nonneg_left a.half_gibbs_normalizer_bound (Real.exp_nonneg _)
    _ = _ := by
      have hcancel : Real.exp (-U a.minimizer / 2) * Real.exp (U a.minimizer / 2) = 1 := by
        rw [← Real.exp_add]
        have he : -U a.minimizer / 2 + U a.minimizer / 2 = 0 := by ring
        rw [he, Real.exp_zero]
      calc
        _ = (Real.exp (-U a.minimizer / 2) * Real.exp (U a.minimizer / 2)) *
            ((2 : ℝ) ^ Module.finrank ℝ E * ∫ x : E, Real.exp (-U x)) := by ring
        _ = _ := by rw [hcancel, one_mul]

theorem A1.position_energy_exp_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Integrable (fun x => Real.exp ((U x - U a.minimizer) / 2)) (positionGibbs U) := by
  apply (integrable_tilted_iff a.gibbs_integrable _).mpr
  convert a.half_gibbs_integrable.const_mul (Real.exp (-U a.minimizer / 2)) using 1
  funext x
  simp only [smul_eq_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem kinetic_half_normalizer :
    (∫ v : E, Real.exp (-kineticPotential v / 2)) =
      (Real.sqrt 2) ^ Module.finrank ℝ E * (∫ v : E, Real.exp (-kineticPotential v)) := by
  have hn (v : E) : kineticPotential ((Real.sqrt 2)⁻¹ • v) = kineticPotential v / 2 := by
    simp only [kineticPotential, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have he : (fun v : E => Real.exp (-kineticPotential v / 2)) =
      fun v => Real.exp (-kineticPotential ((Real.sqrt 2)⁻¹ • v)) := by
    funext v
    rw [hn]
    congr 1
    ring
  rw [he]
  exact Measure.integral_comp_inv_smul_of_nonneg volume
    (fun v : E => Real.exp (-kineticPotential v)) (Real.sqrt_nonneg 2)

theorem kinetic_energy_mgf :
    (∫ v : E, Real.exp (kineticPotential v / 2) ∂stdGaussian E) =
      (Real.sqrt 2) ^ Module.finrank ℝ E := by
  rw [stdGaussian_eq_kinetic_tilted, integral_exp_tilted]
  change (∫ v : E, Real.exp (-kineticPotential v + kineticPotential v / 2)) /
    (∫ v : E, Real.exp (-kineticPotential v)) = _
  have he : (fun v : E => Real.exp (-kineticPotential v + kineticPotential v / 2)) =
      fun v => Real.exp (-kineticPotential v / 2) := by
    funext v
    congr 1
    ring
  rw [he, kinetic_half_normalizer]
  exact mul_div_cancel_right₀ _ (integral_exp_pos kinetic_gibbs_integrable).ne'

theorem kinetic_energy_exp_integrable :
    Integrable (fun v : E => Real.exp (kineticPotential v / 2)) (stdGaussian E) := by
  rw [stdGaussian_eq_kinetic_tilted]
  apply (integrable_tilted_iff kinetic_gibbs_integrable _).mpr
  convert gaussian_radial_integrable (E := E) (by norm_num : (0 : ℝ) < 1 / 4) using 1
  funext v
  simp only [smul_eq_mul]
  rw [← Real.exp_add]
  congr 1
  dsimp [kineticPotential]
  ring

theorem A1.phase_energy_exp_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Integrable (fun z => Real.exp ((phaseEnergy U z - U a.minimizer) / 2)) (phaseGibbs U) := by
  unfold phaseGibbs
  convert a.position_energy_exp_integrable.mul_prod (kinetic_energy_exp_integrable (E := E)) using 1
  funext z
  rw [← Real.exp_add, phaseEnergy_eq_norm]
  congr 1
  dsimp [kineticPotential]
  ring

theorem A1.phase_energy_mgf_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    (∫ z, Real.exp ((phaseEnergy U z - U a.minimizer) / 2) ∂phaseGibbs U) ≤
      (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt 2) ^ Module.finrank ℝ E := by
  have he : (fun z : E × E => Real.exp ((phaseEnergy U z - U a.minimizer) / 2)) =
      fun z => Real.exp ((U z.1 - U a.minimizer) / 2) * Real.exp (kineticPotential z.2 / 2) := by
    funext z
    rw [← Real.exp_add, phaseEnergy_eq_norm]
    congr 1
    dsimp [kineticPotential]
    ring
  rw [he, phaseGibbs, integral_prod_mul
    (fun x : E => Real.exp ((U x - U a.minimizer) / 2))
    (fun v : E => Real.exp (kineticPotential v / 2)), kinetic_energy_mgf]
  exact mul_le_mul_of_nonneg_right a.position_energy_mgf_bound (by positivity)

/-- The high-energy tail with an exactly equivalent product form of the
paper's constant 2^(3d/2). The energy is centered at the actual minimizer. -/
theorem A1.gibbs_energy_tail {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (R : ℝ) :
    phaseGibbs U {z | R < phaseEnergy U z - U a.minimizer} ≤
      ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt 2) ^ Module.finrank ℝ E *
        Real.exp (-R / 2)) := by
  have hi := a.phase_energy_exp_integrable.const_mul (Real.exp (-R / 2))
  calc
    _ ≤ ENNReal.ofReal (∫ z, Real.exp (-R / 2) *
        Real.exp ((phaseEnergy U z - U a.minimizer) / 2) ∂phaseGibbs U) := by
      apply hi.measure_le_integral
      · exact Filter.Eventually.of_forall (fun _ => by positivity)
      · intro z hz
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        change R < phaseEnergy U z - U a.minimizer at hz
        linarith
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul]
      calc
        _ ≤ Real.exp (-R / 2) *
            ((2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt 2) ^ Module.finrank ℝ E) :=
          mul_le_mul_of_nonneg_left a.phase_energy_mgf_bound (Real.exp_nonneg _)
        _ = _ := by ring

theorem energy_tail_constant (d : ℕ) :
    (2 : ℝ) ^ d * (Real.sqrt 2) ^ d = (2 : ℝ) ^ (3 * (d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) d,
    ← Real.rpow_natCast ((2 : ℝ) ^ (1 / (2 : ℝ))) d,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Lemma 5.4, with the exact constant and the actual normalized target. -/
theorem lemma_5_4 {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (R : ℝ) :
    phaseGibbs U {z | R < phaseEnergy U z - U a.minimizer} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * (Module.finrank ℝ E : ℝ) / 2) * Real.exp (-R / 2)) := by
  simpa only [energy_tail_constant] using a.gibbs_energy_tail R

end
end PersistencePays

#print axioms PersistencePays.A1.position_energy_mgf_bound
#print axioms PersistencePays.A1.gibbs_energy_tail
#print axioms PersistencePays.lemma_5_4
