import PersistencePays.GibbsTail

/-! The Gaussian noise-tail estimate in Lemma 5.6, from an exact quadratic
Gaussian integral rather than an additional concentration theorem. -/

namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_norm_tail_mgf (v : ℝ) (hv : 0 ≤ v) :
    stdGaussian E {ξ | v < ‖ξ‖} ≤
      ENNReal.ofReal (Real.exp (-v^2/4)*(Real.sqrt 2)^Module.finrank ℝ E) := by
  have hi := (kinetic_energy_exp_integrable (E := E)).const_mul (Real.exp (-v^2/4))
  calc
    _ ≤ ENNReal.ofReal (∫ ξ, Real.exp (-v^2/4)*
        Real.exp (kineticPotential ξ/2) ∂stdGaussian E) := by
      apply hi.measure_le_integral
      · exact Filter.Eventually.of_forall (fun _ => by positivity)
      · intro ξ hξ
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        unfold kineticPotential
        change v < ‖ξ‖ at hξ
        nlinarith [norm_nonneg ξ]
    _ = _ := by rw [integral_const_mul, kinetic_energy_mgf]

theorem stdGaussian_norm_tail (v : ℝ) (hv : 0 ≤ v)
    (hd : 4*(Module.finrank ℝ E : ℝ) ≤ v^2) :
    stdGaussian E {ξ | v < ‖ξ‖} ≤ ENNReal.ofReal (Real.exp (-v^2/8)) := by
  apply (stdGaussian_norm_tail_mgf v hv).trans
  apply ENNReal.ofReal_le_ofReal
  have hs : Real.sqrt 2 ≤ Real.exp (1/2:ℝ) := by
    have hh := Real.add_one_le_exp (1:ℝ)
    have he : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [Real.exp_pos (1/2:ℝ), Real.sqrt_nonneg 2]
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg 2) hs (Module.finrank ℝ E)
  calc
    _ ≤ Real.exp (-v^2/4)*Real.exp (1/2:ℝ)^Module.finrank ℝ E :=
      mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ = Real.exp (-v^2/4+(Module.finrank ℝ E : ℝ)/2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem stdGaussian_scaled_norm_tail (σ v : ℝ) (hσ : 0 ≤ σ) (hσmax : σ ≤ 1/2)
    (hv : 0 ≤ v) (hd : 4*(Module.finrank ℝ E : ℝ) ≤ v^2) :
    stdGaussian E {ξ | v/2 < ‖σ•ξ‖} ≤ ENNReal.ofReal (Real.exp (-v^2/8)) := by
  apply (measure_mono (t := {ξ : E | v < ‖ξ‖}) _).trans (stdGaussian_norm_tail v hv hd)
  intro ξ hξ
  change v/2 < ‖σ•ξ‖ at hξ
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ] at hξ
  change v < ‖ξ‖
  have hh := mul_le_mul_of_nonneg_right hσmax (norm_nonneg ξ)
  linarith

end
end PersistencePays

#print axioms PersistencePays.stdGaussian_scaled_norm_tail
