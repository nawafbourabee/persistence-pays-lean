import PersistencePays.GaussianDensity

/-! Exact Gaussian quadratic exponential integrals for the one-step Lyapunov proof. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem complete_square_exp {a : ℝ} (ha : 0 < a) (b x : E) :
    Real.exp (-a*‖x‖^2+⟪b,x⟫_ℝ) =
      Real.exp (‖b‖^2/(4*a)) * Real.exp (-a*‖x-(1/(2*a))•b‖^2) := by
  rw [← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right,
    real_inner_comm x b]
  field_simp
  ring

theorem integrable_gaussian_quadratic_linear {a : ℝ} (ha : 0 < a) (b : E) :
    Integrable (fun x => Real.exp (-a*‖x‖^2+⟪b,x⟫_ℝ)) volume := by
  simp_rw [complete_square_exp ha b]
  exact ((measurePreserving_sub_right (volume : Measure E) ((1/(2*a))•b)).integrable_comp_of_integrable
    (gaussian_radial_integrable (E := E) ha)).const_mul _

theorem integral_gaussian_quadratic_linear {a : ℝ} (ha : 0 < a) (b : E) :
    (∫ x : E, Real.exp (-a*‖x‖^2+⟪b,x⟫_ℝ)) =
      Real.exp (‖b‖^2/(4*a)) * (Real.pi/a)^((Module.finrank ℝ E : ℝ)/2) := by
  simp_rw [complete_square_exp ha b]
  rw [integral_const_mul]
  have hh := (measurePreserving_sub_right (volume : Measure E) ((1/(2*a))•b)).integral_comp
    (Homeomorph.subRight ((1/(2*a))•b)).measurableEmbedding (fun x : E => Real.exp (-a*‖x‖^2))
  rw [hh, GaussianFourier.integral_rexp_neg_mul_sq_norm ha]

/-- The exact Gaussian identity used in Lemma 5.5. -/
theorem stdGaussian_quadratic_mgf (s : ℝ) (hs : s < 1) (b : E) :
    (∫ x, Real.exp (⟪b,x⟫_ℝ+s/2*‖x‖^2) ∂stdGaussian E) =
      (1-s)^(-((Module.finrank ℝ E : ℝ)/2)) *
        Real.exp (‖b‖^2/(2*(1-s))) := by
  rw [stdGaussian_eq_kinetic_tilted, integral_exp_tilted]
  have he : ((-kineticPotential : E → ℝ) + (fun x => ⟪b,x⟫_ℝ+s/2*‖x‖^2)) =
      (fun x => -((1-s)/2)*‖x‖^2+⟪b,x⟫_ℝ) := by
    funext x
    simp only [Pi.add_apply, Pi.neg_apply, kineticPotential]
    ring
  rw [he, integral_gaussian_quadratic_linear (by linarith : 0 < (1-s)/2)]
  have hbase : (∫ x : E, Real.exp (-kineticPotential x)) =
      (Real.pi/(1/2:ℝ))^((Module.finrank ℝ E : ℝ)/2) := by
    convert GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (by norm_num : (0:ℝ)<1/2) using 1
    congr 1
    funext x
    congr 1
    unfold kineticPotential
    ring
  simp only [Pi.neg_apply]
  rw [hbase]
  have hratio : (Real.pi / ((1-s)/2)) / (Real.pi/(1/2:ℝ)) = (1-s)⁻¹ := by
    field_simp
  rw [mul_div_assoc, ← Real.div_rpow (by positivity) (by positivity), hratio,
    Real.inv_rpow (by linarith : 0 ≤ 1-s), ← Real.rpow_neg (by linarith : 0 ≤ 1-s)]
  rw [mul_comm]
  congr 3
  ring


theorem stdGaussian_quadratic_exp_integrable (s : ℝ) (hs : s < 1) (b : E) :
    Integrable (fun x => Real.exp (⟪b,x⟫_ℝ+s/2*‖x‖^2)) (stdGaussian E) := by
  rw [stdGaussian_eq_kinetic_tilted]
  apply (integrable_tilted_iff (f := (-kineticPotential : E → ℝ))
    (μ := (volume : Measure E)) (kinetic_gibbs_integrable (E := E)) _).mpr
  convert integrable_gaussian_quadratic_linear (E := E)
    (by linarith : 0 < (1-s)/2) b using 1
  funext x
  simp only [Pi.neg_apply, smul_eq_mul, ← Real.exp_add, kineticPotential]
  congr 1
  ring

theorem stdGaussian_quadratic_mgf_exp (s : ℝ) (hs : s < 1) (b : E) :
    (∫ x, Real.exp (⟪b,x⟫_ℝ+s/2*‖x‖^2) ∂stdGaussian E) =
      Real.exp (-((Module.finrank ℝ E : ℝ)/2)*Real.log (1-s)+‖b‖^2/(2*(1-s))) := by
  rw [stdGaussian_quadratic_mgf s hs b, Real.rpow_def_of_pos (by linarith : 0 < 1-s),
    ← Real.exp_add]
  congr 1
  ring

/-- The small-variance Gaussian constants in the proof of Lemma 5.5. -/
theorem gaussian_noise_exponent_bound
    (d h σ B X Y : ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h) (hhmax : h ≤ 1/8)
    (hσ : σ^2 ≤ 2*h) (hB : 0 ≤ B) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hBX : B ≤ 4*h*(X+(0.08:ℝ)*Y)) :
    -(d/2)*Real.log (1-(1/20:ℝ)*σ^2) + (1/20:ℝ)^2*B/(2*(1-(1/20:ℝ)*σ^2)) ≤
      (1.02:ℝ)*(1/20:ℝ)*h*d+(1/20:ℝ)*h*((0.1013:ℝ)*X+(0.0082:ℝ)*Y) := by
  let s : ℝ := (1/20:ℝ)*σ^2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsh : s ≤ h/10 := by dsimp [s]; linarith
  have hsmax : s ≤ 1/80 := by linarith
  have hden : 0 < 1-s := by linarith
  have hinv : (1-s)⁻¹ ≤ 80/79 := by
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hlog : -Real.log (1-s) ≤ (80/79:ℝ)*s := by
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
    rw [Real.log_inv] at hl
    have he : (1-s)⁻¹-1=s*(1-s)⁻¹ := by field_simp; ring
    rw [he] at hl
    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hinv hs0])
  have hlogbound : -(d/2)*Real.log (1-s) ≤ (1.02:ℝ)*(1/20:ℝ)*h*d := by
    have h1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ d/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsh (show 0 ≤ (d/2)*(80/79:ℝ) by positivity)
    nlinarith [mul_nonneg hh hd]
  have hquad : (1/20:ℝ)^2*B/(2*(1-s)) ≤
      (1/20:ℝ)*h*((0.1013:ℝ)*X+(0.0082:ℝ)*Y) := by
    have h1 := mul_le_mul_of_nonneg_left hinv (show 0 ≤ (1/20:ℝ)^2*B/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hBX (show 0 ≤ (1/20:ℝ)^2/2*(80/79:ℝ) by norm_num)
    have he : (1/20:ℝ)^2*B/(2*(1-s)) = ((1/20:ℝ)^2*B/2)*(1-s)⁻¹ := by field_simp
    rw [he]
    nlinarith [mul_nonneg hh hX, mul_nonneg hh hY]
  exact add_le_add hlogbound hquad


/-- A reusable form of each OU-noise integration in Lemma 5.5. -/
theorem stdGaussian_small_quadratic_mgf_bound
    (h σ X Y : ℝ) (b : E) (hh : 0 ≤ h) (hhmax : h ≤ 1/8)
    (hσ : σ^2 ≤ 2*h) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hB : ‖b‖^2 ≤ 4*h*(X+(0.08:ℝ)*Y)) :
    (∫ x, Real.exp ((1/20:ℝ)*(⟪b,x⟫_ℝ+σ^2/2*‖x‖^2)) ∂stdGaussian E) ≤
      Real.exp ((1.02:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)+
        (1/20:ℝ)*h*((0.1013:ℝ)*X+(0.0082:ℝ)*Y)) := by
  have hs : (1/20:ℝ)*σ^2 < 1 := by nlinarith
  have he (x : E) : (1/20:ℝ)*(⟪b,x⟫_ℝ+σ^2/2*‖x‖^2) =
      ⟪(1/20:ℝ)•b,x⟫_ℝ+((1/20:ℝ)*σ^2)/2*‖x‖^2 := by
    rw [real_inner_smul_left]
    ring
  simp_rw [he]
  rw [stdGaussian_quadratic_mgf_exp _ hs]
  apply Real.exp_le_exp.mpr
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact gaussian_noise_exponent_bound (Module.finrank ℝ E) h σ (‖b‖^2) X Y
    (by positivity) hh hhmax hσ (sq_nonneg _) hX hY hB

end
end PersistencePays

#print axioms PersistencePays.stdGaussian_quadratic_mgf

#print axioms PersistencePays.gaussian_noise_exponent_bound

#print axioms PersistencePays.stdGaussian_small_quadratic_mgf_bound
