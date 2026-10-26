import PersistencePays.Assumptions
import PersistencePays.OBABOPath

/-! Normalized potential and Lyapunov bounds used in Section 5.3. -/

namespace PersistencePays
noncomputable section
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def modifiedEnergy (U : E → ℝ) (h : ℝ) (z : E × E) : ℝ :=
  phaseEnergy U z - gradientCorrection (gradient U) h z.1

def lyapunov (U : E → ℝ) (h : ℝ) (z : E × E) : ℝ :=
  modifiedEnergy U h z + (1 / 5 : ℝ) * ⟪z.1, z.2⟫_ℝ

theorem A1.normalized_potential_nonnegative {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (x : E) : 0 ≤ U x := by
  simpa [hstar, hzero] using a.minimizer_le x

theorem A1.normalized_position_bound {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (x : E) : ‖x‖ ^ 2 ≤ 2 * U x := by
  have hh := a.quadratic_lower_at_minimizer x
  simp [hstar, hzero] at hh
  linarith

theorem A1.normalized_gradient_coercivity {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hzero : U 0 = 0) (x : E) :
    U x + ‖x‖ ^ 2 / 2 ≤ ⟪x, gradient U x⟫_ℝ := by
  have hh := a.strong_lower_bound x 0
  simp only [hzero, zero_sub, inner_neg_right, norm_neg, one_div] at hh
  rw [real_inner_comm] at hh
  linarith

theorem A1.normalized_gradient_bound {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (x : E) :
    ‖gradient U x‖ ^ 2 ≤ 2 * L * U x := by
  simpa [sub_zero] using gradient_norm_sq_le_energy U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian L a.L_pos a.upper 0
    (a.normalized_potential_nonnegative hstar hzero) x

theorem A1.normalized_energy_nonnegative {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (z : E × E) : 0 ≤ phaseEnergy U z := by
  rw [phaseEnergy_eq_norm]
  exact add_nonneg (a.normalized_potential_nonnegative hstar hzero z.1) (by positivity)

theorem A1.normalized_inner_energy {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (z : E × E) :
    |⟪z.1, z.2⟫_ℝ| ≤ phaseEnergy U z := by
  rw [phaseEnergy_eq_norm]
  have hc := abs_real_inner_le_norm z.1 z.2
  have hp := a.normalized_position_bound hstar hzero z.1
  nlinarith [sq_nonneg (‖z.1‖ - ‖z.2‖)]

theorem A1.normalized_correction_bound {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (hh : h ^ 2 * L ≤ 1 / 64) (x : E) :
    0 ≤ gradientCorrection (gradient U) h x ∧
      gradientCorrection (gradient U) h x ≤ U x / 256 := by
  have hg := gradientCorrection_bound U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian L a.L_pos a.upper 0
    (a.normalized_potential_nonnegative hstar hzero) h x
  constructor
  · exact hg.1
  · have hmul := mul_le_mul_of_nonneg_right hh (a.normalized_potential_nonnegative hstar hzero x)
    simp only [sub_zero] at hg
    nlinarith

/-- The two comparisons in equation (5.1), with the paper's rounded constants. -/
theorem lyapunov_energy_bounds {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (hh : h ^ 2 * L ≤ 1 / 64) (z : E × E) :
    0.79 * phaseEnergy U z ≤ lyapunov U h z ∧
      lyapunov U h z ≤ 1.2 * phaseEnergy U z ∧
      0.996 * phaseEnergy U z ≤ modifiedEnergy U h z ∧
      modifiedEnergy U h z ≤ phaseEnergy U z := by
  have hH := a.normalized_energy_nonnegative hstar hzero z
  have hG := a.normalized_correction_bound hstar hzero hh z.1
  have hI := a.normalized_inner_energy hstar hzero z
  have hU : U z.1 ≤ phaseEnergy U z := by
    rw [phaseEnergy_eq_norm]
    exact le_add_of_nonneg_right (by positivity)
  have hI' := neg_abs_le ⟪z.1, z.2⟫_ℝ
  have hI'' := le_abs_self ⟪z.1, z.2⟫_ℝ
  dsimp only [lyapunov, modifiedEnergy]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_sub_sq_bound (v w : E) : ‖v - w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have ht := norm_sub_le v w
  have hn := norm_nonneg (v - w)
  nlinarith [norm_nonneg v, norm_nonneg w, sq_nonneg (‖v‖ - ‖w‖)]

theorem A1.normalized_flight_square_bound {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (z : E × E) :
    ‖flightVelocity (gradient U) h z‖ ^ 2 ≤ 2 * ‖z.2‖ ^ 2 + h ^ 2 * L * U z.1 := by
  have hb := norm_sub_sq_bound z.2 ((h / 2) • gradient U z.1)
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow] at hb
  have hg := mul_le_mul_of_nonneg_left (a.normalized_gradient_bound hstar hzero z.1)
    (sq_nonneg h)
  change ‖z.2 - (h / 2) • gradient U z.1‖ ^ 2 ≤ _
  nlinarith

theorem A1.normalized_flight_energy_bound {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (hh : h ^ 2 * L ≤ 1 / 64) (z : E × E) :
    ‖flightVelocity (gradient U) h z‖ ^ 2 ≤ 4 * phaseEnergy U z := by
  have hb := a.normalized_flight_square_bound (h := h) hstar hzero z
  have hU := a.normalized_potential_nonnegative hstar hzero z.1
  have hmul := mul_le_mul_of_nonneg_right hh hU
  rw [phaseEnergy_eq_norm]
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_sub_sq_weighted (v w : E) :
    ‖v - w‖ ^ 2 ≤ (257 / 256 : ℝ) * ‖v‖ ^ 2 + 257 * ‖w‖ ^ 2 := by
  have ht := norm_sub_le v w
  have hn := norm_nonneg (v - w)
  nlinarith [norm_nonneg v, norm_nonneg w, sq_nonneg (‖v‖ / 16 - 16 * ‖w‖)]

theorem A1.normalized_damped_flight_square {U : E → ℝ} {L h r : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (hh : h ^ 2 * L ≤ 1 / 64)
    (hr : r ^ 2 ≤ 1) (z : E × E) :
    ‖r • z.2 - (h / 2) • gradient U z.1‖ ^ 2 ≤ (257 / 128 : ℝ) * phaseEnergy U z := by
  have hb := norm_sub_sq_weighted (r • z.2) ((h / 2) • gradient U z.1)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow] at hb
  have hrv := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖z.2‖)
  have hg := mul_le_mul_of_nonneg_left (a.normalized_gradient_bound hstar hzero z.1)
    (sq_nonneg h)
  have hU := mul_le_mul_of_nonneg_right hh (a.normalized_potential_nonnegative hstar hzero z.1)
  rw [phaseEnergy_eq_norm]
  nlinarith

theorem A1.normalized_damped_flight_radius {U : E → ℝ} {L h r vstar : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (hh : h ^ 2 * L ≤ 1 / 64)
    (hr : r ^ 2 ≤ 1) (hv : 0 ≤ vstar) (z : E × E)
    (hz : phaseEnergy U z ≤ vstar ^ 2 / 32) :
    ‖r • z.2 - (h / 2) • gradient U z.1‖ ≤ 0.2525 * vstar := by
  have hb := a.normalized_damped_flight_square hstar hzero hh hr z
  have hnorm := norm_nonneg (r • z.2 - (h / 2) • gradient U z.1)
  nlinarith [sq_nonneg vstar]

theorem A1.normalized_noisy_flight_radius {U : E → ℝ} {L h r σ vstar : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0) (hh : h ^ 2 * L ≤ 1 / 64)
    (hr : r ^ 2 ≤ 1) (hv : 0 ≤ vstar) (z : E × E)
    (hz : phaseEnergy U z ≤ vstar ^ 2 / 32) (ξ : E) (hξ : ‖σ • ξ‖ ≤ vstar / 2) :
    ‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖ ≤ 0.76 * vstar := by
  have hb := a.normalized_damped_flight_radius hstar hzero hh hr hv z hz
  have he : flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z) =
      (r • z.2 - (h / 2) • gradient U z.1) + σ • ξ := by
    dsimp [flightVelocity, OBABOPath.ou]
    module
  rw [he]
  have hn := norm_add_le (r • z.2 - (h / 2) • gradient U z.1) (σ • ξ)
  linarith

end
end PersistencePays

#print axioms PersistencePays.lyapunov_energy_bounds
#print axioms PersistencePays.A1.normalized_flight_energy_bound
#print axioms PersistencePays.A1.normalized_noisy_flight_radius
