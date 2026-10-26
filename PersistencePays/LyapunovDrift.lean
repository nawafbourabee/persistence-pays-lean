import PersistencePays.LyapunovBounds
import PersistencePays.GaussianQuadraticMGF
import PersistencePays.OUScalarBounds

/-! Actual one-step Lyapunov drift: deterministic expansions and Gaussian integrations. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The complete random term of an OU half-step, including the quadratic noise. -/
def ouNoise (r σ : ℝ) (y u ξ : E) : ℝ :=
  ⟪σ•(r•u+(1/5:ℝ)•y), ξ⟫_ℝ+σ^2/2*‖ξ‖^2

theorem lyapunov_ou_increment (U : E → ℝ) (h r σ : ℝ) (z : E × E) (ξ : E) :
    lyapunov U h (OBABOPath.ou r σ ξ z)-lyapunov U h z =
      (r^2-1)/2*‖z.2‖^2+(1/5:ℝ)*(r-1)*⟪z.1,z.2⟫_ℝ+ouNoise r σ z.1 z.2 ξ := by
  simp only [lyapunov, modifiedEnergy, OBABOPath.ou, phaseEnergy_eq_norm, ouNoise,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem verlet_cross_increment (g : E → E) (h : ℝ) (z : E × E) :
    ⟪(verlet g h z).1,(verlet g h z).2⟫_ℝ-⟪z.1,z.2⟫_ℝ =
      h*‖flightVelocity g h z‖^2-
        h/2*(⟪z.1,g z.1⟫_ℝ+⟪(verlet g h z).1,g (verlet g h z).1⟫_ℝ) := by
  rw [verlet_velocity, inner_sub_right, real_inner_smul_right, verlet_position,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [flightVelocity, inner_sub_right, real_inner_smul_right]
  ring

theorem lyapunov_verlet_increment (U : E → ℝ) (h : ℝ) (z : E × E) :
    lyapunov U h (verlet (gradient U) h z)-lyapunov U h z =
      trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h z).1+
        (1/5:ℝ)*(h*‖flightVelocity (gradient U) h z‖^2-
          h/2*(⟪z.1,gradient U z.1⟫_ℝ+
            ⟪(verlet (gradient U) h z).1,gradient U (verlet (gradient U) h z).1⟫_ℝ)) := by
  have he := verlet_energy_identity U (gradient U) h z
  have hc := verlet_cross_increment (gradient U) h z
  unfold lyapunov modifiedEnergy
  linarith

/-- Weighted Young inequality with the constants used in the OU estimate. -/
theorem inner_quarter_bound (y u : E) :
    |⟪y,u⟫_ℝ| ≤ ‖y‖^2/4+‖u‖^2 := by
  have hc := abs_real_inner_le_norm y u
  nlinarith [sq_nonneg (‖y‖/2-‖u‖)]

theorem ou_deterministic_drift (h r : ℝ) (hh : 0 ≤ h)
    (hr : r ≤ 1) (hrh : 1-r ≤ h) (hrsq : 2*h*(1-h) ≤ 1-r^2) (y u : E) :
    (r^2-1)/2*‖u‖^2+(1/5:ℝ)*(r-1)*⟪y,u⟫_ℝ ≤
      -h*(1-h-(1/5:ℝ))*‖u‖^2+h/20*‖y‖^2 := by
  have hq := mul_le_mul_of_nonneg_right hrsq (sq_nonneg ‖u‖)
  have hi := inner_quarter_bound y u
  have hn := neg_abs_le ⟪y,u⟫_ℝ
  have ha := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1-r by linarith)
  have hb := mul_le_mul_of_nonneg_right hrh (show 0 ≤ ‖y‖^2/4+‖u‖^2 by positivity)
  have hc := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1-r by linarith)
  nlinarith


def unadjustedNoiseStep (U : E → ℝ) (h r σ : ℝ) (z : E × E) (η : E × E) : E × E :=
  OBABOPath.ou r σ η.2 (verlet (gradient U) h (OBABOPath.ou r σ η.1 z))

theorem flight_after_flipped_verlet (g : E → E) (h : ℝ) (z : E × E) :
    flightVelocity g h (velocityFlip (verlet g h z)) = -flightVelocity g h z := by
  change -(verlet g h z).2-(h/2)•g (verlet g h z).1 = _
  rw [verlet_velocity]
  module

/-- The deterministic inequality before the two Gaussian integrations. -/
theorem lyapunov_obabo_deterministic_bound
    {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hhmax : h ≤ 1/8) (hL : h^2*L ≤ 1/64)
    (hr : r ≤ 1) (hrh : 1-r ≤ h) (hrsq : 2*h*(1-h) ≤ 1-r^2)
    (z : E × E) (ξ ξ' : E)
    (hτ : trapezoidDefect U (gradient U) z.1
        (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1 ≤
      (0.02:ℝ)*h*‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖^2) :
    let w := verlet (gradient U) h (OBABOPath.ou r σ ξ z)
    lyapunov U h (unadjustedNoiseStep U h r σ z (ξ,ξ'))-lyapunov U h z ≤
      -(0.675:ℝ)*h*‖z.2‖^2-(0.1:ℝ)*h*U z.1-
        (0.235:ℝ)*h*‖w.2‖^2-(0.0965:ℝ)*h*U w.1+
          ouNoise r σ z.1 z.2 ξ+ouNoise r σ w.1 w.2 ξ' := by
  let z0 := OBABOPath.ou r σ ξ z
  let w := verlet (gradient U) h z0
  let V := flightVelocity (gradient U) h z0
  change lyapunov U h (OBABOPath.ou r σ ξ' w)-lyapunov U h z ≤ _
  have ho1 := lyapunov_ou_increment U h r σ z ξ
  have ho2 := lyapunov_ou_increment U h r σ w ξ'
  have hv := lyapunov_verlet_increment U h z0
  have hd1 := ou_deterministic_drift h r hh hr hrh hrsq z.1 z.2
  have hd2 := ou_deterministic_drift h r hh hr hrh hrsq w.1 w.2
  have hc1 := mul_le_mul_of_nonneg_left (a.normalized_gradient_coercivity hzero z.1)
    (show 0 ≤ h/10 by positivity)
  have hc2 := mul_le_mul_of_nonneg_left (a.normalized_gradient_coercivity hzero w.1)
    (show 0 ≤ h/10 by positivity)
  have hpost := a.normalized_flight_square_bound (h := h) hstar hzero (velocityFlip w)
  change ‖flightVelocity (gradient U) h (velocityFlip (verlet (gradient U) h z0))‖^2 ≤ _ at hpost
  rw [flight_after_flipped_verlet, norm_neg] at hpost
  simp only [velocityFlip, norm_neg] at hpost
  have hp := mul_le_mul_of_nonneg_left hpost (show 0 ≤ (0.22:ℝ)*h by positivity)
  have hU := a.normalized_potential_nonnegative hstar hzero w.1
  have hhU := mul_le_mul_of_nonneg_right hL (show 0 ≤ h*U w.1 by positivity)
  have hh1 := mul_le_mul_of_nonneg_right hhmax (show 0 ≤ h*‖z.2‖^2 by positivity)
  have hh2 := mul_le_mul_of_nonneg_right hhmax (show 0 ≤ h*‖w.2‖^2 by positivity)
  change trapezoidDefect U (gradient U) z.1 w.1 ≤ (0.02:ℝ)*h*‖V‖^2 at hτ
  change lyapunov U h z0-lyapunov U h z = _ at ho1
  change lyapunov U h (OBABOPath.ou r σ ξ' w)-lyapunov U h w = _ at ho2
  change lyapunov U h w-lyapunov U h z0 =
    trapezoidDefect U (gradient U) z.1 w.1+(1/5:ℝ)*(h*‖V‖^2-
      h/2*(⟪z.1,gradient U z.1⟫_ℝ+⟪w.1,gradient U w.1⟫_ℝ)) at hv
  nlinarith

/-- The cubic trapezoidal estimate becomes friction-scaled on the good-noise event. -/
theorem good_noise_trapezoid_bound
    {U : E → ℝ} {L LH h r σ vstar : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH) (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E × E) (hz : phaseEnergy U z ≤ vstar^2/32)
    (ξ : E) (hξ : ‖σ•ξ‖ ≤ vstar/2) :
    trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1 ≤
      (0.02:ℝ)*h*‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖^2 := by
  let V := flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)
  have hnorm := a.normalized_noisy_flight_radius hstar hzero hL hr hv z hz ξ hξ
  have hnorm' : ‖V‖ ≤ vstar := by change ‖V‖ ≤ 0.76*vstar at hnorm; linarith
  have ht := verlet_trapezoidDefect_lipschitz_bound U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian LH h hh a2.lipschitz (OBABOPath.ou r σ ξ z)
  have hp := mul_le_mul_of_nonneg_left hnorm'
    (show 0 ≤ LH*h^3/12*‖V‖^2 by positivity)
  have hs := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖V‖)
  have hle := le_abs_self (trapezoidDefect U (gradient U) z.1
    (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1)
  change |trapezoidDefect U (gradient U) z.1
    (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1| ≤ LH/12*h^3*‖V‖^3 at ht
  nlinarith


theorem ouNoise_vector_bound {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h) (y u : E) :
    ‖σ•(r•u+(1/5:ℝ)•y)‖^2 ≤ 4*h*(‖u‖^2+(0.08:ℝ)*U y) := by
  have hn := norm_sub_sq_bound (r•u) (-((1/5:ℝ)•y))
  simp only [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hn
  have hr' := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖u‖)
  have hy := a.normalized_position_bound hstar hzero y
  have hu := a.normalized_potential_nonnegative hstar hzero y
  have hb : ‖r•u+(1/5:ℝ)•y‖^2 ≤ 2*‖u‖^2+(0.16:ℝ)*U y := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hb (sq_nonneg σ)
  have h2 := mul_le_mul_of_nonneg_right hσ (show 0 ≤ 2*‖u‖^2+(0.16:ℝ)*U y by positivity)
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith

theorem ouNoise_exp_integrable (h r σ : ℝ) (hhmax : h ≤ 1/8) (hσ : σ^2 ≤ 2*h)
    (y u : E) : Integrable (fun ξ => Real.exp ((1/20:ℝ)*ouNoise r σ y u ξ)) (stdGaussian E) := by
  have hs : (1/20:ℝ)*σ^2 < 1 := by nlinarith
  convert stdGaussian_quadratic_exp_integrable ((1/20:ℝ)*σ^2) hs
    ((1/20:ℝ)•(σ•(r•u+(1/5:ℝ)•y))) using 1
  funext ξ
  congr 1
  rw [real_inner_smul_left]
  unfold ouNoise
  ring

theorem ouNoise_lintegral_exp_bound {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hhmax : h ≤ 1/8) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h) (y u : E) :
    (∫⁻ ξ, ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ y u ξ)) ∂stdGaussian E) ≤
      ENNReal.ofReal (Real.exp ((1.02:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)+
        (1/20:ℝ)*h*((0.1013:ℝ)*‖u‖^2+(0.0082:ℝ)*U y))) := by
  have hi := ouNoise_exp_integrable h r σ hhmax hσ y u
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  apply ENNReal.ofReal_le_ofReal
  exact stdGaussian_small_quadratic_mgf_bound h σ (‖u‖^2) (U y)
    (σ•(r•u+(1/5:ℝ)•y)) hh hhmax hσ (sq_nonneg _)
    (a.normalized_potential_nonnegative hstar hzero y)
    (ouNoise_vector_bound a hstar hzero hh hr hσ y u)

/-- Integrating the second actual OU half-step absorbs all post-Verlet energy terms. -/
theorem lyapunov_conditional_drift
    {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hhmax : h ≤ 1/8) (hL : h^2*L ≤ 1/64)
    (hr : r ≤ 1) (hrh : 1-r ≤ h) (hrsq : 2*h*(1-h) ≤ 1-r^2)
    (hrnorm : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h) (z : E × E) (ξ : E)
    (hτ : trapezoidDefect U (gradient U) z.1
        (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1 ≤
      (0.02:ℝ)*h*‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖^2) :
    (∫⁻ ξ', ENNReal.ofReal (Real.exp ((1/20:ℝ)*lyapunov U h
      (unadjustedNoiseStep U h r σ z (ξ,ξ')))) ∂stdGaussian E) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*lyapunov U h z-
        (1/20:ℝ)*h*((0.675:ℝ)*‖z.2‖^2+(0.1:ℝ)*U z.1)+
          (1.02:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ))) *
        ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ z.1 z.2 ξ)) := by
  let w := verlet (gradient U) h (OBABOPath.ou r σ ξ z)
  let C := (1/20:ℝ)*(lyapunov U h z-(0.675:ℝ)*h*‖z.2‖^2-(0.1:ℝ)*h*U z.1-
    (0.235:ℝ)*h*‖w.2‖^2-(0.0965:ℝ)*h*U w.1+ouNoise r σ z.1 z.2 ξ)
  have hm : Measurable (fun ξ' => ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ w.1 w.2 ξ'))) := by
    unfold ouNoise
    fun_prop
  calc
    _ ≤ ∫⁻ ξ', ENNReal.ofReal (Real.exp C) *
        ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ w.1 w.2 ξ')) ∂stdGaussian E := by
      apply lintegral_mono
      intro ξ'
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hb := lyapunov_obabo_deterministic_bound a hstar hzero hh hhmax hL hr hrh hrsq z ξ ξ' hτ
      change lyapunov U h (unadjustedNoiseStep U h r σ z (ξ,ξ'))-lyapunov U h z ≤ _ at hb
      dsimp only [C]
      linarith
    _ = ENNReal.ofReal (Real.exp C) *
        ∫⁻ ξ', ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ w.1 w.2 ξ')) ∂stdGaussian E :=
      lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (Real.exp C) *
        ENNReal.ofReal (Real.exp ((1.02:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)+
          (1/20:ℝ)*h*((0.1013:ℝ)*‖w.2‖^2+(0.0082:ℝ)*U w.1))) :=
      mul_le_mul' le_rfl (ouNoise_lintegral_exp_bound a hstar hzero hh hhmax hrnorm hσ w.1 w.2)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hu := a.normalized_potential_nonnegative hstar hzero w.1
      dsimp only [C]
      nlinarith [mul_nonneg hh hu, mul_nonneg hh (sq_nonneg ‖w.2‖)]


def stoppedLyapunovExp (U : E → ℝ) (h r σ vstar : ℝ) (z : E × E) (η : E × E) : ℝ :=
  if ‖σ•η.1‖ ≤ vstar/2 then
    Real.exp ((1/20:ℝ)*lyapunov U h (unadjustedNoiseStep U h r σ z η)) else 0

theorem stoppedLyapunovExp_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (z : E × E) : Measurable (stoppedLyapunovExp U h r σ vstar z) := by
  have hU := a.twice_contDiff.continuous.measurable
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  unfold stoppedLyapunovExp
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
  · unfold lyapunov modifiedEnergy phaseEnergy gradientCorrection unadjustedNoiseStep
      OBABOPath.ou verlet kick drift
    fun_prop
  · fun_prop

theorem stoppedLyapunovExp_nonnegative (U : E → ℝ) (h r σ vstar : ℝ) (z η : E × E) :
    0 ≤ stoppedLyapunovExp U h r σ vstar z η := by
  unfold stoppedLyapunovExp
  split_ifs <;> positivity

/-- Full one-step inequality, before specializing the exact OU coefficients. -/
theorem lyapunov_drift_lintegral
    {U : E → ℝ} {L LH h r σ vstar : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hhmax : h ≤ 1/8) (hL : h^2*L ≤ 1/64)
    (hr : r ≤ 1) (hrh : 1-r ≤ h) (hrsq : 2*h*(1-h) ≤ 1-r^2)
    (hrnorm : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH) (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E × E) (hz : phaseEnergy U z ≤ vstar^2/32) :
    (∫⁻ η, ENNReal.ofReal (stoppedLyapunovExp U h r σ vstar z η)
      ∂(stdGaussian E).prod (stdGaussian E)) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*(1-(0.076:ℝ)*h)*lyapunov U h z+
        (2.04:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ))) := by
  let C := (1/20:ℝ)*lyapunov U h z-
    (1/20:ℝ)*h*((0.675:ℝ)*‖z.2‖^2+(0.1:ℝ)*U z.1)+
      (1.02:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)
  have hm : Measurable (fun ξ => ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ z.1 z.2 ξ))) := by
    unfold ouNoise
    fun_prop
  rw [lintegral_prod _ (stoppedLyapunovExp_measurable a h r σ vstar z).ennreal_ofReal.aemeasurable]
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (Real.exp C) *
        ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ z.1 z.2 ξ)) ∂stdGaussian E := by
      apply lintegral_mono
      intro ξ
      by_cases hξ : ‖σ•ξ‖ ≤ vstar/2
      · simp only [stoppedLyapunovExp, hξ, ite_true]
        exact lyapunov_conditional_drift a hstar hzero hh hhmax hL hr hrh hrsq hrnorm hσ z ξ
          (good_noise_trapezoid_bound a a2 hstar hzero hh hL hrnorm hv hLH hscale z hz ξ hξ)
      · simp only [stoppedLyapunovExp, hξ, ite_false, ENNReal.ofReal_zero, lintegral_zero]
        exact zero_le
    _ = ENNReal.ofReal (Real.exp C) *
        ∫⁻ ξ, ENNReal.ofReal (Real.exp ((1/20:ℝ)*ouNoise r σ z.1 z.2 ξ)) ∂stdGaussian E :=
      lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (Real.exp C) *
        ENNReal.ofReal (Real.exp ((1.02:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)+
          (1/20:ℝ)*h*((0.1013:ℝ)*‖z.2‖^2+(0.0082:ℝ)*U z.1))) :=
      mul_le_mul' le_rfl (ouNoise_lintegral_exp_bound a hstar hzero hh hhmax hrnorm hσ z.1 z.2)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hly := (lyapunov_energy_bounds a hstar hzero hL z).2.1
      have hlyh := mul_le_mul_of_nonneg_left hly hh
      rw [phaseEnergy_eq_norm] at hlyh
      have hU := a.normalized_potential_nonnegative hstar hzero z.1
      dsimp only [C]
      nlinarith [mul_nonneg hh hU, mul_nonneg hh (sq_nonneg ‖z.2‖)]

/-- The real-valued expectation and its integrability are both justified. -/
theorem lyapunov_drift_expectation
    {U : E → ℝ} {L LH h r σ vstar : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hhmax : h ≤ 1/8) (hL : h^2*L ≤ 1/64)
    (hr : r ≤ 1) (hrh : 1-r ≤ h) (hrsq : 2*h*(1-h) ≤ 1-r^2)
    (hrnorm : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH) (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E × E) (hz : phaseEnergy U z ≤ vstar^2/32) :
    Integrable (stoppedLyapunovExp U h r σ vstar z) ((stdGaussian E).prod (stdGaussian E)) ∧
    (∫ η, stoppedLyapunovExp U h r σ vstar z η ∂(stdGaussian E).prod (stdGaussian E)) ≤
      Real.exp ((1/20:ℝ)*(1-(0.076:ℝ)*h)*lyapunov U h z+
        (2.04:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)) := by
  have hb := lyapunov_drift_lintegral a a2 hstar hzero hh hhmax hL hr hrh hrsq hrnorm hσ
    hv hLH hscale z hz
  have hm := stoppedLyapunovExp_measurable a h r σ vstar z
  have hn : ∀ᵐ η ∂(stdGaussian E).prod (stdGaussian E),
      0 ≤ stoppedLyapunovExp U h r σ vstar z η :=
    Filter.Eventually.of_forall (stoppedLyapunovExp_nonnegative U h r σ vstar z)
  constructor
  · refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_of_nonneg (stoppedLyapunovExp_nonnegative U h r σ vstar z _)]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ht

/-- Lemma 5.5 for the actual normalized OU coefficients.  The radius condition
also permits the quadratic case `LH = 0`, with any finite radius. -/
theorem lemma_5_5
    {U : E → ℝ} {L LH h vstar : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E × E) (hz : phaseEnergy U z ≤ vstar^2/32) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    (∀ ξ : E, ‖σ•ξ‖ ≤ vstar/2 →
      ‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖ ≤ (0.76:ℝ)*vstar ∧
      trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1 ≤
        (0.02:ℝ)*h*‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖^2) ∧
    Integrable (stoppedLyapunovExp U h r σ vstar z) ((stdGaussian E).prod (stdGaussian E)) ∧
    (∫ η, stoppedLyapunovExp U h r σ vstar z η ∂(stdGaussian E).prod (stdGaussian E)) ≤
      Real.exp ((1/20:ℝ)*(1-(0.076:ℝ)*h)*lyapunov U h z+
        (2.04:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)) := by
  dsimp only
  obtain ⟨hrpos, hr, hspos, hnorm, hrh, hrsq, _, hσ⟩ := normalized_ou_coefficients h hh
  have hrnorm : (Real.exp (-h))^2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt (1-Real.exp (-2*h)))]
  have hhmax : h ≤ 1/8 := by
    have := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  constructor
  · intro ξ hξ
    exact ⟨a.normalized_noisy_flight_radius hstar hzero hL hrnorm hv z hz ξ hξ,
      good_noise_trapezoid_bound a a2 hstar hzero hh hL hrnorm hv hLH hscale z hz ξ hξ⟩
  · exact lyapunov_drift_expectation a a2 hstar hzero hh hhmax hL hr hrh hrsq hrnorm hσ
      hv hLH hscale z hz

/-- Lemma 5.5 with the paper's exact finite radius `0.24/(LH*h²)`. -/
theorem lemma_5_5_paper_radius
    {U : E → ℝ} {L LH h : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64) (hLH : 0 < LH)
    (z : E × E) (hz : phaseEnergy U z ≤ ((0.24:ℝ)/(LH*h^2))^2/32) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let vstar := (0.24:ℝ)/(LH*h^2)
    (∀ ξ : E, ‖σ•ξ‖ ≤ vstar/2 →
      ‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖ ≤ (0.76:ℝ)*vstar ∧
      trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h (OBABOPath.ou r σ ξ z)).1 ≤
        (0.02:ℝ)*h*‖flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z)‖^2) ∧
    Integrable (stoppedLyapunovExp U h r σ vstar z) ((stdGaussian E).prod (stdGaussian E)) ∧
    (∫ η, stoppedLyapunovExp U h r σ vstar z η ∂(stdGaussian E).prod (stdGaussian E)) ≤
      Real.exp ((1/20:ℝ)*(1-(0.076:ℝ)*h)*lyapunov U h z+
        (2.04:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ)) := by
  apply lemma_5_5 a a2 hstar hzero hh.le hL (by positivity) hLH.le _ z hz
  have he : LH*h^3/12*((0.24:ℝ)/(LH*h^2)) = (0.02:ℝ)*h := by
    field_simp [ne_of_gt hLH, ne_of_gt hh]
    <;> ring
  exact he.le

end
end PersistencePays

#print axioms PersistencePays.lyapunov_ou_increment
#print axioms PersistencePays.lyapunov_verlet_increment

#print axioms PersistencePays.lyapunov_obabo_deterministic_bound
#print axioms PersistencePays.good_noise_trapezoid_bound

#print axioms PersistencePays.ouNoise_lintegral_exp_bound
#print axioms PersistencePays.lyapunov_conditional_drift

#print axioms PersistencePays.lyapunov_drift_expectation

#print axioms PersistencePays.lemma_5_5
#print axioms PersistencePays.lemma_5_5_paper_radius
