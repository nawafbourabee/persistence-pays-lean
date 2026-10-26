import Mathlib

/-!
# Exact algebra of velocity Verlet

This file proves the algebraic part of Lemma 2.1 of `main_9.pdf` and
the reversibility identity used in Lemma 2.3. No differentiability or
measure-preservation claim is implicit in these results. The force is an
arbitrary map; in the manuscript it is instantiated by the gradient.
-/

namespace PersistencePays

noncomputable section
open scoped InnerProductSpace

section Verlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def kick (g : E → E) (t : ℝ) (z : E × E) : E × E :=
  (z.1, z.2 - t • g z.1)

def drift (t : ℝ) (z : E × E) : E × E :=
  (z.1 + t • z.2, z.2)

def velocityFlip (z : E × E) : E × E := (z.1, -z.2)

def verlet (g : E → E) (h : ℝ) (z : E × E) : E × E :=
  kick g (h / 2) (drift h (kick g (h / 2) z))

def flightVelocity (g : E → E) (h : ℝ) (z : E × E) : E :=
  z.2 - (h / 2) • g z.1

def phaseEnergy (U : E → ℝ) (z : E × E) : ℝ :=
  U z.1 + ⟪z.2, z.2⟫_ℝ / 2

def gradientCorrection (g : E → E) (h : ℝ) (x : E) : ℝ :=
  h ^ 2 / 8 * ⟪g x, g x⟫_ℝ

def trapezoidDefect (U : E → ℝ) (g : E → E) (x y : E) : ℝ :=
  U y - U x - ⟪g x + g y, y - x⟫_ℝ / 2

theorem kick_inverse (g : E → E) (t : ℝ) (z : E × E) :
    kick g (-t) (kick g t z) = z := by
  ext <;> simp [kick]

theorem drift_inverse (t : ℝ) (z : E × E) :
    drift (-t) (drift t z) = z := by
  ext <;> simp [drift]

omit [InnerProductSpace ℝ E] in
theorem velocityFlip_involutive : Function.Involutive (velocityFlip (E := E)) := by
  intro z
  ext <;> simp [velocityFlip]

theorem velocityFlip_kick (g : E → E) (t : ℝ) (z : E × E) :
    velocityFlip (kick g t z) = kick g (-t) (velocityFlip z) := by
  ext <;> simp [velocityFlip, kick]
  module

theorem velocityFlip_drift (t : ℝ) (z : E × E) :
    velocityFlip (drift t z) = drift (-t) (velocityFlip z) := by
  ext <;> simp [velocityFlip, drift]

theorem verlet_inverse (g : E → E) (h : ℝ) (z : E × E) :
    verlet g (-h) (verlet g h z) = z := by
  simp only [verlet, neg_div, kick_inverse, drift_inverse]

theorem velocityFlip_verlet (g : E → E) (h : ℝ) (z : E × E) :
    velocityFlip (verlet g h z) = verlet g (-h) (velocityFlip z) := by
  simp only [verlet, velocityFlip_kick, velocityFlip_drift, neg_div]

theorem flipped_verlet_involutive (g : E → E) (h : ℝ) :
    Function.Involutive (fun z => velocityFlip (verlet g h z)) := by
  intro z
  change velocityFlip (verlet g h (velocityFlip (verlet g h z))) = z
  rw [velocityFlip_verlet]
  rw [velocityFlip_involutive]
  exact verlet_inverse g h z

theorem phaseEnergy_velocityFlip (U : E → ℝ) (z : E × E) :
    phaseEnergy U (velocityFlip z) = phaseEnergy U z := by
  simp [phaseEnergy, velocityFlip]

theorem phaseEnergy_eq_norm (U : E → ℝ) (z : E × E) :
    phaseEnergy U z = U z.1 + ‖z.2‖ ^ 2 / 2 := by
  simp only [phaseEnergy, real_inner_self_eq_norm_sq]

theorem gradientCorrection_eq_norm (g : E → E) (h : ℝ) (x : E) :
    gradientCorrection g h x = h ^ 2 / 8 * ‖g x‖ ^ 2 := by
  simp only [gradientCorrection, real_inner_self_eq_norm_sq]

theorem verlet_position (g : E → E) (h : ℝ) (z : E × E) :
    (verlet g h z).1 = z.1 + h • flightVelocity g h z := rfl

theorem verlet_velocity (g : E → E) (h : ℝ) (z : E × E) :
    (verlet g h z).2 = flightVelocity g h z -
      (h / 2) • g (verlet g h z).1 := rfl

theorem verlet_kinetic_identity (V g₀ g₁ : E) (h : ℝ) :
    (⟪V - (h / 2) • g₁, V - (h / 2) • g₁⟫_ℝ -
      ⟪V + (h / 2) • g₀, V + (h / 2) • g₀⟫_ℝ) / 2 =
    -(h / 2) * ⟪V, g₀ + g₁⟫_ℝ +
      h ^ 2 / 8 * (⟪g₁, g₁⟫_ℝ - ⟪g₀, g₀⟫_ℝ) := by
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm g₁ V, real_inner_comm g₀ V]
  ring

/-- Lemma 2.1's exact energy decomposition. -/
theorem verlet_energy_identity (U : E → ℝ) (g : E → E) (h : ℝ) (z : E × E) :
    phaseEnergy U (verlet g h z) - phaseEnergy U z =
    gradientCorrection g h (verlet g h z).1 - gradientCorrection g h z.1 +
      trapezoidDefect U g z.1 (verlet g h z).1 := by
  let V := flightVelocity g h z
  let x₁ := (verlet g h z).1
  have hv : z.2 = V + (h / 2) • g z.1 := by
    dsimp [V, flightVelocity]
    module
  have hx : x₁ - z.1 = h • V := by
    dsimp [x₁, V]
    rw [verlet_position]
    module
  have hk := verlet_kinetic_identity V (g z.1) (g x₁) h
  change U x₁ + ⟪(verlet g h z).2, (verlet g h z).2⟫_ℝ / 2 -
    (U z.1 + ⟪z.2, z.2⟫_ℝ / 2) = _
  rw [verlet_velocity, hv]
  change U x₁ + ⟪V - (h / 2) • g x₁, V - (h / 2) • g x₁⟫_ℝ / 2 -
    (U z.1 + ⟪V + (h / 2) • g z.1, V + (h / 2) • g z.1⟫_ℝ / 2) = _
  change _ = h ^ 2 / 8 * ⟪g x₁, g x₁⟫_ℝ -
    h ^ 2 / 8 * ⟪g z.1, g z.1⟫_ℝ +
    (U x₁ - U z.1 - ⟪g z.1 + g x₁, x₁ - z.1⟫_ℝ / 2)
  rw [hx, real_inner_smul_right, real_inner_comm V (g z.1 + g x₁)]
  linarith

/-- Norm notation version of the exact manuscript identity. -/
theorem verlet_energy_identity_norm (U : E → ℝ) (g : E → E) (h : ℝ) (z : E × E) :
    (U (verlet g h z).1 + ‖(verlet g h z).2‖ ^ 2 / 2) -
      (U z.1 + ‖z.2‖ ^ 2 / 2) =
    h ^ 2 / 8 * (‖g (verlet g h z).1‖ ^ 2 - ‖g z.1‖ ^ 2) +
      trapezoidDefect U g z.1 (verlet g h z).1 := by
  simpa only [phaseEnergy_eq_norm, gradientCorrection_eq_norm, mul_sub]
    using verlet_energy_identity U g h z

def quadraticPotential (A : E →ₗ[ℝ] E) (b : E) (c : ℝ) (x : E) : ℝ :=
  ⟪x, A x⟫_ℝ / 2 + ⟪b, x⟫_ℝ + c

/-- The trapezoidal defect vanishes for every symmetric quadratic potential. -/
theorem quadratic_trapezoidDefect (A : E →ₗ[ℝ] E) (b : E) (c : ℝ)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (x y : E) :
    trapezoidDefect (quadraticPotential A b c) (fun x => A x + b) x y = 0 := by
  simp only [trapezoidDefect, quadraticPotential, inner_add_left,
    inner_sub_right]
  have hab : ⟪y, A x⟫_ℝ = ⟪x, A y⟫_ℝ := by
    rw [real_inner_comm (A x) y, hA x y]
  rw [hA x y, hA x x, hA y x, hA y y, hab]
  ring

end Verlet

section ScalarRemainder

open MeasureTheory Set

theorem integral_centered_linear : (∫ t : ℝ in 0..1, t - 1 / 2) = 0 := by
  rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => (1 / 2 : ℝ))
    (continuous_id.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)]
  norm_num [integral_id]

theorem integral_centered_square : (∫ t : ℝ in 0..1, (t - 1 / 2) ^ 2) = 1 / 12 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (t - 1 / 2) ^ 3 / 3)
      ((t - 1 / 2) ^ 2) t := by
    convert! (((hasDerivAt_id t).sub_const (1 / 2)).pow 3).div_const 3 using 1 <;>
      simp only [id_eq] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (((continuous_id.sub continuous_const).pow 2).intervalIntegrable 0 1)
  norm_num at hi ⊢
  exact hi

theorem integral_centered_abs : (∫ t : ℝ in 0..1, |t - 1 / 2|) = 1 / 4 := by
  have hc : Continuous (fun t : ℝ => |t - 1 / 2|) :=
    (continuous_id.sub continuous_const).abs
  have hl : (∫ t : ℝ in 0..(1 / 2), |t - 1 / 2|) =
      ∫ t : ℝ in 0..(1 / 2), 1 / 2 - t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change |t - 1 / 2| = 1 / 2 - t
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    ring
  have hr : (∫ t : ℝ in (1 / 2)..1, |t - 1 / 2|) =
      ∫ t : ℝ in (1 / 2)..1, t - 1 / 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    change |t - 1 / 2| = t - 1 / 2
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    rw [abs_of_nonneg (by linarith [ht.1])]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), hl, hr]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 / 2 : ℝ)) (g := fun t => t)
    (continuous_const.intervalIntegrable 0 (1 / 2))
    (continuous_id.intervalIntegrable 0 (1 / 2))]
  rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => (1 / 2 : ℝ))
    (continuous_id.intervalIntegrable (1 / 2) 1)
    (continuous_const.intervalIntegrable (1 / 2) 1)]
  norm_num [integral_id]

/-- Integration-by-parts identity used in the proof of Lemma 2.1. -/
theorem scalar_trapezoid_remainder (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'') :
    f 1 - f 0 - (f' 0 + f' 1) / 2 =
      -(∫ t : ℝ in 0..1, (t - 1 / 2) * f'' t) := by
  have hcont' : Continuous f' := continuous_iff_continuousAt.mpr
    (fun t => (hf' t).continuousAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hf t) (hcont'.intervalIntegrable 0 1)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => t - 1 / 2) (u' := fun _ => (1 : ℝ))
    (v := f') (v' := f'') (a := 0) (b := 1)
    (continuous_id.sub continuous_const).continuousOn hcont'.continuousOn
    (fun t _ => by simpa using (hasDerivAt_id t).sub_const (1 / 2))
    (fun t _ => hf' t) (continuous_const.intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1)
  simp only [one_mul] at hparts
  rw [hFTC] at hparts
  linarith

/-- Centering the curvature at any constant leaves the signed defect unchanged. -/
theorem centered_curvature_integral (a : ℝ → ℝ) (ha : Continuous a) (c : ℝ) :
    (∫ t : ℝ in 0..1, (t - 1 / 2) * (a t - c)) =
      ∫ t : ℝ in 0..1, (t - 1 / 2) * a t := by
  have hi := intervalIntegral.integral_sub (μ := volume)
    (f := fun t : ℝ => (t - 1 / 2) * a t) (g := fun t => (t - 1 / 2) * c)
    (((continuous_id.sub continuous_const).mul ha).intervalIntegrable 0 1)
    (((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable 0 1)
  have hp : (fun t : ℝ => (t - 1 / 2) * (a t - c)) =
      (fun t => (t - 1 / 2) * a t - (t - 1 / 2) * c) := by
    funext t
    ring
  rw [hp, hi, intervalIntegral.integral_mul_const, integral_centered_linear]
  ring

/-- Sharp bounded-curvature estimate for the signed scalar trapezoidal defect. -/
theorem curvature_integral_bound (a : ℝ → ℝ) (ha : Continuous a) (M : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ a t ∧ a t ≤ M) :
    |∫ t : ℝ in 0..1, (t - 1 / 2) * a t| ≤ M / 8 := by
  rw [← centered_curvature_integral a ha (M / 2)]
  have hnorm : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(t - 1 / 2) * (a t - M / 2)‖ ≤ (M / 2) * |t - 1 / 2| := by
    intro t ht
    have hab := hbound t ⟨le_of_lt ht.1, ht.2⟩
    have haabs : |a t - M / 2| ≤ M / 2 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      ‖(t - 1 / 2) * (a t - M / 2)‖ = |t - 1 / 2| * |a t - M / 2| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |t - 1 / 2| * (M / 2) := mul_le_mul_of_nonneg_left haabs (abs_nonneg _)
      _ = (M / 2) * |t - 1 / 2| := mul_comm _ _
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall hnorm)
    ((continuous_const.mul (continuous_id.sub continuous_const).abs).intervalIntegrable 0 1)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_centered_abs] at hi
  linarith

/-- Sharp Lipschitz-curvature estimate for the signed scalar trapezoidal defect. -/
theorem lipschitz_curvature_integral_bound (a : ℝ → ℝ) (ha : Continuous a) (M : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |a t - a (1 / 2)| ≤ M * |t - 1 / 2|) :
    |∫ t : ℝ in 0..1, (t - 1 / 2) * a t| ≤ M / 12 := by
  rw [← centered_curvature_integral a ha (a (1 / 2))]
  have hnorm : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(t - 1 / 2) * (a t - a (1 / 2))‖ ≤ M * (t - 1 / 2) ^ 2 := by
    intro t ht
    have hab := hbound t ⟨le_of_lt ht.1, ht.2⟩
    calc
      ‖(t - 1 / 2) * (a t - a (1 / 2))‖ =
          |t - 1 / 2| * |a t - a (1 / 2)| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |t - 1 / 2| * (M * |t - 1 / 2|) :=
        mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = M * (t - 1 / 2) ^ 2 := by
        calc
          _ = M * |t - 1 / 2| ^ 2 := by ring
          _ = _ := by rw [sq_abs]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall hnorm)
    ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable 0 1)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_centered_square] at hi
  linarith

theorem scalar_trapezoid_bound (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'') (M : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f'' t ∧ f'' t ≤ M) :
    |f 1 - f 0 - (f' 0 + f' 1) / 2| ≤ M / 8 := by
  rw [scalar_trapezoid_remainder f f' f'' hf hf' hcont, abs_neg]
  exact curvature_integral_bound f'' hcont M hbound

theorem scalar_trapezoid_lipschitz_bound (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'') (M : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |f'' t - f'' (1 / 2)| ≤ M * |t - 1 / 2|) :
    |f 1 - f 0 - (f' 0 + f' 1) / 2| ≤ M / 12 := by
  rw [scalar_trapezoid_remainder f f' f'' hf hf' hcont, abs_neg]
  exact lipschitz_curvature_integral_bound f'' hcont M hbound

theorem integral_one_sub : (∫ t : ℝ in 0..1, 1 - t) = 1 / 2 := by
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => t)
    (continuous_const.intervalIntegrable 0 1) (continuous_id.intervalIntegrable 0 1)]
  norm_num [integral_id]

/-- The scalar descent lemma, obtained by integrating the second derivative. -/
theorem scalar_descent_bound (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'') (M : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, f'' t ≤ M) :
    f 1 ≤ f 0 + f' 0 + M / 2 := by
  have hcont' : Continuous f' := continuous_iff_continuousAt.mpr
    (fun t => (hf' t).continuousAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hf t) (hcont'.intervalIntegrable 0 1)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => 1 - t) (u' := fun _ => (-1 : ℝ))
    (v := f') (v' := f'') (a := 0) (b := 1)
    (continuous_const.sub continuous_id).continuousOn hcont'.continuousOn
    (fun t _ => by simpa using (hasDerivAt_id t).const_sub 1)
    (fun t _ => hf' t) (continuous_const.intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, hFTC] at hparts
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => (1 - t) * f'' t) (g := fun t : ℝ => (1 - t) * M)
    (by norm_num : (0 : ℝ) ≤ 1)
    (((continuous_const.sub continuous_id).mul hcont).intervalIntegrable 0 1)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1)
    (fun t ht => mul_le_mul_of_nonneg_left (hbound t ht) (by linarith [ht.2]))
  rw [intervalIntegral.integral_mul_const, integral_one_sub] at hmono
  linarith

end ScalarRemainder

section MultivariateRemainder

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem potential_line_derivative (U : E → ℝ) (g : E → E)
    (hgrad : ∀ x, HasGradientAt U (g x) x) (x δ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U (x + s • δ)) ⟪g (x + t • δ), δ⟫_ℝ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • δ) δ t := by
    simpa using ((hasDerivAt_id t).smul_const δ).const_add x
  convert! (hgrad (x + t • δ)).hasFDerivAt.comp_hasDerivAt t hline using 1

theorem gradient_line_derivative (g : E → E) (A : E → E →L[ℝ] E)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (x δ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪g (x + s • δ), δ⟫_ℝ)
      ⟪A (x + t • δ) δ, δ⟫_ℝ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • δ) δ t := by
    simpa using ((hasDerivAt_id t).smul_const δ).const_add x
  simpa using ((hHess (x + t • δ)).comp_hasDerivAt t hline).inner ℝ
    (hasDerivAt_const t δ)

theorem hessian_line_continuous (A : E → E →L[ℝ] E) (hA : Continuous A) (x δ : E) :
    Continuous (fun t : ℝ => ⟪A (x + t • δ) δ, δ⟫_ℝ) := by
  exact ((hA.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
    continuous_const).inner continuous_const

/-- The `L/8` part of Lemma 2.1, from the actual gradient and Hessian.
The curvature hypothesis is the nonnegative, upper-bounded part of (A1). -/
theorem trapezoidDefect_bound (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (L : ℝ)
    (hcurv : ∀ x u, 0 ≤ ⟪A x u, u⟫_ℝ ∧ ⟪A x u, u⟫_ℝ ≤ L * ‖u‖ ^ 2)
    (x y : E) : |trapezoidDefect U g x y| ≤ L / 8 * ‖y - x‖ ^ 2 := by
  have h1 : x + (1 : ℝ) • (y - x) = y := by module
  have hb := scalar_trapezoid_bound
    (fun t : ℝ => U (x + t • (y - x)))
    (fun t : ℝ => ⟪g (x + t • (y - x)), y - x⟫_ℝ)
    (fun t : ℝ => ⟪A (x + t • (y - x)) (y - x), y - x⟫_ℝ)
    (potential_line_derivative U g hgrad x (y - x))
    (gradient_line_derivative g A hHess x (y - x))
    (hessian_line_continuous A hA x (y - x)) (L * ‖y - x‖ ^ 2)
    (fun t _ => hcurv (x + t • (y - x)) (y - x))
  simpa only [h1, zero_smul, add_zero, trapezoidDefect, inner_add_left,
    mul_div_assoc, div_mul_eq_mul_div] using hb

theorem hessian_line_lipschitz (A : E → E →L[ℝ] E) (LH : ℝ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ LH * ‖x - y‖) (x δ : E) (s t : ℝ) :
    |⟪A (x + s • δ) δ, δ⟫_ℝ - ⟪A (x + t • δ) δ, δ⟫_ℝ| ≤
      (LH * ‖δ‖ ^ 3) * |s - t| := by
  have hline : (x + s • δ) - (x + t • δ) = (s - t) • δ := by module
  have hn : ‖(x + s • δ) - (x + t • δ)‖ = |s - t| * ‖δ‖ := by
    rw [hline, norm_smul, Real.norm_eq_abs]
  calc
    _ = |⟪(A (x + s • δ) - A (x + t • δ)) δ, δ⟫_ℝ| := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    _ ≤ ‖(A (x + s • δ) - A (x + t • δ)) δ‖ * ‖δ‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖A (x + s • δ) - A (x + t • δ)‖ * ‖δ‖) * ‖δ‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ((LH * ‖(x + s • δ) - (x + t • δ)‖) * ‖δ‖) * ‖δ‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by rw [hn]; ring

/-- The `LH/12` part of Lemma 2.1, from an operator-Lipschitz Hessian. -/
theorem trapezoidDefect_lipschitz_bound (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (LH : ℝ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ LH * ‖x - y‖) (x y : E) :
    |trapezoidDefect U g x y| ≤ LH / 12 * ‖y - x‖ ^ 3 := by
  have h1 : x + (1 : ℝ) • (y - x) = y := by module
  have hb := scalar_trapezoid_lipschitz_bound
    (fun t : ℝ => U (x + t • (y - x)))
    (fun t : ℝ => ⟪g (x + t • (y - x)), y - x⟫_ℝ)
    (fun t : ℝ => ⟪A (x + t • (y - x)) (y - x), y - x⟫_ℝ)
    (potential_line_derivative U g hgrad x (y - x))
    (gradient_line_derivative g A hHess x (y - x))
    (hessian_line_continuous A hA x (y - x)) (LH * ‖y - x‖ ^ 3)
    (fun t _ => hessian_line_lipschitz A LH hLip x (y - x) t (1 / 2))
  simpa only [h1, zero_smul, add_zero, trapezoidDefect, inner_add_left,
    mul_div_assoc, div_mul_eq_mul_div] using hb

/-- Multivariate descent lemma from the actual gradient and Hessian. -/
theorem potential_descent_bound (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (L : ℝ)
    (hcurv : ∀ x u, ⟪A x u, u⟫_ℝ ≤ L * ‖u‖ ^ 2) (x y : E) :
    U y ≤ U x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  have h1 : x + (1 : ℝ) • (y - x) = y := by module
  have hb := scalar_descent_bound
    (fun t : ℝ => U (x + t • (y - x)))
    (fun t : ℝ => ⟪g (x + t • (y - x)), y - x⟫_ℝ)
    (fun t : ℝ => ⟪A (x + t • (y - x)) (y - x), y - x⟫_ℝ)
    (potential_line_derivative U g hgrad x (y - x))
    (gradient_line_derivative g A hHess x (y - x))
    (hessian_line_continuous A hA x (y - x)) (L * ‖y - x‖ ^ 2)
    (fun t _ => hcurv (x + t • (y - x)) (y - x))
  simpa only [h1, zero_smul, add_zero, mul_div_assoc, div_mul_eq_mul_div] using hb

theorem gradient_norm_sq_le_energy (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (L : ℝ) (hL : 0 < L)
    (hcurv : ∀ x u, ⟪A x u, u⟫_ℝ ≤ L * ‖u‖ ^ 2)
    (Ustar : ℝ) (hmin : ∀ y, Ustar ≤ U y) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * L * (U x - Ustar) := by
  have hd := potential_descent_bound U g A hgrad hHess hA L hcurv x
    (x - (1 / L) • g x)
  have hδ : (x - (1 / L) • g x) - x = -((1 / L) • g x) := by module
  rw [hδ, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL), mul_pow] at hd
  have heq : U x + -(1 / L * ‖g x‖ ^ 2) + L / 2 * ((1 / L) ^ 2 * ‖g x‖ ^ 2) =
      U x - ‖g x‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [heq] at hd
  have he : ‖g x‖ ^ 2 / (2 * L) ≤ U x - Ustar := by
    linarith [hmin (x - (1 / L) • g x)]
  have hp : 0 < 2 * L := by positivity
  have he' := (div_le_iff₀ hp).mp he
  nlinarith

theorem gradientCorrection_bound (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (L : ℝ) (hL : 0 < L)
    (hcurv : ∀ x u, ⟪A x u, u⟫_ℝ ≤ L * ‖u‖ ^ 2)
    (Ustar : ℝ) (hmin : ∀ y, Ustar ≤ U y) (h : ℝ) (x : E) :
    0 ≤ gradientCorrection g h x ∧
      gradientCorrection g h x ≤ (h ^ 2 * L / 4) * (U x - Ustar) := by
  rw [gradientCorrection_eq_norm]
  constructor
  · positivity
  · have hb := gradient_norm_sq_le_energy U g A hgrad hHess hA L hL hcurv Ustar hmin x
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ h ^ 2 / 8)
    nlinarith

theorem verlet_trapezoidDefect_bound (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (L h : ℝ)
    (hcurv : ∀ x u, 0 ≤ ⟪A x u, u⟫_ℝ ∧ ⟪A x u, u⟫_ℝ ≤ L * ‖u‖ ^ 2)
    (z : E × E) :
    |trapezoidDefect U g z.1 (verlet g h z).1| ≤
      L * h ^ 2 / 8 * ‖flightVelocity g h z‖ ^ 2 := by
  have hb := trapezoidDefect_bound U g A hgrad hHess hA L hcurv z.1 (verlet g h z).1
  have hd : (verlet g h z).1 - z.1 = h • flightVelocity g h z := by
    rw [verlet_position]
    module
  rw [hd, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hb
  convert hb using 1 <;> ring

theorem verlet_trapezoidDefect_lipschitz_bound (U : E → ℝ) (g : E → E)
    (A : E → E →L[ℝ] E) (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (LH h : ℝ) (hh : 0 ≤ h)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ LH * ‖x - y‖) (z : E × E) :
    |trapezoidDefect U g z.1 (verlet g h z).1| ≤
      LH / 12 * h ^ 3 * ‖flightVelocity g h z‖ ^ 3 := by
  have hb := trapezoidDefect_lipschitz_bound U g A hgrad hHess hA LH hLip
    z.1 (verlet g h z).1
  have hd : (verlet g h z).1 - z.1 = h • flightVelocity g h z := by
    rw [verlet_position]
    module
  rw [hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, mul_pow] at hb
  convert hb using 1 <;> ring

end MultivariateRemainder

end

end PersistencePays

#print axioms PersistencePays.verlet_energy_identity
#print axioms PersistencePays.flipped_verlet_involutive
#print axioms PersistencePays.quadratic_trapezoidDefect
#print axioms PersistencePays.scalar_trapezoid_remainder
#print axioms PersistencePays.trapezoidDefect_bound
#print axioms PersistencePays.trapezoidDefect_lipschitz_bound
#print axioms PersistencePays.gradientCorrection_bound
#print axioms PersistencePays.verlet_trapezoidDefect_bound
#print axioms PersistencePays.verlet_trapezoidDefect_lipschitz_bound
