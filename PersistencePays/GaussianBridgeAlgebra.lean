import PersistencePays.NonnegativeBridge

/-!
Explicit isotropic Gaussian kernels, their normalization, and Brownian bridge
factorization. These instantiate the measure-theoretic bridge inequality without
assuming Gaussian identities as proof axioms.
-/

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace PersistencePays

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def heatConstant (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (s : ℝ) : ℝ :=
  (2 * Real.pi * s) ^ (-((Module.finrank ℝ E : ℝ) / 2))

noncomputable def heatReal (s : ℝ) (x : E) : ℝ :=
  heatConstant E s * exp (-‖x‖ ^ 2 / (2 * s))

noncomputable def heatDensity (s : ℝ) (x : E) : ℝ≥0∞ := ENNReal.ofReal (heatReal s x)

theorem heatConstant_pos {s : ℝ} (hs : 0 < s) : 0 < heatConstant E s := by
  apply rpow_pos_of_pos
  positivity

theorem heatReal_pos {s : ℝ} (hs : 0 < s) (x : E) : 0 < heatReal s x :=
  mul_pos (heatConstant_pos hs) (exp_pos _)

theorem measurable_heatDensity (s : ℝ) : Measurable (heatDensity (E := E) s) := by
  unfold heatDensity heatReal
  fun_prop

theorem bridge_gaussian_radial_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => exp (-b * ‖x‖ ^ 2)) volume := by
  by_contra hi
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  rw [integral_undef hi] at h
  have hp : 0 < (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2) :=
    rpow_pos_of_pos (div_pos pi_pos hb) _
  linarith

theorem heatReal_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (heatReal (E := E) s) volume := by
  have hi := (bridge_gaussian_radial_integrable (E := E) (show 0 < 1 / (2 * s) by positivity)).const_mul
    (heatConstant E s)
  convert hi using 1
  funext x
  unfold heatReal
  congr 2
  ring

theorem integral_heatReal {s : ℝ} (hs : 0 < s) :
    (∫ x : E, heatReal s x) = 1 := by
  have hbase : 0 < 2 * Real.pi * s := by positivity
  have hnorm : (∫ x : E, exp (-‖x‖ ^ 2 / (2 * s))) =
      (2 * Real.pi * s) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E)
      (show 0 < 1 / (2 * s) by positivity)
    convert h using 1
    · congr 1
      funext x
      congr 1
      ring
    · congr 1
      field_simp
  unfold heatReal heatConstant
  rw [integral_const_mul, hnorm, ← rpow_add hbase]
  simp

theorem lintegral_heatDensity {s : ℝ} (hs : 0 < s) :
    (∫⁻ x : E, heatDensity s x) = 1 := by
  unfold heatDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (heatReal_integrable hs)
    (Filter.Eventually.of_forall (fun x => (heatReal_pos hs x).le)), integral_heatReal hs]
  norm_num

theorem heatConstant_bridge {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    heatConstant E 1 * heatConstant E (t * (1 - t)) =
      heatConstant E t * heatConstant E (1 - t) := by
  unfold heatConstant
  rw [← mul_rpow (by positivity : 0 ≤ 2 * Real.pi * 1)
      (by positivity : 0 ≤ 2 * Real.pi * (t * (1 - t))),
    ← mul_rpow (by positivity : 0 ≤ 2 * Real.pi * t)
      (by positivity : 0 ≤ 2 * Real.pi * (1 - t))]
  congr 1
  ring

theorem gaussian_bridge_exponent {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (u v : E) :
    -‖v‖ ^ 2 / 2 + -‖u‖ ^ 2 / (2 * (t * (1 - t))) =
      -‖u + t • v‖ ^ 2 / (2 * t) + -‖u - (1 - t) • v‖ ^ 2 / (2 * (1 - t)) := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  field_simp [ne_of_gt ht, ne_of_gt (sub_pos.mpr ht1)]
  ring

theorem heatReal_bridge {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (u v : E) :
    heatReal 1 v * heatReal (t * (1 - t)) u =
      heatReal t (u + t • v) * heatReal (1 - t) (u - (1 - t) • v) := by
  unfold heatReal
  calc
    _ = (heatConstant E 1 * heatConstant E (t * (1 - t))) *
        exp (-‖v‖ ^ 2 / 2 + -‖u‖ ^ 2 / (2 * (t * (1 - t)))) := by
      rw [exp_add]
      ring
    _ = _ := by
      rw [heatConstant_bridge ht ht1, gaussian_bridge_exponent ht ht1, exp_add]
      ring

theorem heatDensity_bridge {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (u v : E) :
    heatDensity 1 v * heatDensity (t * (1 - t)) u =
      heatDensity t (u + t • v) * heatDensity (1 - t) (u - (1 - t) • v) := by
  unfold heatDensity
  rw [← ENNReal.ofReal_mul (heatReal_pos (by norm_num : (0 : ℝ) < 1) v).le,
    ← ENNReal.ofReal_mul (heatReal_pos ht (u + t • v)).le, heatReal_bridge ht ht1]

/-- Lemma 3.2 for the standard isotropic Gaussian and all interior interpolation
    times, with arbitrary measurable probability densities and no moments. -/
theorem gaussian_bridge_integral_bound_interior
    (p q : E → ℝ≥0∞) (hp : Measurable p) (hq : Measurable q)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (∫⁻ y, bridgeMarginal p q (heatDensity 1) t y ^ (1 / 2 : ℝ)) ≤ 1 := by
  apply bridge_square_root_bound p q (heatDensity 1)
    (heatDensity (t * (1 - t))) (heatDensity t) (heatDensity (1 - t)) t
    hp hq (measurable_heatDensity _) (measurable_heatDensity _)
    (measurable_heatDensity _) (measurable_heatDensity _) hp1 hq1
    (lintegral_heatDensity (by positivity)) (lintegral_heatDensity ht)
    (lintegral_heatDensity (sub_pos.mpr ht1))
  exact heatDensity_bridge ht ht1

/-- Lemma 3.2 for the standard isotropic Gaussian, including both endpoints. -/
theorem gaussian_bridge_integral_bound
    (p q : E → ℝ≥0∞) (hp : Measurable p) (hq : Measurable q)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ y, bridgeMarginal p q (heatDensity 1) t y ^ (1 / 2 : ℝ)) ≤ 1 := by
  rcases eq_or_lt_of_le ht with h0 | ht
  · subst t
    exact bridge_square_root_bound_zero p q (heatDensity 1) hp hq (measurable_heatDensity 1)
      hp1 hq1 (lintegral_heatDensity (by norm_num))
  rcases eq_or_lt_of_le ht1 with h1 | ht1
  · subst t
    exact bridge_square_root_bound_one p q (heatDensity 1) hp hq (measurable_heatDensity 1)
      hp1 hq1 (lintegral_heatDensity (by norm_num))
  exact gaussian_bridge_integral_bound_interior p q hp hq hp1 hq1 ht ht1

end PersistencePays

#print axioms PersistencePays.gaussian_bridge_integral_bound_interior
#print axioms PersistencePays.gaussian_bridge_integral_bound
