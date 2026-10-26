import PersistencePays.HeatKernelInequality

/-!
The change-of-variables and Tonelli part of Lemma 3.2. The only Gaussian-specific
input is the pointwise bridge identity; no integrability or moment premise is
substituted for the conclusion.
-/

open MeasureTheory
open scoped ENNReal

namespace PersistencePays

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem bridge_first_shear_preserving (t : ℝ) :
    MeasurePreserving (fun z : E × E => (z.1 - t • z.2, z.2))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) := by
  have hs : MeasurePreserving (Prod.swap : E × E → E × E)
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
    Measure.measurePreserving_swap
  have hsecond : MeasurePreserving (fun z : E × E => (z.1, z.2 - t • z.1))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) := by
    exact (MeasurePreserving.id (volume : Measure E)).skew_product
      (measurable_snd.sub (measurable_fst.const_smul t))
      (Filter.Eventually.of_forall (fun x =>
        (measurePreserving_sub_right (volume : Measure E) (t • x)).map_eq))
  exact hs.comp (hsecond.comp hs)

/-- The linear-affine substitution in the bridge proof has Jacobian modulus one.
    This is proved as a composition of measure-preserving shears and reflection. -/
theorem bridge_coordinates_preserving (y : E) (t : ℝ) :
    MeasurePreserving
      (fun z : E × E => (y - z.1 - t • z.2, y - z.1 - t • z.2 + z.2))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) := by
  have hr : MeasurePreserving (fun u : E => y - u) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure E) y).comp
        (Measure.measurePreserving_neg (volume : Measure E))
  exact (measurePreserving_prod_add (volume : Measure E) volume).comp
    ((bridge_first_shear_preserving t).comp (hr.prod (MeasurePreserving.id volume)))

noncomputable def bridgeMarginal (p q g : E → ℝ≥0∞) (t : ℝ) (y : E) : ℝ≥0∞ :=
  ∫⁻ v, p (y - t • v) * q (y + (1 - t) • v) * g v

theorem measurable_bridgeMarginal (p q g : E → ℝ≥0∞) (t : ℝ)
    (hp : Measurable p) (hq : Measurable q) (hg : Measurable g) :
    Measurable (bridgeMarginal p q g t) := by
  apply Measurable.lintegral_prod_right
  exact ((hp.comp (measurable_fst.sub (measurable_snd.const_smul t))).mul
    (hq.comp (measurable_fst.add (measurable_snd.const_smul (1 - t))))).mul
      (hg.comp measurable_snd)

/-- Integrating the pointwise bridge identity yields the convolution
    factorization, for arbitrary nonnegative measurable functions. -/
theorem nonnegative_bridge_factorization
    (p q g G G₁ G₂ : E → ℝ≥0∞) (t : ℝ)
    (hp : Measurable p) (hq : Measurable q) (hg : Measurable g)
    (hG : Measurable G) (hG₁ : Measurable G₁) (hG₂ : Measurable G₂)
    (hbridge : ∀ u v, g v * G u = G₁ (u + t • v) * G₂ (u - (1 - t) • v))
    (y : E) :
    nonnegativeConvolution (bridgeMarginal p q g t) G y =
      nonnegativeConvolution G₁ p y * nonnegativeConvolution G₂ q y := by
  let F : E × E → ℝ≥0∞ := fun z =>
    (G₁ (y - z.1) * p z.1) * (G₂ (y - z.2) * q z.2)
  have hF : Measurable F := by
    exact ((hG₁.comp (measurable_const.sub measurable_fst)).mul
      (hp.comp measurable_fst)).mul
      ((hG₂.comp (measurable_const.sub measurable_snd)).mul (hq.comp measurable_snd))
  let M : E × E → E × E := fun z =>
    (y - z.1 - t • z.2, y - z.1 - t • z.2 + z.2)
  have hM : MeasurePreserving M ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) := bridge_coordinates_preserving y t
  have hid (u v : E) :
      p (y - u - t • v) * q (y - u + (1 - t) • v) * g v * G u = F (M (u, v)) := by
    have h1 : y - (y - u - t • v) = u + t • v := by abel
    have h2 : y - (y - u - t • v + v) = u - (1 - t) • v := by module
    have h3 : y - u - t • v + v = y - u + (1 - t) • v := by module
    dsimp [F, M]
    rw [h1, h2, h3]
    calc
      _ = (p (y - u - t • v) * q (y - u + (1 - t) • v)) * (g v * G u) := by ring
      _ = _ := by rw [hbridge]; ring
  calc
    nonnegativeConvolution (bridgeMarginal p q g t) G y =
        ∫⁻ u, ∫⁻ v, F (M (u, v)) := by
      unfold nonnegativeConvolution bridgeMarginal
      apply lintegral_congr
      intro u
      have hv : Measurable (fun v => p (y - u - t • v) * q (y - u + (1 - t) • v) * g v) := by
        fun_prop
      rw [← lintegral_mul_const (G u) hv]
      exact lintegral_congr (hid u)
    _ = ∫⁻ z, F (M z) ∂((volume : Measure E).prod volume) :=
      (lintegral_prod _ (hF.comp hM.measurable).aemeasurable).symm
    _ = ∫⁻ z, F z ∂((volume : Measure E).prod volume) := hM.lintegral_comp hF
    _ = nonnegativeConvolution G₁ p y * nonnegativeConvolution G₂ q y := by
      rw [lintegral_prod _ hF.aemeasurable]
      dsimp [F, nonnegativeConvolution]
      have h1 : Measurable (fun u => G₁ (y - u) * p u) := by fun_prop
      have h2 : Measurable (fun v => G₂ (y - v) * q v) := by fun_prop
      simp_rw [lintegral_const_mul _ h2]
      exact lintegral_mul_const _ h1

/-- The complete no-moment integral implication of a normalized bridge identity.
    The Gaussian specialization requires only its explicit pointwise identity and
    the four kernel normalizations, rather than additional analytic assumptions. -/
theorem bridge_square_root_bound
    (p q g G G₁ G₂ : E → ℝ≥0∞) (t : ℝ)
    (hp : Measurable p) (hq : Measurable q) (hg : Measurable g)
    (hG : Measurable G) (hG₁ : Measurable G₁) (hG₂ : Measurable G₂)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1)
    (hG1 : ∫⁻ x, G x = 1) (hG₁1 : ∫⁻ x, G₁ x = 1) (hG₂1 : ∫⁻ x, G₂ x = 1)
    (hbridge : ∀ u v, g v * G u = G₁ (u + t • v) * G₂ (u - (1 - t) • v)) :
    (∫⁻ y, bridgeMarginal p q g t y ^ (1 / 2 : ℝ)) ≤ 1 := by
  apply square_root_mass_le_of_convolution_factorization
    (bridgeMarginal p q g t) G (nonnegativeConvolution G₁ p) (nonnegativeConvolution G₂ q)
    (measurable_bridgeMarginal p q g t hp hq hg) hG
    (measurable_nonnegativeConvolution G₁ p hG₁ hp)
    (measurable_nonnegativeConvolution G₂ q hG₂ hq) hG1
  · rw [lintegral_nonnegativeConvolution G₁ p hG₁ hp, hG₁1, hp1, one_mul]
  · rw [lintegral_nonnegativeConvolution G₂ q hG₂ hq, hG₂1, hq1, one_mul]
  · exact nonnegative_bridge_factorization p q g G G₁ G₂ t hp hq hg hG hG₁ hG₂ hbridge

/-- The first endpoint needs no Gaussian property. -/
theorem bridge_square_root_bound_zero
    (p q g : E → ℝ≥0∞) (hp : Measurable p) (hq : Measurable q) (hg : Measurable g)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1) (hg1 : ∫⁻ x, g x = 1) :
    (∫⁻ y, bridgeMarginal p q g 0 y ^ (1 / 2 : ℝ)) ≤ 1 := by
  let Q : E → ℝ≥0∞ := fun y => ∫⁻ v, q (y + v) * g v
  have hQ : Measurable Q :=
    Measurable.lintegral_prod_right
      ((hq.comp (measurable_fst.add measurable_snd)).mul (hg.comp measurable_snd))
  have hQ1 : ∫⁻ y, Q y = 1 := by
    dsimp [Q]
    rw [lintegral_lintegral_swap]
    · have hinner (v : E) : (∫⁻ y, q (y + v) * g v) = g v := by
        have hy : Measurable (fun y => q (y + v)) := hq.comp (measurable_id.add_const v)
        rw [lintegral_mul_const _ hy,
          (measurePreserving_add_right (volume : Measure E) v).lintegral_comp hq,
          hq1, one_mul]
      simp_rw [hinner]
      exact hg1
    · exact ((hq.comp (measurable_fst.add measurable_snd)).mul
        (hg.comp measurable_snd)).aemeasurable
  have hid (y : E) : bridgeMarginal p q g 0 y = p y * Q y := by
    unfold bridgeMarginal
    simp only [zero_smul, sub_zero, one_smul]
    dsimp [Q]
    have hv : Measurable (fun v => q (y + v) * g v) := by fun_prop
    rw [← lintegral_const_mul (p y) hv]
    apply lintegral_congr
    intro v
    ring
  simp_rw [hid]
  exact (lintegral_sqrt_mul_le volume p Q hp hQ).trans_eq
    (by rw [hp1, hQ1, ENNReal.one_rpow, one_mul])

/-- The second endpoint also holds for any probability density in velocity. -/
theorem bridge_square_root_bound_one
    (p q g : E → ℝ≥0∞) (hp : Measurable p) (hq : Measurable q) (hg : Measurable g)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1) (hg1 : ∫⁻ x, g x = 1) :
    (∫⁻ y, bridgeMarginal p q g 1 y ^ (1 / 2 : ℝ)) ≤ 1 := by
  have hP := measurable_nonnegativeConvolution p g hp hg
  have hP1 : ∫⁻ y, nonnegativeConvolution p g y = 1 := by
    rw [lintegral_nonnegativeConvolution p g hp hg, hp1, hg1, one_mul]
  have hid (y : E) : bridgeMarginal p q g 1 y = q y * nonnegativeConvolution p g y := by
    unfold bridgeMarginal nonnegativeConvolution
    simp only [one_smul, sub_self, zero_smul, add_zero]
    have hv : Measurable (fun v => p (y - v) * g v) := by fun_prop
    rw [← lintegral_const_mul (q y) hv]
    apply lintegral_congr
    intro v
    ring
  simp_rw [hid]
  exact (lintegral_sqrt_mul_le volume q (nonnegativeConvolution p g) hq hP).trans_eq
    (by rw [hq1, hP1, ENNReal.one_rpow, one_mul])

end PersistencePays

#print axioms PersistencePays.bridge_square_root_bound
