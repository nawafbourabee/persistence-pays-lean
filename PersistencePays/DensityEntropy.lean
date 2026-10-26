import PersistencePays.KernelEntropy
import PersistencePays.GaussianBridgeLaw

/-!
Nonnegative-integrand route to the no-moment entropy comparison. Working with
`klFun` avoids subtracting possibly infinite differential entropies.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace PersistencePays

theorem log_le_twice_sqrt_sub_one {x : ℝ} (hx : 0 < x) :
    log x ≤ 2 * (sqrt x - 1) := by
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hx)
  rw [log_sqrt hx.le] at h
  linarith

noncomputable def entropyDensity (r s : ℝ) : ℝ := s * klFun (r / s)

theorem entropyDensity_eq {r s : ℝ} (hs : s ≠ 0) :
    entropyDensity r s = r * log (r / s) + s - r := by
  unfold entropyDensity klFun
  field_simp

/-- Pointwise entropy comparison before integration. The reference-density
    masses appear on both sides so every term is nonnegative. -/
theorem three_density_pointwise (r p q s : ℝ)
    (hr : 0 ≤ r) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hpos : r = 0 ∨ (0 < p ∧ 0 < q ∧ 0 < s)) :
    entropyDensity r s + r + p + q ≤
      entropyDensity r p + entropyDensity r q + 2 * sqrt (r * p * q / s) + s := by
  rcases eq_or_lt_of_le hr with hr0 | hr
  · subst r
    simp [entropyDensity, klFun]
    linarith
  · obtain ⟨hp, hq, hs⟩ := hpos.resolve_left (ne_of_gt hr)
    have hz : 0 < p * q / (r * s) := by positivity
    have hlog := mul_le_mul_of_nonneg_left (log_le_twice_sqrt_sub_one hz) hr.le
    have hlogs : log (p * q / (r * s)) = log p + log q - log r - log s := by
      rw [log_div (mul_ne_zero hp.ne' hq.ne') (mul_ne_zero hr.ne' hs.ne'),
        log_mul hp.ne' hq.ne', log_mul hr.ne' hs.ne']
      ring
    have hsq : sqrt (r * p * q / s) = r * sqrt (p * q / (r * s)) := by
      have hid : r * p * q / s = r ^ 2 * (p * q / (r * s)) := by field_simp
      rw [hid, sqrt_mul (sq_nonneg r), sqrt_sq_eq_abs, abs_of_pos hr]
    rw [hlogs] at hlog
    rw [entropyDensity_eq hs.ne', entropyDensity_eq hp.ne', entropyDensity_eq hq.ne',
      log_div hr.ne' hs.ne', log_div hr.ne' hp.ne', log_div hr.ne' hq.ne', hsq]
    nlinarith

variable {S : Type*} [MeasurableSpace S]

/-- A quotient density reconstructs the first measure whenever its support is
    contained in the support of the reference density. -/
theorem withDensity_ratio
    (ξ : Measure S) (r s : S → ℝ≥0∞) (hr : Measurable r) (hs : Measurable s)
    (hsfinite : ∀ᵐ x ∂ξ, s x ≠ ∞)
    (hsupport : ∀ᵐ x ∂ξ, s x = 0 → r x = 0) :
    (ξ.withDensity s).withDensity (fun x => r x / s x) = ξ.withDensity r := by
  have hratio : Measurable (fun x => r x / s x) := hr.div hs
  rw [← withDensity_mul ξ hs hratio]
  · apply withDensity_congr_ae
    filter_upwards [hsfinite, hsupport] with x hfin hsupp
    by_cases hzero : s x = 0
    · simp [hzero, hsupp hzero]
    · simp only [Pi.mul_apply, div_eq_mul_inv]
      calc
        s x * (r x * (s x)⁻¹) = r x * (s x * (s x)⁻¹) := by ring
        _ = r x := by rw [ENNReal.mul_inv_cancel hzero hfin, mul_one]

/-- Actual KL divergence as a nonnegative integral of the two densities. -/
theorem klDiv_withDensity_eq_lintegral
    (ξ : Measure S) [SigmaFinite ξ] (r s : S → ℝ≥0∞)
    (hr : Measurable r) (hs : Measurable s)
    [IsFiniteMeasure (ξ.withDensity r)] [IsFiniteMeasure (ξ.withDensity s)]
    (hsfinite : ∀ᵐ x ∂ξ, s x ≠ ∞)
    (hsupport : ∀ᵐ x ∂ξ, s x = 0 → r x = 0) :
    klDiv (ξ.withDensity r) (ξ.withDensity s) =
      ∫⁻ x, s x * ENNReal.ofReal (klFun ((r x / s x).toReal)) ∂ξ := by
  have he := withDensity_ratio ξ r s hr hs hsfinite hsupport
  have hac : ξ.withDensity r ≪ ξ.withDensity s := by
    rw [← he]
    exact withDensity_absolutelyContinuous _ _
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hRN : (ξ.withDensity r).rnDeriv (ξ.withDensity s) =ᵐ[ξ.withDensity s]
      (fun x => r x / s x) := by
    rw [← he]
    exact Measure.rnDeriv_withDensity _ (hr.div hs)
  calc
    (∫⁻ x, ENNReal.ofReal (klFun (((ξ.withDensity r).rnDeriv (ξ.withDensity s) x).toReal))
      ∂ξ.withDensity s) = ∫⁻ x, ENNReal.ofReal (klFun ((r x / s x).toReal)) ∂ξ.withDensity s := by
        apply lintegral_congr_ae
        filter_upwards [hRN] with x hx
        rw [hx]
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul ξ hs]
      · rfl
      · fun_prop


noncomputable def ennEntropyDensity (r s : ℝ≥0∞) : ℝ≥0∞ :=
  s * ENNReal.ofReal (klFun ((r / s).toReal))

lemma ennEntropyDensity_ne_top (r s : ℝ≥0∞) (hs : s ≠ ∞) :
    ennEntropyDensity r s ≠ ∞ := ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top

lemma toReal_ennEntropyDensity (r s : ℝ≥0∞) :
    (ennEntropyDensity r s).toReal = entropyDensity r.toReal s.toReal := by
  unfold ennEntropyDensity entropyDensity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (klFun_nonneg ENNReal.toReal_nonneg),
    ENNReal.toReal_div]

/-- Extended-valued version, suited to integration without moment assumptions. -/
theorem three_density_pointwise_ennreal (r p q s : ℝ≥0∞)
    (hr : r ≠ ∞) (hp : p ≠ ∞) (hq : q ≠ ∞) (hs : s ≠ ∞)
    (hsupp : r = 0 ∨ (p ≠ 0 ∧ q ≠ 0 ∧ s ≠ 0)) :
    ennEntropyDensity r s + r + p + q ≤
      ennEntropyDensity r p + ennEntropyDensity r q +
        2 * (r * p * q / s) ^ (1 / 2 : ℝ) + s := by
  rcases hsupp with hr0 | ⟨hp0, hq0, hs0⟩
  · subst r
    simp [ennEntropyDensity, klFun]
    simp [add_comm, add_left_comm, add_assoc]
  · have hf : r * p * q / s ≠ ∞ :=
      ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hr hp) hq) hs0
    have hes := ennEntropyDensity_ne_top r s hs
    have hep := ennEntropyDensity_ne_top r p hp
    have heq := ennEntropyDensity_ne_top r q hq
    have hpow : (r * p * q / s) ^ (1 / 2 : ℝ) ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf
    have hL : ennEntropyDensity r s + r + p + q ≠ ∞ := by
      finiteness
    have hR : ennEntropyDensity r p + ennEntropyDensity r q +
        2 * (r * p * q / s) ^ (1 / 2 : ℝ) + s ≠ ∞ := by
      finiteness
    apply (ENNReal.toReal_le_toReal hL hR).mp
    rw [ENNReal.toReal_add (by finiteness) hq,
      ENNReal.toReal_add (by finiteness) hp, ENNReal.toReal_add hes hr,
      ENNReal.toReal_add (by finiteness) hs,
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add hep heq]
    simp only [toReal_ennEntropyDensity, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow, ENNReal.toReal_div, ← sqrt_eq_rpow]
    apply three_density_pointwise _ _ _ _ ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    exact Or.inr ⟨ENNReal.toReal_pos hp0 hp, ENNReal.toReal_pos hq0 hq,
      ENNReal.toReal_pos hs0 hs⟩

end PersistencePays

#print axioms PersistencePays.three_density_pointwise
#print axioms PersistencePays.klDiv_withDensity_eq_lintegral

#print axioms PersistencePays.three_density_pointwise_ennreal
