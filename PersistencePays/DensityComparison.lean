import PersistencePays.DensityEntropy

/-! A KL comparison from a four-density affinity bound, with no moment or
finite differential-entropy assumptions. -/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace PersistencePays
noncomputable section
variable {S : Type*} [MeasurableSpace S]

lemma measurable_ennEntropyDensity {r s : S → ℝ≥0∞}
    (hr : Measurable r) (hs : Measurable s) :
    Measurable (fun x => ennEntropyDensity (r x) (s x)) := by
  unfold ennEntropyDensity
  fun_prop

lemma lintegral_density_eq_one (ξ : Measure S) (r : S → ℝ≥0∞)
    [IsProbabilityMeasure (ξ.withDensity r)] : (∫⁻ x, r x ∂ξ) = 1 := by
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    using (measure_univ : ξ.withDensity r Set.univ = 1)

lemma density_finite_ae (ξ : Measure S) (r : S → ℝ≥0∞)
    (hr : Measurable r) [IsProbabilityMeasure (ξ.withDensity r)] :
    ∀ᵐ x ∂ξ, r x ≠ ∞ := by
  exact (ae_lt_top hr (by rw [lintegral_density_eq_one ξ r]; norm_num)).mono
    (fun _ h => h.ne)

/-- The central entropy comparison. The affinity is an explicit, nonnegative
integral, rather than an integrability assumption on logarithms. -/
theorem klDiv_comparison_of_affinity
    (ξ : Measure S) [SigmaFinite ξ] (r p q s : S → ℝ≥0∞)
    (hr : Measurable r) (hp : Measurable p) (hq : Measurable q) (hs : Measurable s)
    [IsProbabilityMeasure (ξ.withDensity r)] [IsProbabilityMeasure (ξ.withDensity p)]
    [IsProbabilityMeasure (ξ.withDensity q)] [IsProbabilityMeasure (ξ.withDensity s)]
    (hsupport : ∀ᵐ x ∂ξ, r x = 0 ∨ (p x ≠ 0 ∧ q x ≠ 0 ∧ s x ≠ 0))
    (haff : (∫⁻ x, (r x * p x * q x / s x) ^ (1 / 2 : ℝ) ∂ξ) ≤ 1) :
    klDiv (ξ.withDensity r) (ξ.withDensity s) ≤
      klDiv (ξ.withDensity r) (ξ.withDensity p) +
        klDiv (ξ.withDensity r) (ξ.withDensity q) := by
  have hrf := density_finite_ae ξ r hr
  have hpf := density_finite_ae ξ p hp
  have hqf := density_finite_ae ξ q hq
  have hsf := density_finite_ae ξ s hs
  have hsp : ∀ᵐ x ∂ξ, p x = 0 → r x = 0 := by
    filter_upwards [hsupport] with x hx
    rcases hx with hx | hx
    · exact fun _ => hx
    · exact fun he => False.elim (hx.1 he)
  have hsq : ∀ᵐ x ∂ξ, q x = 0 → r x = 0 := by
    filter_upwards [hsupport] with x hx
    rcases hx with hx | hx
    · exact fun _ => hx
    · exact fun he => False.elim (hx.2.1 he)
  have hss : ∀ᵐ x ∂ξ, s x = 0 → r x = 0 := by
    filter_upwards [hsupport] with x hx
    rcases hx with hx | hx
    · exact fun _ => hx
    · exact fun he => False.elim (hx.2.2 he)
  rw [klDiv_withDensity_eq_lintegral ξ r s hr hs hsf hss,
    klDiv_withDensity_eq_lintegral ξ r p hr hp hpf hsp,
    klDiv_withDensity_eq_lintegral ξ r q hr hq hqf hsq]
  change (∫⁻ x, ennEntropyDensity (r x) (s x) ∂ξ) ≤
    (∫⁻ x, ennEntropyDensity (r x) (p x) ∂ξ) +
      ∫⁻ x, ennEntropyDensity (r x) (q x) ∂ξ
  have hpoint : ∀ᵐ x ∂ξ, ennEntropyDensity (r x) (s x) + r x + p x + q x ≤
      ennEntropyDensity (r x) (p x) + ennEntropyDensity (r x) (q x) +
        2 * (r x * p x * q x / s x) ^ (1 / 2 : ℝ) + s x := by
    filter_upwards [hrf, hpf, hqf, hsf, hsupport] with x h1 h2 h3 h4 h5
    exact three_density_pointwise_ennreal _ _ _ _ h1 h2 h3 h4 h5
  have hint := lintegral_mono_ae hpoint
  have hms := measurable_ennEntropyDensity hr hs
  have hmp := measurable_ennEntropyDensity hr hp
  have hmq := measurable_ennEntropyDensity hr hq
  have hma : Measurable (fun x => (r x * p x * q x / s x) ^ (1 / 2 : ℝ)) := by
    fun_prop
  simp (disch := fun_prop) only [lintegral_add_left, lintegral_const_mul,
    lintegral_density_eq_one] at hint
  have hfin : (3 : ℝ≥0∞) ≠ ∞ := by norm_num
  apply (ENNReal.add_le_add_iff_right hfin).mp
  calc
    (∫⁻ x, ennEntropyDensity (r x) (s x) ∂ξ) + 3 =
        (∫⁻ x, ennEntropyDensity (r x) (s x) ∂ξ) + 1 + 1 + 1 := by ring
    _ ≤ (∫⁻ x, ennEntropyDensity (r x) (p x) ∂ξ) +
        (∫⁻ x, ennEntropyDensity (r x) (q x) ∂ξ) +
        2 * (∫⁻ x, (r x * p x * q x / s x) ^ (1 / 2 : ℝ) ∂ξ) + 1 := hint
    _ ≤ (∫⁻ x, ennEntropyDensity (r x) (p x) ∂ξ) +
        (∫⁻ x, ennEntropyDensity (r x) (q x) ∂ξ) + 2 * 1 + 1 := by gcongr
    _ = _ := by ring

end
end PersistencePays

#print axioms PersistencePays.klDiv_comparison_of_affinity
