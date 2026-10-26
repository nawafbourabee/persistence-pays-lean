import PersistencePays.AffineGaussianBridge

/-! Conditional Cauchy--Schwarz turns the Gaussian bridge inequality into the
four-density affinity bound needed for the entropy comparison. -/

open MeasureTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- Division by a marginal mass yields a subprobability even at the exceptional
values zero and infinity, using the standard nonnegative-integral conventions. -/
theorem lintegral_normalized_density_le_one
    (ν : Measure T) (r : T → ℝ≥0∞) (hr : Measurable r) :
    (∫⁻ v, r v / (∫⁻ w, r w ∂ν) ∂ν) ≤ 1 := by
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ hr]
  exact ENNReal.mul_inv_le_one _

theorem conditional_affinity_bound (μ : Measure S) (ν : Measure T) [SFinite ν]
    (r b : S × T → ℝ≥0∞) (hr : Measurable r) (hb : Measurable b) :
    (∫⁻ y, ∫⁻ v,
      ((r (y, v) / (∫⁻ w, r (y, w) ∂ν)) * b (y, v)) ^ (1 / 2 : ℝ) ∂ν ∂μ) ≤
      ∫⁻ y, (∫⁻ v, b (y, v) ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
  apply lintegral_mono
  intro y
  have hry : Measurable (fun v => r (y, v)) := hr.comp (measurable_const.prodMk measurable_id)
  have hby : Measurable (fun v => b (y, v)) := hb.comp (measurable_const.prodMk measurable_id)
  have hc := lintegral_sqrt_mul_le ν
    (fun v => r (y, v) / (∫⁻ w, r (y, w) ∂ν)) (fun v => b (y, v))
    (hry.div_const _) hby
  calc
    _ ≤ (∫⁻ v, r (y, v) / (∫⁻ w, r (y, w) ∂ν) ∂ν) ^ (1 / 2 : ℝ) *
        (∫⁻ v, b (y, v) ∂ν) ^ (1 / 2 : ℝ) := hc
    _ ≤ 1 * (∫⁻ v, b (y, v) ∂ν) ^ (1 / 2 : ℝ) := by
      gcongr
      exact ENNReal.rpow_le_one (lintegral_normalized_density_le_one ν _ hry) (by norm_num)
    _ = _ := one_mul _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Full Gaussian affinity estimate. The joint density `r` may have no moments,
and no integrability is imposed on its logarithm. -/
theorem gaussian_bridge_affinity
    (e : E ≃L[ℝ] E) (b : E) (r : E × E → ℝ≥0∞)
    (p q : E → ℝ≥0∞) (hr : Measurable r) (hp : Measurable p) (hq : Measurable q)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ z, ((r z / (∫⁻ w, r (z.1, w))) *
      (p (z.1 - t • z.2) * q (z.1 + (1 - t) • z.2) * affineGaussianDensity e b z.2)) ^
        (1 / 2 : ℝ) ∂(volume : Measure E).prod volume) ≤ 1 := by
  let B : E × E → ℝ≥0∞ := fun z =>
    p (z.1 - t • z.2) * q (z.1 + (1 - t) • z.2) * affineGaussianDensity e b z.2
  have hB : Measurable B := by
    apply Measurable.mul
    · exact (hp.comp (measurable_fst.sub (measurable_snd.const_smul t))).mul
        (hq.comp (measurable_fst.add (measurable_snd.const_smul (1 - t))))
    · exact (measurable_affineGaussianDensity e b).comp measurable_snd
  have hm : Measurable (fun y => ∫⁻ w, r (y, w)) :=
    Measurable.lintegral_prod_right (show Measurable (fun z : E × E => r (z.1, z.2)) from hr)
  have hF : Measurable (fun z : E × E =>
      ((r z / (∫⁻ w, r (z.1, w))) * B z) ^ (1 / 2 : ℝ)) :=
    ((hr.div (hm.comp measurable_fst)).mul hB).pow_const _
  change (∫⁻ z, ((r z / (∫⁻ w, r (z.1, w))) * B z) ^ (1 / 2 : ℝ)
    ∂(volume : Measure E).prod volume) ≤ 1
  rw [lintegral_prod _ hF.aemeasurable]
  exact (conditional_affinity_bound volume volume r B hr hB).trans
    (affine_gaussian_bridge_integral_bound e b p q hp hq hp1 hq1 ht ht1)

lemma affineGaussianDensity_ne_zero (e : E ≃L[ℝ] E) (b x : E) :
    affineGaussianDensity e b x ≠ 0 := by
  unfold affineGaussianDensity ellipticHeat inverseJacobian heatDensity
  apply mul_ne_zero
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact abs_pos.mpr (inv_ne_zero e.toLinearEquiv.isUnit_det'.ne_zero)
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (heatReal_pos (by norm_num) _))

lemma affineGaussianDensity_ne_top (e : E ≃L[ℝ] E) (b x : E) :
    affineGaussianDensity e b x ≠ ∞ := by
  unfold affineGaussianDensity ellipticHeat inverseJacobian heatDensity
  finiteness

lemma gaussian_affinity_factor (r p q a g : ℝ≥0∞) (hg0 : g ≠ 0) (hgfin : g ≠ ∞) :
    r * (p * g) * (q * g) / (a * g) = (r / a) * (p * q * g) := by
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr hgfin) (Or.inr hg0), div_eq_mul_inv]
  calc
    _ = (r * a⁻¹ * (p * q * g)) * (g * g⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hg0 hgfin, mul_one]

/-- The same affinity written directly in terms of the three Gaussian-product
reference densities used in the relative-entropy comparison. -/
theorem gaussian_reference_affinity
    (e : E ≃L[ℝ] E) (b : E) (r : E × E → ℝ≥0∞)
    (p q : E → ℝ≥0∞) (hr : Measurable r) (hp : Measurable p) (hq : Measurable q)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ z, (r z * (p (z.1 - t • z.2) * affineGaussianDensity e b z.2) *
      (q (z.1 + (1 - t) • z.2) * affineGaussianDensity e b z.2) /
      ((∫⁻ w, r (z.1, w)) * affineGaussianDensity e b z.2)) ^ (1 / 2 : ℝ)
        ∂(volume : Measure E).prod volume) ≤ 1 := by
  simp_rw [gaussian_affinity_factor _ _ _ _ _ (affineGaussianDensity_ne_zero e b _)
    (affineGaussianDensity_ne_top e b _)]
  exact gaussian_bridge_affinity e b r p q hr hp hq hp1 hq1 ht ht1

end
end PersistencePays
#print axioms PersistencePays.gaussian_bridge_affinity

#print axioms PersistencePays.gaussian_reference_affinity
