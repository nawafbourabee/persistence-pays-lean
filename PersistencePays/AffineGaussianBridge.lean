import PersistencePays.GaussianBridgeAlgebra

/-!
The Gaussian bridge bound for every nonsingular affine Gaussian density. The
covariance is parametrized by an invertible square-root map, and its determinant
normalization and all changes of variables are proved explicitly.
-/

open MeasureTheory
open scoped ENNReal

namespace PersistencePays

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def inverseJacobian (e : E ≃L[ℝ] E) : ℝ≥0∞ :=
  ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹|

/-- Density with covariance `s A A*`, where `A=e` is invertible. -/
noncomputable def ellipticHeat (e : E ≃L[ℝ] E) (s : ℝ) (x : E) : ℝ≥0∞ :=
  inverseJacobian e * heatDensity s (e.symm x)

theorem measurable_ellipticHeat (e : E ≃L[ℝ] E) (s : ℝ) :
    Measurable (ellipticHeat e s) :=
  measurable_const.mul ((measurable_heatDensity s).comp e.symm.continuous.measurable)

theorem map_volume_linearEquiv (e : E ≃L[ℝ] E) :
    Measure.map e (volume : Measure E) = inverseJacobian e • volume := by
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    e.toLinearEquiv.isUnit_det'.ne_zero

theorem lintegral_ellipticHeat (e : E ≃L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    (∫⁻ x, ellipticHeat e s x) = 1 := by
  have hf : Measurable (fun x => heatDensity s (e.symm x)) :=
    (measurable_heatDensity s).comp e.symm.continuous.measurable
  unfold ellipticHeat
  rw [lintegral_const_mul _ hf]
  change inverseJacobian e • (∫⁻ x, heatDensity s (e.symm x) ∂volume) = 1
  rw [← lintegral_smul_measure,
    ← map_volume_linearEquiv e, lintegral_map hf e.continuous.measurable]
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    (lintegral_heatDensity (E := E) hs)

theorem ellipticHeat_bridge (e : E ≃L[ℝ] E) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (u v : E) :
    ellipticHeat e 1 v * ellipticHeat e (t * (1 - t)) u =
      ellipticHeat e t (u + t • v) * ellipticHeat e (1 - t) (u - (1 - t) • v) := by
  unfold ellipticHeat
  simp only [map_add, map_sub, map_smul]
  calc
    _ = (inverseJacobian e * inverseJacobian e) *
        (heatDensity 1 (e.symm v) * heatDensity (t * (1 - t)) (e.symm u)) := by ring
    _ = _ := by rw [heatDensity_bridge ht ht1]; ring

/-- Explicit density of the affine Gaussian `b + A Z`, where `Z` is standard and
    `A=e` is invertible. Its normalization is derived below. -/
noncomputable def affineGaussianDensity (e : E ≃L[ℝ] E) (b x : E) : ℝ≥0∞ :=
  ellipticHeat e 1 (x - b)

theorem measurable_affineGaussianDensity (e : E ≃L[ℝ] E) (b : E) :
    Measurable (affineGaussianDensity e b) :=
  (measurable_ellipticHeat e 1).comp (measurable_id.sub_const b)

theorem lintegral_affineGaussianDensity (e : E ≃L[ℝ] E) (b : E) :
    (∫⁻ x, affineGaussianDensity e b x) = 1 := by
  unfold affineGaussianDensity
  rw [(measurePreserving_sub_right (volume : Measure E) b).lintegral_comp
    (measurable_ellipticHeat e 1)]
  exact lintegral_ellipticHeat e (by norm_num)

/-- Lemma 3.2 for arbitrary nonsingular affine Gaussian densities, without moment
    assumptions on the measurable probability densities `p` and `q`. -/
theorem affine_gaussian_bridge_integral_bound
    (e : E ≃L[ℝ] E) (b : E) (p q : E → ℝ≥0∞)
    (hp : Measurable p) (hq : Measurable q)
    (hp1 : ∫⁻ x, p x = 1) (hq1 : ∫⁻ x, q x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ y, bridgeMarginal p q (affineGaussianDensity e b) t y ^ (1 / 2 : ℝ)) ≤ 1 := by
  rcases eq_or_lt_of_le ht with h0 | ht
  · subst t
    exact bridge_square_root_bound_zero p q _ hp hq (measurable_affineGaussianDensity e b)
      hp1 hq1 (lintegral_affineGaussianDensity e b)
  rcases eq_or_lt_of_le ht1 with h1 | ht1
  · subst t
    exact bridge_square_root_bound_one p q _ hp hq (measurable_affineGaussianDensity e b)
      hp1 hq1 (lintegral_affineGaussianDensity e b)
  let G : E → ℝ≥0∞ := ellipticHeat e (t * (1 - t))
  let G₁ : E → ℝ≥0∞ := fun x => ellipticHeat e t (x - t • b)
  let G₂ : E → ℝ≥0∞ := fun x => ellipticHeat e (1 - t) (x + (1 - t) • b)
  have hG : Measurable G := measurable_ellipticHeat e _
  have hG₁ : Measurable G₁ :=
    (measurable_ellipticHeat e t).comp (measurable_id.sub_const (t • b))
  have hG₂ : Measurable G₂ :=
    (measurable_ellipticHeat e (1 - t)).comp (measurable_id.add_const ((1 - t) • b))
  apply bridge_square_root_bound p q _ G G₁ G₂ t hp hq
    (measurable_affineGaussianDensity e b) hG hG₁ hG₂ hp1 hq1
  · exact lintegral_ellipticHeat e (by positivity)
  · dsimp [G₁]
    rw [(measurePreserving_sub_right (volume : Measure E) (t • b)).lintegral_comp
      (measurable_ellipticHeat e t)]
    exact lintegral_ellipticHeat e ht
  · dsimp [G₂]
    rw [(measurePreserving_add_right (volume : Measure E) ((1 - t) • b)).lintegral_comp
      (measurable_ellipticHeat e (1 - t))]
    exact lintegral_ellipticHeat e (sub_pos.mpr ht1)
  · intro u v
    have h1 : u + t • v - t • b = u + t • (v - b) := by module
    have h2 : u - (1 - t) • v + (1 - t) • b = u - (1 - t) • (v - b) := by module
    dsimp [G, G₁, G₂, affineGaussianDensity]
    rw [h1, h2]
    exact ellipticHeat_bridge e ht ht1 u (v - b)

end PersistencePays

#print axioms PersistencePays.affine_gaussian_bridge_integral_bound
