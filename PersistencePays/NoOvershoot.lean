import PersistencePays.TransportReferences
import PersistencePays.DensitySupport

/-! The no-overshoot inequality for the actual free-transport joint law and a
nonsingular Gaussian reference. All entropy quantities are actual KL divergence;
no moment or differential-entropy assumptions are used. -/

open MeasureTheory InformationTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma affineGaussianDensity_probability (e : E ≃L[ℝ] E) (b : E) :
    IsProbabilityMeasure ((volume : Measure E).withDensity (affineGaussianDensity e b)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_affineGaussianDensity e b

/-- Proposition 3.1, finite-endpoint case. Finiteness is only used to obtain
joint absolute continuity; the proof does not impose moment hypotheses. -/
theorem no_overshoot_finite_endpoints (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : E ≃L[ℝ] E) (b : E)
    (h0 : conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 0 ≠ ∞)
    (h1 : conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 1 ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) t ≤
      conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 0 +
        conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 1 := by
  let g := affineGaussianDensity e b
  let γ := (volume : Measure E).withDensity g
  let ξ : Measure (E × E) := (volume : Measure E).prod (volume : Measure E)
  let r := transportedDensity μ t
  let P : E × E → ℝ≥0∞ := fun z => positionDensity μ 0 (z.1 - t • z.2) * g z.2
  let Q : E × E → ℝ≥0∞ := fun z => positionDensity μ 1 (z.1 + (1-t) • z.2) * g z.2
  let S : E × E → ℝ≥0∞ := fun z => positionDensity μ t z.1 * g z.2
  have hg : Measurable g := measurable_affineGaussianDensity e b
  letI : IsProbabilityMeasure γ := affineGaussianDensity_probability e b
  have hγ : γ ≪ (volume : Measure E) := withDensity_absolutelyContinuous _ _
  have hγ' : (volume : Measure E) ≪ γ :=
    withDensity_absolutelyContinuous' hg.aemeasurable
      (Filter.Eventually.of_forall (affineGaussianDensity_ne_zero e b))
  have hμ : μ ≪ ξ := (lemma_3_3 μ γ hγ h0 h1).2.2
  have hr : Measurable r := measurable_transportedDensity μ t
  have hP : Measurable P :=
    ((measurable_positionDensity μ 0).comp
      (measurable_fst.sub (measurable_snd.const_smul t))).mul (hg.comp measurable_snd)
  have hQ : Measurable Q :=
    ((measurable_positionDensity μ 1).comp
      (measurable_fst.add (measurable_snd.const_smul (1-t)))).mul (hg.comp measurable_snd)
  have hS : Measurable S :=
    ((measurable_positionDensity μ t).comp measurable_fst).mul (hg.comp measurable_snd)
  have hRlaw : transportJoint μ t = ξ.withDensity r := transportJoint_eq_withDensity μ hμ t
  have hSlaw : (transportPosition μ t).prod γ = ξ.withDensity S :=
    product_reference_eq_withDensity μ hμ g hg t
  have hPlaw : ((transportPosition μ 0).prod γ).map (freeTransport (t-0)) = ξ.withDensity P := by
    simpa only [sub_zero] using endpoint_reference_eq_withDensity μ hμ g hg 0 t
  have hQlaw : ((transportPosition μ 1).prod γ).map (freeTransport (t-1)) = ξ.withDensity Q := by
    have hh := endpoint_reference_eq_withDensity μ hμ g hg 1 t
    convert hh using 1
    apply withDensity_congr_ae
    filter_upwards with z
    change positionDensity μ 1 (z.1 + (1-t) • z.2) * g z.2 =
      positionDensity μ 1 (z.1 - (t-1) • z.2) * g z.2
    have hz : z.1 + (1-t) • z.2 = z.1 - (t-1) • z.2 := by module
    rw [hz]
  letI : IsProbabilityMeasure (ξ.withDensity r) := by rw [← hRlaw]; infer_instance
  letI : IsProbabilityMeasure (ξ.withDensity S) := by rw [← hSlaw]; infer_instance
  letI : IsProbabilityMeasure (ξ.withDensity P) := by
    rw [← hPlaw]
    exact Measure.isProbabilityMeasure_map (measurable_freeTransport _).aemeasurable
  letI : IsProbabilityMeasure (ξ.withDensity Q) := by
    rw [← hQlaw]
    exact Measure.isProbabilityMeasure_map (measurable_freeTransport _).aemeasurable
  have haP : ξ.withDensity r ≪ ξ.withDensity P := by
    have hh := ((klDiv_ne_top_iff.mp h0).1).map (measurable_freeTransport (t-0))
    change (transportJoint μ 0).map (freeTransport (t-0)) ≪
      ((transportPosition μ 0).prod γ).map (freeTransport (t-0)) at hh
    rwa [transportJoint_comp μ 0 t, hRlaw, hPlaw] at hh
  have haQ : ξ.withDensity r ≪ ξ.withDensity Q := by
    have hh := ((klDiv_ne_top_iff.mp h1).1).map (measurable_freeTransport (t-1))
    change (transportJoint μ 1).map (freeTransport (t-1)) ≪
      ((transportPosition μ 1).prod γ).map (freeTransport (t-1)) at hh
    rwa [transportJoint_comp μ 1 t, hRlaw, hQlaw] at hh
  have haS : ξ.withDensity r ≪ ξ.withDensity S := by
    rw [← hRlaw, ← hSlaw]
    exact transportJoint_absolutelyContinuous_position_prod μ hμ γ hγ' t
  have hsupp : ∀ᵐ z ∂ξ, r z = 0 ∨ (P z ≠ 0 ∧ Q z ≠ 0 ∧ S z ≠ 0) := by
    filter_upwards [density_support_of_absolutelyContinuous ξ r P hr hP haP,
      density_support_of_absolutelyContinuous ξ r Q hr hQ haQ,
      density_support_of_absolutelyContinuous ξ r S hr hS haS] with z hp hq hs
    by_cases hz : r z = 0
    · exact Or.inl hz
    · exact Or.inr ⟨fun hh => hz (hp hh), fun hh => hz (hq hh), fun hh => hz (hs hh)⟩
  have haff : (∫⁻ z, (r z * P z * Q z / S z) ^ (1 / 2 : ℝ) ∂ξ) ≤ 1 :=
    gaussian_reference_affinity e b r (positionDensity μ 0) (positionDensity μ 1)
      hr (measurable_positionDensity μ 0) (measurable_positionDensity μ 1)
      (lintegral_positionDensity μ hμ 0) (lintegral_positionDensity μ hμ 1) ht ht1
  have hcomp := klDiv_comparison_of_affinity ξ r P Q S hr hP hQ hS hsupp haff
  have heP : klDiv (ξ.withDensity r) (ξ.withDensity P) = conditionalGaussianEntropy μ γ 0 := by
    rw [← hRlaw, ← hPlaw, ← transportJoint_comp μ 0 t]
    exact klDiv_map_measurableEquiv (freeTransportEquiv (t-0))
      (transportJoint μ 0) ((transportPosition μ 0).prod γ)
  have heQ : klDiv (ξ.withDensity r) (ξ.withDensity Q) = conditionalGaussianEntropy μ γ 1 := by
    rw [← hRlaw, ← hQlaw, ← transportJoint_comp μ 1 t]
    exact klDiv_map_measurableEquiv (freeTransportEquiv (t-1))
      (transportJoint μ 1) ((transportPosition μ 1).prod γ)
  rw [heP, heQ, ← hRlaw, ← hSlaw] at hcomp
  exact hcomp

/-- Proposition 3.1 for arbitrary probability laws and every nonsingular affine
Gaussian reference; infinite endpoint entropies are allowed. -/
theorem proposition_3_1 (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : E ≃L[ℝ] E) (b : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) t ≤
      conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 0 +
        conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 1 := by
  by_cases h0 : conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 0 = ∞
  · simp [h0]
  by_cases h1 : conditionalGaussianEntropy μ (volume.withDensity (affineGaussianDensity e b)) 1 = ∞
  · simp [h1]
  exact no_overshoot_finite_endpoints μ e b h0 h1 ht ht1

/-- The Gaussian reference in actual probability-law form. -/
theorem proposition_3_1_affine_law (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : E ≃L[ℝ] E) (b : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    conditionalGaussianEntropy μ ((ProbabilityTheory.stdGaussian E).map (fun x => e x + b)) t ≤
      conditionalGaussianEntropy μ ((ProbabilityTheory.stdGaussian E).map (fun x => e x + b)) 0 +
        conditionalGaussianEntropy μ ((ProbabilityTheory.stdGaussian E).map (fun x => e x + b)) 1 := by
  rw [← affineGaussianDensity_eq_map_stdGaussian e b]
  exact proposition_3_1 μ e b ht ht1

/-- Standard Gaussian version used by OBABO. -/
theorem proposition_3_1_standard (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    conditionalGaussianEntropy μ (ProbabilityTheory.stdGaussian E) t ≤
      conditionalGaussianEntropy μ (ProbabilityTheory.stdGaussian E) 0 +
        conditionalGaussianEntropy μ (ProbabilityTheory.stdGaussian E) 1 := by
  have hh := proposition_3_1_affine_law μ (ContinuousLinearEquiv.refl ℝ E) 0 ht ht1
  simpa using hh

end
end PersistencePays
#print axioms PersistencePays.proposition_3_1

#print axioms PersistencePays.proposition_3_1_standard
