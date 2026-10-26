import PersistencePays.Volume
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Conditional velocity entropy and absolute continuity under free transport

The definitions use actual push-forward probability laws and mathlib's KL
divergence. Lemma 3.3 is proved from finiteness at the two endpoints; no
joint density, moments, or differential entropy is assumed.
-/

namespace PersistencePays
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def freeTransport (t : ℝ) : E × E → E × E := drift t

theorem measurable_freeTransport (t : ℝ) : Measurable (freeTransport (E := E) t) :=
  (drift_measurePreserving t).measurable

def transportJoint (μ : Measure (E × E)) (t : ℝ) : Measure (E × E) :=
  μ.map (freeTransport t)

def transportPosition (μ : Measure (E × E)) (t : ℝ) : Measure E :=
  (transportJoint μ t).fst

def conditionalGaussianEntropy (μ : Measure (E × E)) (γ : Measure E) (t : ℝ) : ℝ≥0∞ :=
  klDiv (transportJoint μ t) ((transportPosition μ t).prod γ)

instance transportJoint_isProbability (μ : Measure (E × E)) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (transportJoint μ t) :=
  Measure.isProbabilityMeasure_map (measurable_freeTransport t).aemeasurable

instance transportPosition_isProbability (μ : Measure (E × E)) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (transportPosition μ t) := by
  unfold transportPosition
  infer_instance

@[simp] theorem transportJoint_zero (μ : Measure (E × E)) : transportJoint μ 0 = μ := by
  unfold transportJoint freeTransport drift
  have he : (fun z : E × E => (z.1 + (0 : ℝ) • z.2, z.2)) = id := by
    funext z
    simp
  rw [he, Measure.map_id]

@[simp] theorem transportPosition_zero (μ : Measure (E × E)) : transportPosition μ 0 = μ.fst := by
  simp [transportPosition]

theorem transportPosition_one (μ : Measure (E × E)) :
    transportPosition μ 1 = μ.map (fun z : E × E => z.1 + z.2) := by
  unfold transportPosition transportJoint freeTransport drift
  rw [Measure.fst_map_prodMk measurable_snd]
  simp

theorem subtract_after_transport_one (μ : Measure (E × E)) :
    (transportJoint μ 1).map (fun z : E × E => z.1 - z.2) = μ.fst := by
  unfold transportJoint
  have hsub : Measurable (fun z : E × E => z.1 - z.2) := by fun_prop
  rw [Measure.map_map hsub (measurable_freeTransport 1)]
  have he : (fun z : E × E => z.1 - z.2) ∘ freeTransport 1 = Prod.fst := by
    funext z
    simp [Function.comp_def, freeTransport, drift]
  rw [he]
  rfl

/-- Independent addition of an absolutely continuous noise yields a density,
even when the other summand has no density. -/
theorem independent_add_absolutelyContinuous (ν γ : Measure E) [SFinite γ]
    (hγ : γ ≪ (volume : Measure E)) :
    (ν.prod γ).map (fun z : E × E => z.1 + z.2) ≪ (volume : Measure E) :=
  Measure.conv_absolutelyContinuous hγ

/-- The corresponding subtraction statement, by Fubini and translation invariance. -/
theorem independent_sub_absolutelyContinuous (ν γ : Measure E) [SFinite γ]
    (hγ : γ ≪ (volume : Measure E)) :
    (ν.prod γ).map (fun z : E × E => z.1 - z.2) ≪ (volume : Measure E) := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 => ?_)
  have hsub : Measurable (fun z : E × E => z.1 - z.2) := by fun_prop
  rw [Measure.map_apply hsub hs, Measure.prod_apply (hsub hs)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with y
  apply hγ
  change volume ((fun v : E => y - v) ⁻¹' s) = 0
  have hp := Measure.measurePreserving_sub_left (volume : Measure E) y
  rw [← Measure.map_apply hp.measurable hs, hp.map_eq, hs0]

/-- Lemma 3.3 in actual measure-theoretic form. In fact the reference need only
be absolutely continuous, not Gaussian. -/
theorem lemma_3_3 (μ : Measure (E × E)) (γ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hγ : γ ≪ (volume : Measure E))
    (h0 : conditionalGaussianEntropy μ γ 0 ≠ ∞)
    (h1 : conditionalGaussianEntropy μ γ 1 ≠ ∞) :
    μ.fst ≪ (volume : Measure E) ∧
    transportPosition μ 1 ≪ (volume : Measure E) ∧
    μ ≪ (volume : Measure E).prod volume := by
  have ha0 : μ ≪ μ.fst.prod γ := by
    have hh := (klDiv_ne_top_iff.mp h0).1
    simpa only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero] using hh
  have ha1 : transportJoint μ 1 ≪ (transportPosition μ 1).prod γ :=
    (klDiv_ne_top_iff.mp h1).1
  have hx : μ.fst ≪ (volume : Measure E) := by
    have hsub : Measurable (fun z : E × E => z.1 - z.2) := by fun_prop
    have hm := (ha1.map hsub).trans
      (independent_sub_absolutelyContinuous (transportPosition μ 1) γ hγ)
    rwa [subtract_after_transport_one] at hm
  have hy : transportPosition μ 1 ≪ (volume : Measure E) := by
    rw [transportPosition_one]
    exact (ha0.map (measurable_fst.add measurable_snd)).trans
      (independent_add_absolutelyContinuous μ.fst γ hγ)
  exact ⟨hx, hy, ha0.trans (hx.prod hγ)⟩

end
end PersistencePays

#print axioms PersistencePays.lemma_3_3
