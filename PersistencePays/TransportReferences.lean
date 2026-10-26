import PersistencePays.TransportDensity
import PersistencePays.DensityComparison
import PersistencePays.BridgeAffinity

open MeasureTheory InformationTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma klDiv_map_measurableEquiv (e : S ≃ᵐ T) (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le μ ν e.measurable)
  have hh := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rw [Measure.map_map e.symm.measurable e.measurable,
    Measure.map_map e.symm.measurable e.measurable] at hh
  have he : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  simpa only [he, Measure.map_id] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma transportJoint_comp (μ : Measure (E × E)) (u t : ℝ) :
    (transportJoint μ u).map (freeTransport (t-u)) = transportJoint μ t := by
  unfold transportJoint
  rw [Measure.map_map (measurable_freeTransport _) (measurable_freeTransport _)]
  congr 1
  funext z
  simp only [Function.comp_apply, freeTransport, drift]
  congr 1
  module

lemma map_product_density_transport (a g : E → ℝ≥0∞)
    (ha : Measurable a) (hg : Measurable g) (t : ℝ) :
    ((volume.withDensity a).prod (volume.withDensity g)).map (freeTransport t) =
      ((volume : Measure E).prod volume).withDensity
        (fun z => a (z.1 - t • z.2) * g z.2) := by
  rw [prod_withDensity ha hg]
  have h := map_density_equiv (freeTransportEquiv (E := E) t)
    ((volume : Measure E).prod volume) (fun z => a z.1 * g z.2)
    ((ha.comp measurable_fst).mul (hg.comp measurable_snd))
  have hv : Measure.map (freeTransportEquiv (E := E) t)
      ((volume : Measure E).prod volume) = (volume : Measure E).prod volume :=
    (drift_measurePreserving t).map_eq
  rw [hv] at h
  simpa [Function.comp_def, freeTransportEquiv, freeTransport, drift, sub_eq_add_neg] using h

lemma product_reference_eq_withDensity (μ : Measure (E × E))
    [IsProbabilityMeasure μ] (hμ : μ ≪ (volume : Measure E).prod volume)
    (g : E → ℝ≥0∞) (hg : Measurable g) (t : ℝ) :
    (transportPosition μ t).prod (volume.withDensity g) =
      ((volume : Measure E).prod volume).withDensity
        (fun z => positionDensity μ t z.1 * g z.2) := by
  rw [transportPosition_eq_withDensity μ hμ t,
    prod_withDensity (measurable_positionDensity μ t) hg]

lemma endpoint_reference_eq_withDensity (μ : Measure (E × E))
    [IsProbabilityMeasure μ] (hμ : μ ≪ (volume : Measure E).prod volume)
    (g : E → ℝ≥0∞) (hg : Measurable g) (u t : ℝ) :
    ((transportPosition μ u).prod (volume.withDensity g)).map (freeTransport (t-u)) =
      ((volume : Measure E).prod volume).withDensity
        (fun z => positionDensity μ u (z.1 - (t-u) • z.2) * g z.2) := by
  rw [transportPosition_eq_withDensity μ hμ u,
    map_product_density_transport _ _ (measurable_positionDensity μ u) hg]

lemma entropy_endpoint_reference (μ : Measure (E × E))
    [IsProbabilityMeasure μ] (hμ : μ ≪ (volume : Measure E).prod volume)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    [IsProbabilityMeasure (volume.withDensity g)] (u t : ℝ) :
    klDiv (transportJoint μ t)
      (((volume : Measure E).prod volume).withDensity
        (fun z => positionDensity μ u (z.1 - (t-u) • z.2) * g z.2)) =
      conditionalGaussianEntropy μ (volume.withDensity g) u := by
  rw [← endpoint_reference_eq_withDensity μ hμ g hg u t,
    ← transportJoint_comp μ u t]
  exact klDiv_map_measurableEquiv (freeTransportEquiv (t-u))
    (transportJoint μ u) ((transportPosition μ u).prod (volume.withDensity g))

end
end PersistencePays
#print axioms PersistencePays.entropy_endpoint_reference
