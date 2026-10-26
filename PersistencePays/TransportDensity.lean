import PersistencePays.TransportEntropy
import PersistencePays.GaussianBridgeLaw

/-!
# Actual densities under free transport

All densities are constructed from Radon--Nikodym derivatives. Transported
joint and marginal laws are identified with these densities, rather than
postulated to have them.
-/

namespace PersistencePays
noncomputable section
open MeasureTheory Set
open scoped ENNReal

theorem fst_withDensity_prod {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [SFinite μ] [SFinite ν]
    (r : S × T → ℝ≥0∞) (hr : Measurable r) :
    ((μ.prod ν).withDensity r).fst =
      μ.withDensity (fun x => ∫⁻ y, r (x, y) ∂ν) := by
  ext A hA
  rw [Measure.fst_apply hA, withDensity_apply r (measurable_fst hA),
    withDensity_apply _ hA]
  have hs : Prod.fst ⁻¹' A = A ×ˢ (univ : Set T) := by ext z; simp
  rw [hs]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  exact lintegral_prod _ hr.aemeasurable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def freeTransportEquiv (t : ℝ) : (E × E) ≃ᵐ (E × E) where
  toFun := freeTransport t
  invFun := freeTransport (-t)
  left_inv := drift_inverse t
  right_inv := by
    intro z
    simpa only [freeTransport, neg_neg] using drift_inverse (-t) z
  measurable_toFun := measurable_freeTransport t
  measurable_invFun := measurable_freeTransport (-t)

def jointDensity (μ : Measure (E × E)) : E × E → ℝ≥0∞ :=
  μ.rnDeriv ((volume : Measure E).prod volume)

def transportedDensity (μ : Measure (E × E)) (t : ℝ) (z : E × E) : ℝ≥0∞ :=
  jointDensity μ (freeTransport (-t) z)

def positionDensity (μ : Measure (E × E)) (t : ℝ) (x : E) : ℝ≥0∞ :=
  ∫⁻ v : E, transportedDensity μ t (x, v)

theorem measurable_jointDensity (μ : Measure (E × E)) : Measurable (jointDensity μ) :=
  Measure.measurable_rnDeriv _ _

theorem measurable_transportedDensity (μ : Measure (E × E)) (t : ℝ) :
    Measurable (transportedDensity μ t) :=
  (measurable_jointDensity μ).comp (measurable_freeTransport (-t))

theorem measurable_positionDensity (μ : Measure (E × E)) (t : ℝ) :
    Measurable (positionDensity μ t) :=
  (measurable_transportedDensity μ t).lintegral_prod_right'

theorem jointDensity_representation (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) :
    ((volume : Measure E).prod volume).withDensity (jointDensity μ) = μ := by
  letI : SigmaFinite ((volume : Measure E).prod (volume : Measure E)) := inferInstance
  exact Measure.withDensity_rnDeriv_eq μ ((volume : Measure E).prod (volume : Measure E)) hμ

theorem lintegral_jointDensity (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) :
    (∫⁻ z, jointDensity μ z ∂(volume : Measure E).prod volume) = 1 := by
  letI : SigmaFinite ((volume : Measure E).prod (volume : Measure E)) := inferInstance
  simpa only [jointDensity, measure_univ] using Measure.lintegral_rnDeriv hμ

theorem transportJoint_eq_withDensity (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) (t : ℝ) :
    transportJoint μ t = ((volume : Measure E).prod volume).withDensity (transportedDensity μ t) := by
  have hrep := jointDensity_representation μ hμ
  have hm := map_density_equiv (freeTransportEquiv (E := E) t)
    ((volume : Measure E).prod volume) (jointDensity μ) (measurable_jointDensity μ)
  have hvol : Measure.map (freeTransportEquiv (E := E) t)
      ((volume : Measure E).prod volume) = (volume : Measure E).prod volume :=
    (drift_measurePreserving t).map_eq
  rw [hvol] at hm
  calc
    transportJoint μ t = Measure.map (freeTransportEquiv t)
        (((volume : Measure E).prod volume).withDensity (jointDensity μ)) := by
      rw [hrep]
      rfl
    _ = _ := hm

theorem transportPosition_eq_withDensity (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) (t : ℝ) :
    transportPosition μ t = (volume : Measure E).withDensity (positionDensity μ t) := by
  unfold transportPosition
  rw [transportJoint_eq_withDensity μ hμ t,
    fst_withDensity_prod volume volume (transportedDensity μ t) (measurable_transportedDensity μ t)]
  rfl

theorem lintegral_transportedDensity (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) (t : ℝ) :
    (∫⁻ z, transportedDensity μ t z ∂(volume : Measure E).prod volume) = 1 := by
  have hh := congrArg (fun ν : Measure (E × E) => ν univ) (transportJoint_eq_withDensity μ hμ t)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hh
  exact hh.symm

theorem lintegral_positionDensity (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) (t : ℝ) :
    (∫⁻ x, positionDensity μ t x) = 1 := by
  have hh := congrArg (fun ν : Measure E => ν univ) (transportPosition_eq_withDensity μ hμ t)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hh
  exact hh.symm

theorem transportedDensity_apply (μ : Measure (E × E)) (t : ℝ) (x v : E) :
    transportedDensity μ t (x, v) = jointDensity μ (x - t • v, v) := by
  simp [transportedDensity, freeTransport, drift, sub_eq_add_neg]

end
end PersistencePays

#print axioms PersistencePays.transportJoint_eq_withDensity
#print axioms PersistencePays.transportPosition_eq_withDensity
#print axioms PersistencePays.lintegral_positionDensity
