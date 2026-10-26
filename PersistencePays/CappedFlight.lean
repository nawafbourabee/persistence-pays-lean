import PersistencePays.SpeedFlipCorrector
import PersistencePays.FreeTransportLimit

/-! The two literal free-flight halves and midpoint speed reflection. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cappedFlightEquiv (h vstar s : ℝ) : (E×E) ≃ᵐ (E×E) :=
  if s ≤ h/2 then freeTransportEquiv s else
    (freeTransportEquiv (h/2)).trans ((speedFlipEquiv vstar).trans (freeTransportEquiv (s-h/2)))

def cappedFlightLaw (μ : Measure (E×E)) (h vstar s : ℝ) : Measure (E×E) :=
  μ.map (cappedFlightEquiv h vstar s)

instance cappedFlightLaw_probability (μ : Measure (E×E)) [IsProbabilityMeasure μ] (h vstar s : ℝ) :
    IsProbabilityMeasure (cappedFlightLaw μ h vstar s) :=
  Measure.isProbabilityMeasure_map (cappedFlightEquiv h vstar s).measurable.aemeasurable

theorem cappedFlight_measurePreserving (h vstar s : ℝ) :
    MeasurePreserving (cappedFlightEquiv (E:=E) h vstar s) ((volume:Measure E).prod volume)
      ((volume:Measure E).prod volume) := by
  unfold cappedFlightEquiv
  split_ifs
  · exact drift_measurePreserving s
  · exact (drift_measurePreserving (s-h/2)).comp
      ((speedFlip_measurePreserving vstar).comp (drift_measurePreserving (h/2)))

theorem cappedFlight_slow {h vstar s : ℝ} {z : E×E} (hz : ‖z.2‖ ≤ vstar) :
    cappedFlightEquiv h vstar s z = freeTransport s z := by
  unfold cappedFlightEquiv
  split_ifs with hs
  · rfl
  · change freeTransport (s-h/2) (speedFlip vstar (freeTransport (h/2) z)) = _
    simp only [freeTransport,drift,speedFlip,not_lt.mpr hz,ite_false]
    ext
    · module
    · rfl

theorem cappedFlight_snd_norm (h vstar s : ℝ) (z : E×E) :
    ‖(cappedFlightEquiv h vstar s z).2‖=‖z.2‖ := by
  unfold cappedFlightEquiv
  split_ifs
  · rfl
  · change ‖(speedFlip vstar (freeTransport (h/2) z)).2‖=‖z.2‖
    rw [speedFlip_snd_norm]; rfl

theorem cappedFlight_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} {Z : Ω → E×E} (hZ : MemLp Z p μ) (h vstar s : ℝ) :
    MemLp (fun ω=>cappedFlightEquiv h vstar s (Z ω)) p μ := by
  unfold cappedFlightEquiv
  split_ifs
  · exact drift_memLp hZ s
  · have hmid := drift_memLp hZ (h/2)
    have hf : MemLp (fun ω=>speedFlip vstar (freeTransport (h/2) (Z ω))) p μ :=
      hmid.congr_norm ((speedFlipEquiv vstar).measurable.comp_aemeasurable
        hmid.aemeasurable).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω=>(speedFlip_norm vstar _).symm))
    exact drift_memLp hf (s-h/2)

theorem cappedFlightLaw_memLp (μ : Measure (E×E)) [IsFiniteMeasure μ] {p : ℝ≥0∞} (hμ : MemLp id p μ)
    (h vstar s : ℝ) : MemLp id p (cappedFlightLaw μ h vstar s) :=
  (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (cappedFlightEquiv h vstar s).measurable.aemeasurable).mpr (cappedFlight_memLp hμ h vstar s)

theorem A1.cappedFlight_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) (h vstar s : ℝ) :
    klDiv (cappedFlightLaw μ h vstar s) (phaseGibbs U) ≠ ∞ :=
  a.volume_stage_entropy_finite μ (cappedFlightEquiv h vstar s)
    (cappedFlight_measurePreserving h vstar s) hμ (cappedFlight_memLp hμ h vstar s) hK

theorem cappedFlightLaw_first (μ : Measure (E×E)) {h vstar s : ℝ} (hs : s ≤ h/2) :
    cappedFlightLaw μ h vstar s = transportJoint μ s := by
  simp only [cappedFlightLaw,cappedFlightEquiv,hs,ite_true,transportJoint]
  rfl

theorem cappedFlightLaw_second (μ : Measure (E×E)) {h vstar s : ℝ} (hs : h/2 < s) :
    cappedFlightLaw μ h vstar s =
      transportJoint ((transportJoint μ (h/2)).map (speedFlipEquiv vstar)) (s-h/2) := by
  unfold cappedFlightLaw cappedFlightEquiv
  rw [if_neg (not_le.mpr hs)]
  simp only [transportJoint,Measure.map_map,(measurable_freeTransport (s-h/2)),
    (measurable_freeTransport (h/2)),(speedFlipEquiv vstar).measurable]
  rw [Measure.map_map (measurable_freeTransport _)
    ((speedFlipEquiv vstar).measurable.comp (measurable_freeTransport _))]
  rfl

end PersistencePays
#print axioms PersistencePays.A1.cappedFlight_entropy_finite
