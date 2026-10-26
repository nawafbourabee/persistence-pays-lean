import PersistencePays.CappedFlight
import PersistencePays.VerletCorrector

/-! Corrector dissipation over the two actual free-flight halves, including
exactly the exceptional reflection cost. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cappedMidpointLaw (μ:Measure (E×E)) (h vstar:ℝ) : Measure (E×E) :=
  (transportJoint μ (h/2)).map (speedFlipEquiv vstar)

instance cappedMidpointLaw_probability (μ:Measure (E×E)) [IsProbabilityMeasure μ] (h vstar:ℝ) :
    IsProbabilityMeasure (cappedMidpointLaw μ h vstar) := by
  unfold cappedMidpointLaw; infer_instance

def cappedEntropyIntegral (μ:Measure (E×E)) (h vstar:ℝ) : ℝ :=
  (∫ s in (0:ℝ)..h/2,(conditionalGaussianEntropy μ (stdGaussian E) s).toReal)+
  (∫ s in (0:ℝ)..h/2,(conditionalGaussianEntropy (cappedMidpointLaw μ h vstar) (stdGaussian E) s).toReal)

theorem cappedMidpointLaw_memLp (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ:MemLp id 2 μ) (h vstar:ℝ) : MemLp id 2 (cappedMidpointLaw μ h vstar) :=
  (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (speedFlipEquiv vstar).measurable.aemeasurable).mpr
      (speedFlip_memLp (transportProbability_memLp μ hμ (h/2)) vstar)

theorem A1.cappedMidpoint_entropy_finite {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (h vstar:ℝ) :
    klDiv (cappedMidpointLaw μ h vstar) (phaseGibbs U)≠∞ := by
  have hm := transportProbability_memLp μ hμ (h/2)
  have hk := a.volume_stage_entropy_finite μ (freeTransportEquiv (h/2))
    (drift_measurePreserving (h/2)) hμ (drift_memLp hμ (h/2)) hK
  exact a.volume_stage_entropy_finite (transportJoint μ (h/2)) (speedFlipEquiv vstar)
    (speedFlip_measurePreserving vstar) hm (speedFlip_memLp hm vstar) hk

theorem cappedFlightLaw_endpoint (μ:Measure (E×E)) {h vstar:ℝ} (hh:0<h) :
    cappedFlightLaw μ h vstar h=transportJoint (cappedMidpointLaw μ h vstar) (h/2) := by
  rw [cappedFlightLaw_second μ (by linarith : h/2<h),show h-h/2=h/2 by ring]
  rfl

theorem A1.capped_free_corrector_bound {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (hsm:GaussianSmoothedFreeTransportBound a)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) {h vstar:ℝ} (hh:0<h) :
    a.corrector (cappedFlightLaw μ h vstar h)-a.corrector μ ≤
      7*cappedEntropyIntegral μ h vstar-h*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
        boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U))+
      2*Real.sqrt (∫ z in {z:E×E|vstar<‖z.2‖},‖z.2‖^2 ∂μ)*
        QuadraticTransport.wassersteinTwo ⟨(transportJoint μ (h/2)).fst,inferInstance⟩ a.targetProbability := by
  let mid := transportJoint μ (h/2)
  let plus := cappedMidpointLaw μ h vstar
  have hmid := transportProbability_memLp μ hμ (h/2)
  have hKmid : klDiv mid (phaseGibbs U)≠∞ := a.volume_stage_entropy_finite μ
    (freeTransportEquiv (h/2)) (drift_measurePreserving (h/2)) hμ (drift_memLp hμ (h/2)) hK
  have hplus := cappedMidpointLaw_memLp μ hμ h vstar
  have hKplus := a.cappedMidpoint_entropy_finite μ hμ hK h vstar
  have h0 := a.free_transport_of_smoothed_bound hsm ⟨μ,inferInstance⟩ hμ hK (by linarith : 0<h/2)
  have h1 := a.free_transport_of_smoothed_bound hsm ⟨plus,inferInstance⟩ hplus hKplus (by linarith : 0<h/2)
  have hflip := transportCorrector_speedFlip_bound mid a.targetProbability hmid a.position_memLp_two
    (a.position_absolutelyContinuous mid hKmid) vstar
  have hE : conditionalGaussianEntropy plus (stdGaussian E) 0=
      conditionalGaussianEntropy μ (stdGaussian E) (h/2) := by
    rw [show plus=mid.map (speedFlipEquiv vstar) from rfl,speedFlip_conditional_entropy]
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition]
    rfl
  have hL : plus.fst=mid.fst := map_position_preserving_fst mid (speedFlipEquiv vstar) (speedFlip_fst vstar)
  have hbalance := (a.free_transport_entropy_balance μ hμ hK (h/2)).2.2
  have hmoment : (∫ z in {z:E×E|vstar<‖z.2‖},‖z.2‖^2 ∂mid)=
      ∫ z in {z:E×E|vstar<‖z.2‖},‖z.2‖^2 ∂μ := by
    have hm : MeasurableSet {z:E×E|vstar<‖z.2‖} := measurableSet_lt measurable_const measurable_snd.norm
    rw [←integral_indicator hm,←integral_indicator hm]
    change (∫z,({z:E×E|vstar<‖z.2‖}.indicator (fun z=>‖z.2‖^2)) z ∂μ.map (freeTransport (h/2)))=_
    rw [integral_map (measurable_freeTransport _).aemeasurable
      ((measurable_snd.norm.pow_const 2).indicator hm).aestronglyMeasurable]
    rfl
  rw [hmoment] at hflip
  have hjump := le_abs_self (a.corrector plus-a.corrector mid)
  change |a.corrector plus-a.corrector mid|≤_ at hflip
  simp only [cappedFlightLaw_endpoint μ hh]
  dsimp only [freeTransportRHS] at h0 h1
  change a.corrector mid-a.corrector μ≤
    7*(∫s in (0:ℝ)..h/2,(conditionalGaussianEntropy μ (stdGaussian E) s).toReal)-
      h/2*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
      h/2*(boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) at h0
  change a.corrector (transportJoint plus (h/2))-a.corrector plus≤
    7*(∫s in (0:ℝ)..h/2,(conditionalGaussianEntropy plus (stdGaussian E) s).toReal)-
      h/2*(conditionalGaussianEntropy plus (stdGaussian E) 0).toReal-
      h/2*(boltzmannEntropy plus.fst-boltzmannEntropy (positionGibbs U)) at h1
  rw [hE,hL] at h1
  change boltzmannEntropy mid.fst+_= _ at hbalance
  unfold cappedEntropyIntegral
  change a.corrector (transportJoint plus (h/2))-a.corrector μ≤_
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.capped_free_corrector_bound
