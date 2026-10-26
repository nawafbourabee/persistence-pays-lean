import PersistencePays.CappedCorrectorError
import PersistencePays.ComparisonRemainder

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.comparisonCorrectorError_eq_remainder {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (h D vstar:ℝ) :
    a.comparisonCorrectorError μ h D vstar=a.comparisonRemainder h vstar D μ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ek := kickEquiv (gradient U) hg (h/2)
  let q := μ.map ek
  have hsq : (∫z,‖z.2‖^2∂q)=∫z,‖flightVelocity (gradient U) h z‖^2∂μ :=
    integral_map ek.measurable.aemeasurable (by fun_prop)
  have hmass : q (fastVelocitySet vstar)=μ {z|vstar<‖flightVelocity (gradient U) h z‖} := by
    rw [show q=μ.map ek from rfl,Measure.map_apply ek.measurable (fastVelocitySet_measurable vstar)]
    rfl
  have hfast := kick_fast_setIntegral (gradient U) hg μ h vstar (fun z=>‖z.2‖^2) (by fun_prop)
  have henergy := kick_fast_setIntegral (gradient U) hg μ h vstar (fun z=>2*U z.1+‖z.2‖^2)
    (by have hU:=a.twice_contDiff.continuous; fun_prop)
  have hmid : (transportJoint q (h/2)).fst=μ.map (flightMidpoint (gradient U) h) := by
    unfold transportJoint Measure.fst
    rw [show q=μ.map ek from rfl,Measure.map_map (measurable_freeTransport (h/2)) ek.measurable,
      Measure.map_map measurable_fst ((measurable_freeTransport (h/2)).comp ek.measurable)]
    rfl
  have hmidP : (⟨(transportJoint q (h/2)).fst,inferInstance⟩:ProbabilityMeasure E)=
      midpointProbability (gradient U) hg h μ := by
    apply Subtype.ext
    exact hmid
  unfold A1.comparisonCorrectorError A1.comparisonRemainder cappedMidEntropyError
  change (13/4:ℝ)*L*h^2*(∫z,‖z.2‖^2∂q)+(13/2:ℝ)*(∫z in fastVelocitySet vstar,‖z.2‖^2∂q)+
    (2/h)*Real.sqrt (∫z in fastVelocitySet vstar,‖z.2‖^2∂q)*
      QuadraticTransport.wassersteinTwo ⟨(transportJoint q (h/2)).fst,inferInstance⟩ a.targetProbability+
    7*(3*(q (fastVelocitySet vstar)).toReal*Real.log (1/(q (fastVelocitySet vstar)).toReal)+
      2*(q (fastVelocitySet vstar)).toReal+(q (fastVelocitySet vstar)).toReal*max (Real.log D) 0+
      (q (fastVelocitySet vstar)).toReal*(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)+
      (∫z in fastVelocitySet vstar,2*U z.1+‖z.2‖^2∂q))=_
  rw [hsq,hmidP,hmass]
  change (∫z in fastVelocitySet vstar,‖z.2‖^2∂q)=_ at hfast
  change (∫z in fastVelocitySet vstar,2*U z.1+‖z.2‖^2∂q)=_ at henergy
  rw [hfast,henergy]
  dsimp only [A1.targetProbability,A1.gibbsProbability,Measure.real,kick,flightVelocity]
  ring

end PersistencePays
#print axioms PersistencePays.A1.comparisonCorrectorError_eq_remainder
