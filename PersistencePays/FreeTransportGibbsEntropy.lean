import PersistencePays.FreeTransportEntropyContinuity

/-! Full Gibbs-relative entropy remains finite under the literal free flight. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.freeTransport_gibbs_entropy_finite {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (s:ℝ) :
    klDiv (transportJoint μ s) (phaseGibbs U)≠∞ := by
  have hi0 := a.phaseEnergy_integrable hμ
  have hi1 := a.phaseEnergy_integrable (drift_memLp hμ s)
  simp only [id_eq] at hi0
  have hk := hK
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hk
  have hc := volume_preserving_entropy_change (volume.prod volume : Measure (E×E))
    (phaseEnergy U) (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phase_gibbs_integrable U a.gibbs_integrable) μ (freeTransportEquiv s)
    (drift_measurePreserving s) hk (hi1.sub hi0)
  have hfin := hc.1
  rw [show μ.map (freeTransportEquiv s)=transportJoint μ s from rfl,
    ←phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hfin
  exact hfin

end PersistencePays
#print axioms PersistencePays.A1.freeTransport_gibbs_entropy_finite
