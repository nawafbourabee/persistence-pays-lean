import PersistencePays.PositionBoltzmannEntropy
import PersistencePays.TimeScaledEntropy

/-! Free transport preserves position Boltzmann entropy plus conditional velocity entropy. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.position_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) : klDiv μ.fst (positionGibbs U) ≠ ∞ := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have he := klDiv_product_reference_decomposition μ (positionGibbs U) (stdGaussian E)
  change klDiv μ (phaseGibbs U) = _ at he
  apply ne_top_of_le_ne_top hK
  rw [he]
  exact le_add_right le_rfl

theorem A1.position_boltzmann_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    Integrable (fun x => Real.log ((μ.fst.rnDeriv volume x).toReal)) μ.fst ∧
    boltzmannEntropy μ.fst = (klDiv μ.fst (positionGibbs U)).toReal -
      (∫ z, U z.1 ∂μ) - Real.log (∫ x, Real.exp (-U x)) := by
  have hm : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hh := gibbs_boltzmann_identity U a.gibbs_integrable μ.fst
    (a.potential_integrable hm) (a.position_entropy_finite μ hK)
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  congr 2
  exact integral_map measurable_fst.aemeasurable a.twice_contDiff.continuous.measurable.aestronglyMeasurable

/-- Exact entropy balance (4.1), expressed using genuine Lebesgue-density
entropy and the actual transported probability law. -/
theorem A1.free_transport_entropy_balance {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) (t : ℝ) :
    conditionalGaussianEntropy μ (stdGaussian E) t ≠ ∞ ∧
    Integrable (fun x => Real.log (((transportPosition μ t).rnDeriv volume x).toReal))
      (transportPosition μ t) ∧
    boltzmannEntropy (transportPosition μ t) +
      (conditionalGaussianEntropy μ (stdGaussian E) t).toReal =
      boltzmannEntropy μ.fst + (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := by
  let e := freeTransportEquiv (E := E) t
  let ν := μ.map e
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have hν : MemLp id 2 ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable e.measurable.aemeasurable).mpr
      (drift_memLp hμ t)
  have hKt := hK
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hKt
  have hc := volume_preserving_entropy_change _ (phaseEnergy U)
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phase_gibbs_integrable U a.gibbs_integrable) μ e (drift_measurePreserving t) hKt
      ((a.phaseEnergy_integrable (drift_memLp hμ t)).sub (a.phaseEnergy_integrable hμ))
  rw [← phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hc
  have hi := a.phase_entropy_eq_sum μ hK
  have ho := a.phase_entropy_eq_sum ν hc.1
  have hLi := a.position_boltzmann_identity μ hμ hK
  have hLo := a.position_boltzmann_identity ν hν hc.1
  have hV := a.velocity_entropy_finite ν hc.1
  have hVeq : conditionalGaussianEntropy ν (stdGaussian E) 0 =
      conditionalGaussianEntropy μ (stdGaussian E) t := by
    simp only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero]
    rfl
  have hposeq : ν.fst = transportPosition μ t := rfl
  rw [hVeq] at hV ho
  rw [hposeq] at hLo
  refine ⟨hV, hLo.1, ?_⟩
  have henergy : (fun z => phaseEnergy U (e z)-phaseEnergy U z) =
      fun z => U (e z).1-U z.1 := by
    funext z
    rw [phaseEnergy_eq_norm, phaseEnergy_eq_norm]
    change U (z.1+t•z.2)+‖z.2‖^2/2-(U z.1+‖z.2‖^2/2) =
      U (z.1+t•z.2)-U z.1
    ring
  have hUe : Integrable (fun z => U (e z).1) μ := a.potential_integrable (drift_memLp hμ t).fst
  have hU0 : Integrable (fun z : E × E => U z.1) μ := a.potential_integrable hμ.fst
  rw [henergy, integral_sub hUe hU0] at hc
  have heint : (∫ z, U z.1 ∂ν) = ∫ z, U (e z).1 ∂μ := by
    exact integral_map e.measurable.aemeasurable
      (a.twice_contDiff.continuous.measurable.comp measurable_fst).aestronglyMeasurable
  rw [heint] at hLo
  change boltzmannEntropy ν.fst + _ = _
  rw [hposeq]
  rw [hposeq] at ho
  linarith [hLi.2, hLo.2, hc.2]

end PersistencePays
#print axioms PersistencePays.A1.free_transport_entropy_balance
