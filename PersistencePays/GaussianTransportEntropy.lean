import PersistencePays.RegularizationEntropyConvergence
import PersistencePays.FreeTransportCorrectorContinuity
import PersistencePays.ConditionalEntropy

/-! The actual free-flight entropy balance, referenced to the standard Gaussian
on both coordinates, with all finiteness conditions discharged. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_freeTransport_entropy (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ)
    (hK : klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) (t : ℝ) :
    klDiv (transportJoint μ t) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞ ∧
    (klDiv (transportJoint μ t) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal =
      (klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E))).toReal +
        (∫ z, (‖(freeTransport t z).1‖^2/2-‖z.1‖^2/2) ∂μ) := by
  let e := freeTransportEquiv (E:=E) t
  have hKt := hK
  change klDiv μ ((stdGaussian E).prod (stdGaussian E)) ≠ ∞ at hKt
  rw [gaussianPair_eq_tilted] at hKt
  have hi1 : Integrable (fun z : E×E => ‖(e z).1‖^2/2) μ :=
    (drift_memLp hμ t).fst.integrable_norm_pow'.div_const 2
  have hi2 : Integrable (fun z : E×E => ‖(e z).2‖^2/2) μ :=
    (drift_memLp hμ t).snd.integrable_norm_pow'.div_const 2
  have hie : Integrable (fun z => phaseEnergy kineticPotential (e z)) μ := by
    have he : (fun z => phaseEnergy kineticPotential (e z)) =
        fun z => ‖(e z).1‖^2/2+‖(e z).2‖^2/2 := by
      funext z
      rw [phaseEnergy_eq_norm]
      rfl
    rw [he]
    exact hi1.add hi2
  have hc := volume_preserving_entropy_change _ (phaseEnergy kineticPotential)
    (phaseEnergy_measurable kineticPotential (by unfold kineticPotential; fun_prop))
    (phase_gibbs_integrable kineticPotential kinetic_gibbs_integrable) μ e
    (drift_measurePreserving t) hKt
      (hie.sub (phaseGaussianEnergy_integrable μ hμ))
  rw [← gaussianPair_eq_tilted] at hc
  refine ⟨hc.1, ?_⟩
  have hh := hc.2
  change (klDiv (transportJoint μ t) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal =
    (klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E))).toReal + _ at hh
  rw [hh]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    simp only [phaseEnergy_eq_norm,kineticPotential]
    change ‖(freeTransport t z).1‖^2/2+‖z.2‖^2/2-(‖z.1‖^2/2+‖z.2‖^2/2) =
      ‖(freeTransport t z).1‖^2/2-‖z.1‖^2/2
    ring)

theorem gaussian_conditional_boltzmann_identity
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) (t : ℝ) :
    conditionalGaussianEntropy μ (stdGaussian E) t ≠ ∞ ∧
    klDiv (transportPosition μ t) (stdGaussian E) ≠ ∞ ∧
    boltzmannEntropy (transportPosition μ t) +
      (conditionalGaussianEntropy μ (stdGaussian E) t).toReal =
      (klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E))).toReal -
        (∫ z, ‖z.1‖^2/2 ∂μ) - (Module.finrank ℝ E:ℝ)/2*Real.log (2*Real.pi) := by
  let ν := transportJoint μ t
  have hc := gaussian_freeTransport_entropy μ hμ hK t
  have he := klDiv_product_reference_decomposition ν (stdGaussian E) (stdGaussian E)
  have hX : klDiv ν.fst (stdGaussian E) ≠ ∞ := by
    apply ne_top_of_le_ne_top hc.1
    change klDiv ν.fst _ ≤ klDiv ν ((stdGaussian E).prod (stdGaussian E))
    rw [he]
    exact le_add_right le_rfl
  have hV : klDiv ν (ν.fst.prod (stdGaussian E)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hc.1
    change klDiv ν (ν.fst.prod _) ≤ klDiv ν ((stdGaussian E).prod (stdGaussian E))
    rw [he]
    exact le_add_left le_rfl
  have hν := transportProbability_memLp μ hμ t
  have hνX : MemLp id 2 ν.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hν.fst
  have hb := (gaussian_boltzmann_identity ν.fst hνX hX).2
  refine ⟨hV,hX,?_⟩
  have her := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hX hV] at her
  have hi0 : Integrable (fun z : E×E => ‖z.1‖^2/2) μ := hμ.fst.integrable_norm_pow'.div_const 2
  have hit : Integrable (fun z => ‖(freeTransport t z).1‖^2/2) μ :=
    (drift_memLp hμ t).fst.integrable_norm_pow'.div_const 2
  rw [integral_sub hit hi0] at hc
  have hint : (∫ x, ‖x‖^2 ∂ν.fst)/2 = ∫ z, ‖(freeTransport t z).1‖^2/2 ∂μ := by
    rw [← integral_div]
    change (∫ x, ‖x‖^2/2 ∂(μ.map (freeTransport t)).map Prod.fst) = _
    rw [Measure.map_map measurable_fst (measurable_freeTransport t),integral_map (by fun_prop) (by fun_prop)]
    rfl
  change boltzmannEntropy ν.fst + (klDiv ν (ν.fst.prod (stdGaussian E))).toReal = _
  rw [hb]
  have hcr := hc.2
  change (klDiv ν ((stdGaussian E).prod (stdGaussian E))).toReal = _ at hcr
  linarith

end PersistencePays
#print axioms PersistencePays.gaussian_conditional_boltzmann_identity
