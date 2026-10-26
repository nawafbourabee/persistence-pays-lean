import PersistencePays.CorrectorTalagrand
import PersistencePays.EntropyDissipationAlgebra

/-! Actual entropy and corrector dissipation for a Gaussian/volume/Gaussian
step. The deterministic stage bound is explicit so the same theorem applies
to both velocity Verlet and the comparison map. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.volume_stage_entropy_change {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (e : (E×E) ≃ᵐ (E×E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (hμ : MemLp id 2 μ) (hμe : MemLp e 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    klDiv (μ.map e) (phaseGibbs U) ≠ ∞ ∧
    (klDiv (μ.map e) (phaseGibbs U)).toReal = (klDiv μ (phaseGibbs U)).toReal+
      (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂μ) := by
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hK ⊢
  exact volume_preserving_entropy_change _ (phaseEnergy U)
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phase_gibbs_integrable U a.gibbs_integrable) μ e he hK
    ((a.phaseEnergy_integrable hμe).sub (a.phaseEnergy_integrable hμ))

theorem A1.ou_entropy_dissipation {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1) :
    (klDiv (phaseOUKernel r σ ∘ₘ μ) (phaseGibbs U)).toReal ≤
      (klDiv μ (phaseGibbs U)).toReal-
        (1-r^2)*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := by
  have hKo : klDiv (phaseOUKernel r σ ∘ₘ μ) (phaseGibbs U) ≠ ∞ :=
    ne_top_of_le_ne_top hK (klDiv_step_le _ _ _ (phaseOUKernel_invariant U r σ hn))
  have hV := a.velocity_entropy_finite μ hK
  have hB := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV)
    (a.lemma_4_2 μ hμ hK r σ hr hσ hn).2.2.1
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at hB
  have hi := a.phase_entropy_eq_sum μ hK
  have ho := a.phase_entropy_eq_sum (phaseOUKernel r σ ∘ₘ μ) hKo
  rw [phaseOUKernel_fst] at ho
  nlinarith

theorem A1.sandwich_entropy_dissipation {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (e : (E×E) ≃ᵐ (E×E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (r σ : ℝ) (hμ : MemLp id 2 μ) (hμe : MemLp e 2 (phaseOUKernel r σ ∘ₘ μ))
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1) :
    (klDiv (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ) (phaseGibbs U)).toReal ≤
      (klDiv μ (phaseGibbs U)).toReal -
        (1-r^2)*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
          (conditionalGaussianEntropy ((phaseOUKernel r σ ∘ₘ μ).map e) (stdGaussian E) 0).toReal)+
        (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂phaseOUKernel r σ ∘ₘ μ) := by
  let ν := phaseOUKernel r σ ∘ₘ μ
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  have hKν : klDiv ν (phaseGibbs U) ≠ ∞ :=
    ne_top_of_le_ne_top hK (klDiv_step_le _ _ _ (phaseOUKernel_invariant U r σ hn))
  letI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have hνe : MemLp id 2 (ν.map e) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable e.measurable.aemeasurable).mpr hμe
  have hd := a.volume_stage_entropy_change ν e he hν hμe hKν
  have hi := a.ou_entropy_dissipation μ hμ hK r σ hr hσ hn
  have ho := a.ou_entropy_dissipation (ν.map e) hνe hd.1 r σ hr hσ hn
  rw [gaussianSandwichKernel_comp]
  change (klDiv (phaseOUKernel r σ ∘ₘ ν.map e) (phaseGibbs U)).toReal ≤ _
  nlinarith [hd.2]

end PersistencePays
#print axioms PersistencePays.A1.sandwich_entropy_dissipation
