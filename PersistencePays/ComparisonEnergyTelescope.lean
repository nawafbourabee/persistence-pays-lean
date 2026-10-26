import PersistencePays.GradientCorrectionExpectation
import PersistencePays.FiniteEntropyPropagation

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def expectedComparisonRemainder (U : E → ℝ) (h vstar : ℝ) (μ : Measure (E×E)) : ℝ :=
  ∫ z,comparisonDefect U (gradient U) h vstar z ∂μ

theorem A1.comparisonRemainder_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (h vstar : ℝ) :
    Integrable (comparisonDefect U (gradient U) h vstar) μ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hF : MeasurableSet {z : E×E | ‖flightVelocity (gradient U) h z‖ ≤ vstar} := by
    apply measurableSet_le _ measurable_const
    unfold flightVelocity
    fun_prop
  exact (a.verletRemainder_integrable μ hμ h).indicator hF

theorem A1.comparison_sandwich_energy_telescope {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h r σ vstar : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂phaseOUKernel r σ ∘ₘ μ) =
      expectedGradientCorrection U h (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ)-
        expectedGradientCorrection U h μ+expectedComparisonRemainder U h vstar (phaseOUKernel r σ ∘ₘ μ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := comparisonVerletEquiv (gradient U) hg h vstar
  let ν := phaseOUKernel r σ ∘ₘ μ
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  letI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have hi0 : Integrable (fun z : E×E => gradientCorrection (gradient U) h z.1) ν :=
    a.gradientCorrection_integrable hν.fst h
  have hi1 : Integrable (fun z : E×E => gradientCorrection (gradient U) h (e z).1) ν :=
    a.gradientCorrection_integrable (a.comparisonVerlet_memLp hν h vstar).fst h
  have hit : Integrable (fun z => comparisonDefect U (gradient U) h vstar z) ν :=
    a.comparisonRemainder_integrable ν hν h vstar
  have hisub : Integrable (fun z => gradientCorrection (gradient U) h (e z).1-
      gradientCorrection (gradient U) h z.1) ν := hi1.sub hi0
  have hG : Measurable (fun z : E×E => gradientCorrection (gradient U) h z.1) := by
    simp_rw [gradientCorrection_eq_norm]
    exact (((contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable.comp measurable_fst).norm.pow_const 2).const_mul _
  have heq : (fun z => phaseEnergy U (e z)-phaseEnergy U z) =
      fun z => gradientCorrection (gradient U) h (e z).1-gradientCorrection (gradient U) h z.1+
        comparisonDefect U (gradient U) h vstar z := by
    funext z
    exact comparisonVerlet_energy_identity U (gradient U) h vstar z
  dsimp only
  change (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂ν) = _
  rw [heq,integral_add hisub hit,integral_sub hi1 hi0]
  rw [gaussianSandwichKernel_comp,a.expectedGradientCorrection_ou]
  have hpost : expectedGradientCorrection U h (ν.map e) =
      ∫ z,gradientCorrection (gradient U) h (e z).1 ∂ν :=
    integral_map e.measurable.aemeasurable hG.aestronglyMeasurable
  rw [hpost,← a.expectedGradientCorrection_ou μ h r σ]
  rfl

end PersistencePays
#print axioms PersistencePays.A1.comparison_sandwich_energy_telescope
