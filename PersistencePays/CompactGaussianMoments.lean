import PersistencePays.GaussianSmoothingFinite
import PersistencePays.GaussianMeanIdentification

/-! All polynomial moments of compact-latent Gaussian-smoothed free-flight laws. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem compactLatent_memLp_all (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) (p:ℝ≥0∞) : MemLp id p (μ.map g) :=
  (memLp_map_measure_iff measurable_id.aestronglyMeasurable hg.measurable.aemeasurable).mpr
    (hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))

theorem compactGaussianSmoothing_memLp (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) (ε:ℝ) (p:ℝ≥0∞) (hp:p≠∞) :
    MemLp id p (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  exact fullGaussianOUKernel_memLp_all _ hp (compactLatent_memLp_all μ g hg p) 1 ε

theorem compactGaussianFlight_memLp (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) (ε s:ℝ) (p:ℝ≥0∞) (hp:p≠∞) :
    MemLp id p (gaussianFlightLaw (μ.map g) ε s) := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  rw [gaussianFlightLaw_transport]
  exact transportProbability_memLp _ (compactGaussianSmoothing_memLp μ g hg ε p hp) s

theorem A1.compactGaussianFlight_entropy_finite {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure Z) [IsProbabilityMeasure μ] (g:Z→E×E) (hg:Continuous g)
    (ε s:ℝ) (hε:ε≠0) :
    klDiv (gaussianFlightLaw (μ.map g) ε s) (phaseGibbs U)≠∞ ∧
    klDiv (gaussianFlightLaw (μ.map g) ε s) ((stdGaussian E).prod (stdGaussian E))≠∞ := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  have hK:=a.gaussianFlightLaw_entropy_finite _ (compactLatent_memLp μ g hg) ε s hε
  refine ⟨hK,?_⟩
  exact a.phaseGaussian_entropy_finite _ (compactGaussianFlight_memLp μ g hg ε s 2 (by norm_num)) hK

end PersistencePays
#print axioms PersistencePays.compactGaussianFlight_memLp
#print axioms PersistencePays.A1.compactGaussianFlight_entropy_finite
