import PersistencePays.MaximalCoupling
import PersistencePays.NoiseCouplingLift
import PersistencePays.EpochCoupling

/-! Lemma 5.2: a measurable maximal coupling of the actual finite Gaussian noise blocks. -/
noncomputable section
namespace PersistencePays.NoiseCoupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
  [MeasurableSpace.CountablyGenerated S] [MeasurableEq S]
  [StandardBorelSpace B] [Nonempty B]

def endpointCoupling (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) : Kernel (S×S) (S×S) :=
  MaximalCoupling.maximalKernel
    ((FiniteNoise.noiseKernel μ F hF).comap Prod.fst measurable_fst)
    ((FiniteNoise.noiseKernel μ F hF).comap Prod.snd measurable_snd)

instance endpointCoupling_markov (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) : IsMarkovKernel (endpointCoupling μ F hF) := by
  unfold endpointCoupling
  infer_instance

theorem endpointCoupling_fst (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) :
    (endpointCoupling μ F hF).fst = (graphKernel μ F hF).fst.comap Prod.fst measurable_fst := by
  rw [endpointCoupling, MaximalCoupling.maximalKernel_fst, graphKernel_fst]

theorem endpointCoupling_snd (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) :
    (endpointCoupling μ F hF).snd = (graphKernel μ F hF).fst.comap Prod.snd measurable_snd := by
  rw [endpointCoupling, MaximalCoupling.maximalKernel_snd, graphKernel_fst]

def maximalNoise (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) : Kernel (S×S) (B×B) :=
  liftedNoise (graphKernel μ F hF) (endpointCoupling μ F hF)

instance maximalNoise_markov (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) : IsMarkovKernel (maximalNoise μ F hF) := by
  unfold maximalNoise
  infer_instance

theorem maximalNoise_fst (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) :
    (maximalNoise μ F hF).fst = Kernel.const (S×S) μ := by
  rw [maximalNoise, liftedNoise_fst _ _ (endpointCoupling_fst μ F hF), graphKernel_snd]
  ext a : 1
  rfl

theorem maximalNoise_snd (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) :
    (maximalNoise μ F hF).snd = Kernel.const (S×S) μ := by
  rw [maximalNoise, liftedNoise_snd _ _ (endpointCoupling_snd μ F hF), graphKernel_snd]
  ext a : 1
  rfl

theorem maximalNoise_disagreement (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) (a : S×S) :
    maximalNoise μ F hF a {b | F (a.1,b.1) ≠ F (a.2,b.2)} =
      probabilityTV (FiniteNoise.noiseKernel μ F hF a.1) (FiniteNoise.noiseKernel μ F hF a.2) := by
  rw [maximalNoise, liftedNoise_disagreement μ F hF _
    (endpointCoupling_fst μ F hF) (endpointCoupling_snd μ F hF), endpointCoupling,
    MaximalCoupling.maximalKernel_disagreement _ _
      ((measurableSet_eq_fun measurable_fst measurable_snd).compl)]
  rfl

end PersistencePays.NoiseCoupling

namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual jointly measurable Gaussian block coupling of Lemma 5.2. -/
def maximalBlockCoupling (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    Kernel ((E×E)×(E×E)) (NoiseBlock E n × NoiseBlock E n) :=
  NoiseCoupling.maximalNoise (gaussianBlock n) (unadjustedEpochEndpoint g h r σ n)
    (measurable_unadjustedEpochEndpoint g hg h r σ n)

instance maximalBlockCoupling_markov (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    IsMarkovKernel (maximalBlockCoupling g hg h r σ n) := by
  unfold maximalBlockCoupling
  infer_instance

/-- Both full noise blocks are precisely the prescribed independent Gaussian arrays. -/
theorem lemma_5_2_marginals (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    (maximalBlockCoupling g hg h r σ n).fst = Kernel.const ((E×E)×(E×E)) (gaussianBlock n) ∧
    (maximalBlockCoupling g hg h r σ n).snd = Kernel.const ((E×E)×(E×E)) (gaussianBlock n) :=
  ⟨NoiseCoupling.maximalNoise_fst _ _ _, NoiseCoupling.maximalNoise_snd _ _ _⟩

/-- The endpoint disagreement equals TV, for the actual unadjusted finite-step chain. -/
theorem lemma_5_2 (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) (z z' : E×E) :
    maximalBlockCoupling g hg h r σ n (z,z')
      {b | unadjustedEpochEndpoint g h r σ n (z,b.1) ≠
        unadjustedEpochEndpoint g h r σ n (z',b.2)} =
      probabilityTV (unadjustedEpochKernel g hg h r σ n z) (unadjustedEpochKernel g hg h r σ n z') :=
  NoiseCoupling.maximalNoise_disagreement _ _ _ (z,z')

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.lemma_5_2
#print axioms PersistencePays.OBABOPath.lemma_5_2_marginals
