import PersistencePays.AdjustedPairCoupling
import PersistencePays.LocalizedCoupling
import PersistencePays.UnadjustedEpochLaw

/-! Proposition 5.3 for the actual adjusted finite-array OBABO epoch kernel. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def localizedEpochBound (U : E → ℝ) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) (D : Set (E×E)) : ℝ≥0∞ :=
  ⨆ (z : E×E) (_ : z∈D) (z' : E×E) (_ : z'∈D),
    probabilityTV (unadjustedEpochKernel g hg h r σ n z) (unadjustedEpochKernel g hg h r σ n z') +
      epochRejectionProbability U g h r σ n z + epochRejectionProbability U g h r σ n z'

/-- Actual sampler version with any proved upper bound on the local defect. -/
theorem proposition_5_3_of_bound (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r^2+σ^2=1)
    (epochLength : ℕ) (ν : Measure (E×E)) [IsProbabilityMeasure ν]
    (hac : ν ≪ phaseGibbs U) (D : Set (E×E)) (hD : MeasurableSet D)
    (q : ℝ≥0∞)
    (hq : ∀ z∈D, ∀ z'∈D,
      probabilityTV (unadjustedEpochKernel g hg h r σ epochLength z)
        (unadjustedEpochKernel g hg h r σ epochLength z') +
      epochRejectionProbability U g h r σ epochLength z +
        epochRejectionProbability U g h r σ epochLength z' ≤ q)
    (N : ℕ) :
    probabilityTV (iterateKernel (epochKernel U hU g hg h r σ epochLength) N ∘ₘ ν) (phaseGibbs U) ≤
      q^N + (N:ℝ≥0∞)*phaseGibbs U Dᶜ +
        warmL2 ν (phaseGibbs U)*((N:ℝ≥0∞)*phaseGibbs U Dᶜ)^(1/2:ℝ) := by
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hi
  let : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  apply LocalizedCoupling.localized_coupling_bound
    (epochKernel U hU g hg h r σ epochLength) (adjustedPairKernel U hU g hg h r σ epochLength)
    (fun z => ?_) (fun z => ?_) ν (phaseGibbs U) hac
    (epochKernel_invariant U hU hi g hg h r σ hnorm epochLength) D hD q
    (adjustedPairKernel_sticky U hU g hg h r σ epochLength) (fun z hz hz' => ?_) N
  · exact congrArg (fun K : Kernel ((E×E)×(E×E)) (E×E) => K z)
      (adjustedPairKernel_fst U hU g hg h r σ epochLength)
  · exact congrArg (fun K : Kernel ((E×E)×(E×E)) (E×E) => K z)
      (adjustedPairKernel_snd U hU g hg h r σ epochLength)
  · exact (adjustedPairKernel_local U hU g hg h r σ epochLength z.1 z.2).trans (hq z.1 hz z.2 hz')

/-- Proposition 5.3 with the exact supremum specified in the manuscript.
It remains valid with infinite `warmL2`; finiteness makes it quantitative. -/
theorem proposition_5_3 (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r^2+σ^2=1)
    (epochLength : ℕ) (ν : Measure (E×E)) [IsProbabilityMeasure ν]
    (hac : ν ≪ phaseGibbs U) (D : Set (E×E)) (hD : MeasurableSet D) (N : ℕ) :
    probabilityTV (iterateKernel (epochKernel U hU g hg h r σ epochLength) N ∘ₘ ν) (phaseGibbs U) ≤
      localizedEpochBound U g hg h r σ epochLength D ^ N + (N:ℝ≥0∞)*phaseGibbs U Dᶜ +
        warmL2 ν (phaseGibbs U)*((N:ℝ≥0∞)*phaseGibbs U Dᶜ)^(1/2:ℝ) := by
  apply proposition_5_3_of_bound U hU hi g hg h r σ hnorm epochLength ν hac D hD _ _ N
  intro z hz z' hz'
  exact le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le z' (le_iSup_of_le hz' le_rfl)))

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_5_3
