import PersistencePays.TransportPlanCompactness
import Mathlib.Topology.Sequences

/-! Tightness of couplings with convergent marginals, retaining the actual measures. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory Set Filter
open scoped Topology
variable {S T : Type*} [MetricSpace S] [MetricSpace T]
  [CompleteSpace S] [CompleteSpace T] [SecondCountableTopology S] [SecondCountableTopology T]
  [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]

theorem convergent_probability_family_tight (μn : ℕ → ProbabilityMeasure S)
    (μ : ProbabilityMeasure S) (hw : Tendsto μn atTop (𝓝 μ)) :
    IsTightMeasureSet {((ρ : ProbabilityMeasure S) : Measure S) | ρ ∈ insert μ (range μn)} := by
  apply isTightMeasureSet_of_isCompact_closure
  have hc := hw.isCompact_insert_range
  rwa [hc.isClosed.closure_eq]

theorem varying_couplings_compact_closure
    (μn : ℕ → ProbabilityMeasure S) (νn : ℕ → ProbabilityMeasure T)
    (μ : ProbabilityMeasure S) (ν : ProbabilityMeasure T)
    (πn : ℕ → ProbabilityMeasure (S × T))
    (hfst : ∀ n, (πn n).map measurable_fst.aemeasurable = μn n)
    (hsnd : ∀ n, (πn n).map measurable_snd.aemeasurable = νn n)
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) :
    IsCompact (closure (range πn)) := by
  have ht : IsTightMeasureSet {((ρ : ProbabilityMeasure (S × T)) : Measure (S × T)) |
      ρ ∈ range πn} := by
    apply IsTightMeasureSet.prodMk
    · apply (convergent_probability_family_tight μn μ hμ).subset
      rintro _ ⟨ρ,⟨π,⟨n,rfl⟩,rfl⟩,rfl⟩
      refine ⟨μn n,Or.inr ⟨n,rfl⟩,?_⟩
      exact (congrArg (fun q : ProbabilityMeasure S => (q : Measure S)) (hfst n)).symm
    · apply (convergent_probability_family_tight νn ν hν).subset
      rintro _ ⟨ρ,⟨π,⟨n,rfl⟩,rfl⟩,rfl⟩
      refine ⟨νn n,Or.inr ⟨n,rfl⟩,?_⟩
      exact (congrArg (fun q : ProbabilityMeasure T => (q : Measure T)) (hsnd n)).symm
  exact isCompact_closure_of_isTightMeasureSet ht

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.varying_couplings_compact_closure
