import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! Compactness of the actual set of probability couplings with fixed
marginals, as a foundation for quadratic optimal transport. -/
open MeasureTheory Set
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  [TopologicalSpace E] [TopologicalSpace F] [BorelSpace E] [BorelSpace F]
  [PolishSpace E] [PolishSpace F]

def plans (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure F) : Set (ProbabilityMeasure (E × F)) :=
  {π | π.map measurable_fst.aemeasurable = μ ∧ π.map measurable_snd.aemeasurable = ν}

theorem plans_closed (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure F) :
    IsClosed (plans μ ν) := by
  exact (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)

theorem plans_nonempty (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure F) :
    (plans μ ν).Nonempty := by
  let π : ProbabilityMeasure (E × F) := ⟨(μ : Measure E).prod ν, inferInstance⟩
  refine ⟨π, ?_, ?_⟩
  · apply Subtype.ext
    change Measure.map Prod.fst ((μ : Measure E).prod (ν : Measure F)) = (μ : Measure E)
    simp
  · apply Subtype.ext
    change Measure.map Prod.snd ((μ : Measure E).prod (ν : Measure F)) = (ν : Measure F)
    simp

theorem plans_compact (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure F) :
    IsCompact (plans μ ν) := by
  have ht : IsTightMeasureSet {((π : ProbabilityMeasure (E × F)) : Measure (E × F)) | π ∈ plans μ ν} := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := (μ : Measure E))).subset
      rintro _ ⟨ρ, ⟨π, hπ, rfl⟩, rfl⟩
      have hh := congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1
      exact mem_singleton_iff.2 hh
    · apply (isTightMeasureSet_singleton (μ := (ν : Measure F))).subset
      rintro _ ⟨ρ, ⟨π, hπ, rfl⟩, rfl⟩
      have hh := congrArg (fun p : ProbabilityMeasure F => (p : Measure F)) hπ.2
      exact mem_singleton_iff.2 hh
  have hh := isCompact_closure_of_isTightMeasureSet ht
  rwa [(plans_closed μ ν).closure_eq] at hh

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.plans_compact
