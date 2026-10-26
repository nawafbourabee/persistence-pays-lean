import PersistencePays.ConvexDifferentiability
import PersistencePays.QuadraticTransport
import Mathlib.MeasureTheory.Measure.Support

/-! An absolutely continuous source turns a cyclically monotone coupling
into an actual gradient transport map. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology RealInnerProductSpace
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_gradient (f : E → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

/-- Any measure carried by a graph is its first marginal transported along that graph. -/
theorem measure_eq_graph_map (π : Measure (E × E)) (T : E → E) (hT : Measurable T)
    (hgraph : ∀ᵐ z ∂π, z.2 = T z.1) :
    π = π.fst.map (fun x => (x,T x)) := by
  have hp : Measurable (fun x : E => (x,T x)) := measurable_id.prodMk hT
  rw [Measure.fst, Measure.map_map hp measurable_fst]
  have heq : (fun z : E × E => (z.1,T z.1)) =ᵐ[π] id := by
    filter_upwards [hgraph] with z hz
    exact Prod.ext rfl hz.symm
  change π = π.map (fun z : E × E => (z.1,T z.1))
  rw [Measure.map_congr heq, Measure.map_id]

/-- The gradient graph is a measure identity, not merely a pointwise formal relation. -/
theorem cyclic_measure_eq_gradient_map (π : Measure (E × E)) (ρ : Measure E)
    [IsAddHaarMeasure ρ] {Γ : Set (E × E)} (hΓ : CyclicallyMonotone Γ)
    (hcarry : ∀ᵐ z ∂π, z ∈ Γ) (hac : π.fst ≪ ρ)
    {a : E × E} (ha : a ∈ Γ) :
    π = π.fst.map (fun x => (x,gradient (rockafellarPotential Γ a) x)) := by
  apply measure_eq_graph_map π _ (measurable_gradient _)
  have hh := hac.ae_le (rockafellar_ae_graph (μ:=ρ) hΓ ha)
  have hh' := ae_of_ae_map measurable_fst.aemeasurable hh
  filter_upwards [hcarry, hh'] with z hz hg
  exact hg z.2 hz

/-- A cyclically monotone coupling with absolutely continuous first marginal
is induced by a measurable gradient of the explicitly constructed convex potential. -/
theorem cyclic_plan_gradient (μ ν : ProbabilityMeasure E)
    (π : ProbabilityMeasure (E × E)) (hπ : π ∈ plans μ ν)
    (ρ : Measure E) [IsAddHaarMeasure ρ] (hac : (μ : Measure E) ≪ ρ)
    {Γ : Set (E × E)} (hΓ : CyclicallyMonotone Γ)
    (hcarry : ∀ᵐ z ∂(π : Measure (E × E)), z ∈ Γ) :
    ∃ a ∈ Γ, let T := gradient (rockafellarPotential Γ a)
      Measurable T ∧ (μ : Measure E).map T = (ν : Measure E) ∧
      (π : Measure (E × E)) = (μ : Measure E).map (fun x => (x,T x)) := by
  obtain ⟨a,ha⟩ := hcarry.exists
  refine ⟨a,ha,measurable_gradient _,?_,?_⟩
  all_goals
    have hf : (π : Measure (E × E)).fst = (μ : Measure E) :=
      congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1
    have hs : (π : Measure (E × E)).snd = (ν : Measure E) :=
      congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.2
    have hg := cyclic_measure_eq_gradient_map (π : Measure (E × E)) ρ hΓ hcarry
      (by rw [hf]; exact hac) ha
    rw [hf] at hg
  · have hp : Measurable (fun x : E => (x,gradient (rockafellarPotential Γ a) x)) :=
      measurable_id.prodMk (measurable_gradient _)
    rw [← hs, Measure.snd, hg, Measure.map_map measurable_snd hp]
    rfl
  · exact hg

/-- Two couplings with the same first marginal and a common cyclically
monotone carrier must agree when that marginal is absolutely continuous. -/
theorem cyclic_measures_eq (π₁ π₂ : Measure (E × E)) (ρ : Measure E)
    [IsAddHaarMeasure ρ] (hfst : π₁.fst = π₂.fst) (hac : π₁.fst ≪ ρ)
    {Γ : Set (E × E)} (hΓ : CyclicallyMonotone Γ)
    (h₁ : ∀ᵐ z ∂π₁, z ∈ Γ) (h₂ : ∀ᵐ z ∂π₂, z ∈ Γ)
    {a : E × E} (ha : a ∈ Γ) : π₁ = π₂ := by
  have hg₁ := cyclic_measure_eq_gradient_map π₁ ρ hΓ h₁ hac ha
  have hg₂ := cyclic_measure_eq_gradient_map π₂ ρ hΓ h₂ (by rw [← hfst]; exact hac) ha
  rw [hg₁, hg₂, hfst]

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.cyclic_plan_gradient
