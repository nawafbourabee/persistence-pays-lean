import PersistencePays.CyclicCost
import PersistencePays.CyclicGraph
import PersistencePays.OptimalPlanMixture

/-! Brenier's gradient representation and uniqueness of quadratic optimal plans,
proved from compactness, finite permutation competitors, Rockafellar's potential,
and Rademacher's theorem. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every finite-cost optimal plan with absolutely continuous source is a
gradient graph. The convex potential is the actual path-supremum construction. -/
theorem brenier_gradient (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E×E))
    (hπ : IsOptimal μ ν π) (hfinite : squaredCost π ≠ ∞)
    (ρ : Measure E) [IsAddHaarMeasure ρ] (hac : (μ : Measure E) ≪ ρ) :
    ∃ a ∈ (π : Measure (E×E)).support,
      let φ := rockafellarPotential (π : Measure (E×E)).support a
      let T := gradient φ
      ConvexOn ℝ (potentialDomain (π : Measure (E×E)).support a) φ ∧
      Measurable T ∧ (μ : Measure E).map T = (ν : Measure E) ∧
      (π : Measure (E×E)) = (μ : Measure E).map (fun x => (x,T x)) := by
  obtain ⟨a,ha,hT,hmap,hgraph⟩ := cyclic_plan_gradient μ ν π hπ.1 ρ hac
    (optimal_support_cyclicallyMonotone μ ν π hπ hfinite) Measure.support_mem_ae
  exact ⟨a,ha,rockafellarPotential_convex _ a,hT,hmap,hgraph⟩

/-- Optimal quadratic plans are unique for an absolutely continuous source,
provided the common optimum is finite. -/
theorem brenier_unique (μ ν : ProbabilityMeasure E)
    (π₁ π₂ : ProbabilityMeasure (E×E)) (h₁ : IsOptimal μ ν π₁) (h₂ : IsOptimal μ ν π₂)
    (hfinite : squaredCost π₁ ≠ ∞) (ρ : Measure E) [IsAddHaarMeasure ρ]
    (hac : (μ : Measure E) ≪ ρ) : π₁ = π₂ := by
  let π := midpointPlan π₁ π₂
  have hπ : IsOptimal μ ν π := midpointPlan_optimal μ ν h₁ h₂
  have hπfinite : squaredCost π ≠ ∞ := by rw [hπ.2, ← h₁.2]; exact hfinite
  have hΓ := optimal_support_cyclicallyMonotone μ ν π hπ hπfinite
  have hc : ∀ᵐ z ∂(π : Measure (E×E)), z ∈ (π : Measure (E×E)).support :=
    Measure.support_mem_ae
  obtain ⟨a,ha⟩ := hc.exists
  have hf₁ : (π₁ : Measure (E×E)).fst = (μ : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) h₁.1.1
  have hf₂ : (π₂ : Measure (E×E)).fst = (μ : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) h₂.1.1
  apply Subtype.ext
  exact cyclic_measures_eq (π₁ : Measure (E×E)) (π₂ : Measure (E×E)) ρ
    (hf₁.trans hf₂.symm) (by rw [hf₁]; exact hac) hΓ
    ((absolutelyContinuous_midpoint_left π₁ π₂).ae_le hc)
    ((absolutelyContinuous_midpoint_right π₁ π₂).ae_le hc) ha

/-- Existence and uniqueness of the genuine optimal quadratic coupling under
the standard finite-second-moment and source-density hypotheses. -/
theorem brenier_existsUnique (μ ν : ProbabilityMeasure E)
    (hμ : Integrable (fun x : E => ‖x‖^2) (μ : Measure E))
    (hν : Integrable (fun x : E => ‖x‖^2) (ν : Measure E))
    (ρ : Measure E) [IsAddHaarMeasure ρ] (hac : (μ : Measure E) ≪ ρ) :
    ∃! π, IsOptimal μ ν π := by
  obtain ⟨π,hπ⟩ := exists_optimal μ ν
  refine ⟨π,hπ,?_⟩
  intro η hη
  exact brenier_unique μ ν η π hη hπ (squaredCost_finite μ ν η hη.1 hμ hν) ρ hac

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenier_gradient
#print axioms PersistencePays.QuadraticTransport.brenier_unique
#print axioms PersistencePays.QuadraticTransport.brenier_existsUnique
