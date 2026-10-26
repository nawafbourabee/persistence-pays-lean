import PersistencePays.OptimalPlanExistence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Quadratic transport cost and genuine finite-cost optimal couplings. -/
open MeasureTheory Set Filter
open scoped ENNReal
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

def squaredCost (π : ProbabilityMeasure (E × E)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖^2) ∂(π : Measure (E × E))

def cost (μ ν : ProbabilityMeasure E) : ℝ≥0∞ := ⨅ π ∈ plans μ ν, squaredCost π

def IsOptimal (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E × E)) : Prop :=
  π ∈ plans μ ν ∧ squaredCost π = cost μ ν

theorem squaredCost_integrable (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E × E))
    (hπ : π ∈ plans μ ν) (hμ : Integrable (fun x : E => ‖x‖^2) (μ : Measure E))
    (hν : Integrable (fun x : E => ‖x‖^2) (ν : Measure E)) :
    Integrable (fun z : E × E => ‖z.1-z.2‖^2) (π : Measure (E × E)) := by
  have hf : (π : Measure (E × E)).map Prod.fst = (μ : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1
  have hs : (π : Measure (E × E)).map Prod.snd = (ν : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.2
  have hfi : Integrable (fun z : E × E => ‖z.1‖^2) (π : Measure (E × E)) := by
    rw [← hf] at hμ
    exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 hμ
  have hsi : Integrable (fun z : E × E => ‖z.2‖^2) (π : Measure (E × E)) := by
    rw [← hs] at hν
    exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).1 hν
  apply ((hfi.add hsi).const_mul 2).mono' (by fun_prop)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  have hh := norm_sub_le z.1 z.2
  have hn := norm_nonneg (z.1-z.2)
  have hsq := (sq_le_sq₀ hn (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hh
  nlinarith [sq_nonneg (‖z.1‖-‖z.2‖)]

theorem squaredCost_finite (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E × E))
    (hπ : π ∈ plans μ ν) (hμ : Integrable (fun x : E => ‖x‖^2) (μ : Measure E))
    (hν : Integrable (fun x : E => ‖x‖^2) (ν : Measure E)) : squaredCost π ≠ ∞ := by
  exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall (fun z : E × E => sq_nonneg ‖z.1-z.2‖))).2
      (squaredCost_integrable μ ν π hπ hμ hν)

theorem exists_optimal (μ ν : ProbabilityMeasure E) : ∃ π, IsOptimal μ ν π := by
  obtain ⟨π, hπ, hmin⟩ := exists_optimal_plan μ ν (fun z : E × E => ‖z.1-z.2‖^2) (by fun_prop)
  refine ⟨π, hπ, le_antisymm ?_ ?_⟩
  · exact le_iInf (fun ρ => le_iInf (fun hρ => hmin ρ hρ))
  · exact iInf₂_le π hπ

theorem cost_finite (μ ν : ProbabilityMeasure E)
    (hμ : Integrable (fun x : E => ‖x‖^2) (μ : Measure E))
    (hν : Integrable (fun x : E => ‖x‖^2) (ν : Measure E)) : cost μ ν ≠ ∞ := by
  obtain ⟨π, hπ⟩ := exists_optimal μ ν
  rw [← hπ.2]
  exact squaredCost_finite μ ν π hπ.1 hμ hν

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.exists_optimal
#print axioms PersistencePays.QuadraticTransport.cost_finite
