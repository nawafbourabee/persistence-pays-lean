import PersistencePays.QuadraticTransport

/-! Finite mixtures of actual optimal quadratic plans. -/
open MeasureTheory Set
open scoped ENNReal
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

def midpointPlan (π ρ : ProbabilityMeasure (E × E)) : ProbabilityMeasure (E × E) :=
  ⟨(2 : ℝ≥0∞)⁻¹ • ((π : Measure (E × E)) + (ρ : Measure (E × E))), by
    constructor
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    norm_num only [one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

lemma midpointPlan_fst (μ ν : ProbabilityMeasure E) {π ρ : ProbabilityMeasure (E × E)}
    (hπ : π ∈ plans μ ν) (hρ : ρ ∈ plans μ ν) :
    (midpointPlan π ρ : Measure (E × E)).fst = (μ : Measure E) := by
  have hp := congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1
  have hq := congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hρ.1
  change (π : Measure (E × E)).map Prod.fst = (μ : Measure E) at hp
  change (ρ : Measure (E × E)).map Prod.fst = (μ : Measure E) at hq
  change Measure.map Prod.fst ((2 : ℝ≥0∞)⁻¹ • ((π : Measure (E × E)) + (ρ : Measure (E × E)))) = _
  rw [Measure.map_smul, Measure.map_add _ _ measurable_fst, hp, hq]
  rw [smul_add, ← add_smul]
  rw [← mul_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

lemma midpointPlan_mem (μ ν : ProbabilityMeasure E) {π ρ : ProbabilityMeasure (E × E)}
    (hπ : π ∈ plans μ ν) (hρ : ρ ∈ plans μ ν) : midpointPlan π ρ ∈ plans μ ν := by
  constructor
  · apply Subtype.ext
    exact midpointPlan_fst μ ν hπ hρ
  · apply Subtype.ext
    have hp := congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.2
    have hq := congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hρ.2
    change (π : Measure (E × E)).map Prod.snd = (ν : Measure E) at hp
    change (ρ : Measure (E × E)).map Prod.snd = (ν : Measure E) at hq
    change Measure.map Prod.snd ((2 : ℝ≥0∞)⁻¹ • ((π : Measure (E × E)) + (ρ : Measure (E × E)))) = _
    rw [Measure.map_smul, Measure.map_add _ _ measurable_snd, hp, hq]
    rw [smul_add, ← add_smul]
    rw [← mul_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]
    rfl

lemma squaredCost_midpoint (π ρ : ProbabilityMeasure (E × E)) :
    squaredCost (midpointPlan π ρ) = (2 : ℝ≥0∞)⁻¹ * (squaredCost π + squaredCost ρ) := by
  change (∫⁻ z : E × E, ENNReal.ofReal (‖z.1-z.2‖^2) ∂((2 : ℝ≥0∞)⁻¹ • ((π : Measure (E × E)) + (ρ : Measure (E × E))))) = _
  rw [lintegral_smul_measure, lintegral_add_measure]
  rfl

lemma midpointPlan_optimal (μ ν : ProbabilityMeasure E) {π ρ : ProbabilityMeasure (E × E)}
    (hπ : IsOptimal μ ν π) (hρ : IsOptimal μ ν ρ) : IsOptimal μ ν (midpointPlan π ρ) := by
  refine ⟨midpointPlan_mem μ ν hπ.1 hρ.1, ?_⟩
  rw [squaredCost_midpoint, hπ.2, hρ.2, ← two_mul]
  rw [← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

lemma absolutelyContinuous_midpoint_left (π ρ : ProbabilityMeasure (E × E)) :
    (π : Measure (E × E)) ≪ (midpointPlan π ρ : Measure (E × E)) := by
  exact (Measure.absolutelyContinuous_of_le (le_add_of_nonneg_right (show (0 : Measure (E × E)) ≤ (ρ : Measure (E × E)) from bot_le))).smul_right (by norm_num)

lemma absolutelyContinuous_midpoint_right (π ρ : ProbabilityMeasure (E × E)) :
    (ρ : Measure (E × E)) ≪ (midpointPlan π ρ : Measure (E × E)) := by
  exact (Measure.absolutelyContinuous_of_le (le_add_of_nonneg_left (show (0 : Measure (E × E)) ≤ (π : Measure (E × E)) from bot_le))).smul_right (by norm_num)

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.midpointPlan_optimal
