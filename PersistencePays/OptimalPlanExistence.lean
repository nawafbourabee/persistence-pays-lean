import PersistencePays.TransportPlanCompactness
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Normed.Group.Real

/-! Existence of actual optimal probability couplings for continuous
nonnegative costs on Polish spaces; in particular, squared Euclidean cost. -/
open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]

def clippedCost (c : S → ℝ) (hc : Continuous c) (n : ℕ) : S →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (Real.toNNReal (c x)) (n : ℝ≥0),
      (continuous_real_toNNReal.comp hc).min continuous_const⟩ (2*n)
    (by
      intro x y
      change |((min (Real.toNNReal (c x)) (n : ℝ≥0) : ℝ≥0) : ℝ) -
        ((min (Real.toNNReal (c y)) (n : ℝ≥0) : ℝ≥0) : ℝ)| ≤ 2*n
      have hx0 := (min (Real.toNNReal (c x)) (n : ℝ≥0)).coe_nonneg
      have hy0 := (min (Real.toNNReal (c y)) (n : ℝ≥0)).coe_nonneg
      have hx : ((min (Real.toNNReal (c x)) (n : ℝ≥0) : ℝ≥0) : ℝ) ≤ (n : ℝ) :=
        NNReal.coe_le_coe.mpr (min_le_right _ _)
      have hy : ((min (Real.toNNReal (c y)) (n : ℝ≥0) : ℝ≥0) : ℝ) ≤ (n : ℝ) :=
        NNReal.coe_le_coe.mpr (min_le_right _ _)
      exact abs_le.mpr ⟨by linarith, by linarith⟩)

lemma clippedCost_coe (c : S → ℝ) (hc : Continuous c) (n : ℕ) (x : S) :
    ((clippedCost c hc n x : ℝ≥0) : ℝ≥0∞) = min (ENNReal.ofReal (c x)) (n : ℝ≥0∞) := by
  simp [clippedCost, ENNReal.ofReal]

theorem cost_lowerSemicontinuous (c : S → ℝ) (hc : Continuous c) :
    LowerSemicontinuous (fun π : ProbabilityMeasure S => ∫⁻ x, ENNReal.ofReal (c x) ∂(π : Measure S)) := by
  have heq : (fun π : ProbabilityMeasure S => ∫⁻ x, ENNReal.ofReal (c x) ∂(π : Measure S)) =
      (fun π : ProbabilityMeasure S => ⨆ n : ℕ, ∫⁻ x, clippedCost c hc n x ∂(π : Measure S)) := by
    funext π
    rw [← lintegral_iSup]
    · apply lintegral_congr
      intro x
      simp_rw [clippedCost_coe]
      apply le_antisymm
      · obtain ⟨n, hn⟩ := exists_nat_ge (c x)
        apply le_iSup_of_le n
        rw [min_eq_left]
        simpa using ENNReal.ofReal_le_ofReal hn
      · exact iSup_le (fun n => min_le_left _ _)
    · intro n
      exact (ENNReal.continuous_coe.comp (clippedCost c hc n).continuous).measurable
    · intro n m hnm x
      dsimp only
      rw [clippedCost_coe, clippedCost_coe]
      exact min_le_min_left _ (by exact_mod_cast hnm)
  rw [heq]
  exact lowerSemicontinuous_iSup (fun n =>
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (clippedCost c hc n)).lowerSemicontinuous)

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  [TopologicalSpace E] [TopologicalSpace F] [BorelSpace E] [BorelSpace F]
  [PolishSpace E] [PolishSpace F]

theorem exists_optimal_plan (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure F)
    (c : E × F → ℝ) (hc : Continuous c) :
    ∃ π ∈ plans μ ν, ∀ ρ ∈ plans μ ν,
      (∫⁻ z, ENNReal.ofReal (c z) ∂(π : Measure (E × F))) ≤
        ∫⁻ z, ENNReal.ofReal (c z) ∂(ρ : Measure (E × F)) := by
  exact ((cost_lowerSemicontinuous c hc).lowerSemicontinuousOn _).exists_isMinOn
    (plans_nonempty μ ν) (plans_compact μ ν)

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.exists_optimal_plan
