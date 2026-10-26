import PersistencePays.StageKernels

/-! Propagation of bounded density ratios through invariant Markov updates. -/

namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem kernel_comp_mono (K : Kernel S T) {μ ν : Measure S} (h : μ ≤ ν) :
    K ∘ₘ μ ≤ K ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable, Measure.bind_apply hA K.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- A pointwise measure domination is propagated, not a fresh independence
assumption on the threshold or velocity at later times. -/
theorem kernel_warm_bound (K : Kernel S S) (π : Measure S)
    (hinv : K ∘ₘ π = π) (μ : Measure S) (c : ℝ≥0∞) (hμ : μ ≤ c • π) :
    K ∘ₘ μ ≤ c • π := by
  have h := kernel_comp_mono K hμ
  rwa [Measure.comp_smul, hinv] at h

theorem evolve_warm_bound (K : ℕ → Kernel S S) (π : Measure S)
    (hinv : ∀ n, K n ∘ₘ π = π) (μ : Measure S) (c : ℝ≥0∞)
    (hμ : μ ≤ c • π) (n : ℕ) : evolve K μ n ≤ c • π := by
  induction n with
  | zero => exact hμ
  | succ n ih => exact kernel_warm_bound (K n) π (hinv n) _ c ih

theorem restricted_warm_start (π : Measure S) (A : Set S) :
    (π A)⁻¹ • π.restrict A ≤ (π A)⁻¹ • π := by
  exact smul_le_smul_left _ (Measure.restrict_le_self)

section ActualSampler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.adjusted_steps_warm_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h)
    (ν : Measure ((E × E) × ℝ)) (c : ℝ≥0∞) (hν : ν ≤ c • extendedTarget U) (n : ℕ) :
    evolve (fun _ => stepKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h
      (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h)))) ν n ≤
      c • extendedTarget U :=
  evolve_warm_bound _ _ (fun _ => a.adjusted_step_invariant γ h hγ hh) ν c hν n

end ActualSampler
end PersistencePays

#print axioms PersistencePays.evolve_warm_bound
#print axioms PersistencePays.A1.adjusted_steps_warm_bound
