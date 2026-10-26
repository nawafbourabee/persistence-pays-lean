import PersistencePays.GibbsProduct
import PersistencePays.KernelEntropy
import PersistencePays.GibbsRegularity
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Concrete Markov kernels for every stage of Definition 2.2. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def velocityOUKernel (r σ : ℝ) : Kernel E E :=
  (Kernel.id ×ₖ Kernel.const E (stdGaussian E)).map (gaussianOU r σ)

instance velocityOUKernel_markov (r σ : ℝ) : IsMarkovKernel (velocityOUKernel (E := E) r σ) :=
  Kernel.IsMarkovKernel.map _ (by unfold gaussianOU; fun_prop)

theorem velocityOUKernel_invariant (r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) :
    velocityOUKernel r σ ∘ₘ stdGaussian E = stdGaussian E := by
  unfold velocityOUKernel
  rw [← Measure.map_comp _ _ (by unfold gaussianOU; fun_prop),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  exact (gaussianOU_preserving r σ hnorm).map_eq

def phaseOUKernel (r σ : ℝ) : Kernel (E × E) (E × E) :=
  Kernel.id ∥ₖ velocityOUKernel r σ

instance phaseOUKernel_markov (r σ : ℝ) : IsMarkovKernel (phaseOUKernel (E := E) r σ) := by
  unfold phaseOUKernel
  infer_instance

def extendedOUKernel (r σ : ℝ) : Kernel ((E × E) × ℝ) ((E × E) × ℝ) :=
  phaseOUKernel r σ ∥ₖ Kernel.id

instance extendedOUKernel_markov (r σ : ℝ) : IsMarkovKernel (extendedOUKernel (E := E) r σ) := by
  unfold extendedOUKernel
  infer_instance

theorem phaseOUKernel_invariant (U : E → ℝ) (r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) :
    phaseOUKernel r σ ∘ₘ phaseGibbs U = phaseGibbs U := by
  unfold phaseOUKernel phaseGibbs
  rw [← Measure.prod_comp_right, velocityOUKernel_invariant r σ hnorm]

theorem extendedOUKernel_invariant (U : E → ℝ) (r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) :
    extendedOUKernel r σ ∘ₘ extendedTarget U = extendedTarget U := by
  unfold extendedOUKernel extendedTarget
  rw [← Measure.prod_comp_left, phaseOUKernel_invariant U r σ hnorm]

def adjustedStageKernel (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) : Kernel ((E × E) × ℝ) ((E × E) × ℝ) :=
  Kernel.deterministic (adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h))
    (verlet_adjusted_preserves_extendedGibbs U hU g hg h).measurable

instance adjustedStageKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) : IsMarkovKernel (adjustedStageKernel U hU g hg h) := by
  unfold adjustedStageKernel
  infer_instance

theorem adjustedStageKernel_invariant (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) :
    adjustedStageKernel U hU g hg h ∘ₘ extendedTarget U = extendedTarget U := by
  rw [adjustedStageKernel, Measure.deterministic_comp_eq_map]
  exact (verlet_adjusted_preserves_target U hU hi g hg h).map_eq

/-- One attempted Definition 2.2 step: independent OU noise, adjusted Verlet,
then a second independent OU half-step. The threshold is carried in the state. -/
def stepKernel (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) : Kernel ((E × E) × ℝ) ((E × E) × ℝ) :=
  extendedOUKernel r σ ∘ₖ (adjustedStageKernel U hU g hg h ∘ₖ extendedOUKernel r σ)

instance stepKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) : IsMarkovKernel (stepKernel U hU g hg h r σ) := by
  unfold stepKernel
  infer_instance

theorem stepKernel_invariant (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) :
    stepKernel U hU g hg h r σ ∘ₘ extendedTarget U = extendedTarget U := by
  unfold stepKernel
  rw [← Measure.comp_assoc, ← Measure.comp_assoc,
    extendedOUKernel_invariant U r σ hnorm,
    adjustedStageKernel_invariant U hU hi g hg h,
    extendedOUKernel_invariant U r σ hnorm]

/-- Gibbs invariance over every finite sequence of actual attempted steps,
including rejected proposals and the non-refreshed threshold. -/
theorem attempted_steps_invariant (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) (n : ℕ) :
    evolve (fun _ => stepKernel U hU g hg h r σ) (extendedTarget U) n = extendedTarget U :=
  evolve_invariant _ _ (fun _ => stepKernel_invariant U hU hi g hg h r σ hnorm) n

/-- Lemma 2.3 for a single attempted step, with all normalization and force
regularity premises discharged from the actual assumption (A1). -/
theorem A1.adjusted_step_invariant {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) :
    stepKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h
      (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) ∘ₘ
      extendedTarget U = extendedTarget U := by
  apply stepKernel_invariant U _ a.gibbs_integrable
  have he₁ : -γ * h / 2 = -(γ * h / 2) := by ring
  have he₂ : -γ * h = -2 * (γ * h / 2) := by ring
  rw [he₁, he₂]
  exact ou_coefficients (γ * h / 2) (by positivity)

def iterateKernel {S : Type*} [MeasurableSpace S] (K : Kernel S S) : ℕ → Kernel S S
  | 0 => Kernel.id
  | n + 1 => K ∘ₖ iterateKernel K n

instance iterateKernel_markov {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) : IsMarkovKernel (iterateKernel K n) := by
  induction n with
  | zero => unfold iterateKernel; infer_instance
  | succ n ih => unfold iterateKernel; infer_instance

theorem iterateKernel_invariant {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsMarkovKernel K] (μ : Measure S)
    (hμ : K ∘ₘ μ = μ) (n : ℕ) : iterateKernel K n ∘ₘ μ = μ := by
  induction n with
  | zero => exact Measure.id_comp
  | succ n ih =>
    rw [iterateKernel, ← Measure.comp_assoc, ih, hμ]

/-- The sequential epoch construction draws one independent Exp(1) threshold,
carries it through n attempted steps, and then forgets it. -/
def sequentialEpochKernel (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) : Kernel (E × E) (E × E) :=
  ((iterateKernel (stepKernel U hU g hg h r σ) n) ∘ₖ
    (Kernel.id ×ₖ Kernel.const (E × E) (expMeasure 1))).map Prod.fst

instance sequentialEpochKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    IsMarkovKernel (sequentialEpochKernel U hU g hg h r σ n) :=
  Kernel.IsMarkovKernel.map _ measurable_fst

theorem sequentialEpochKernel_invariant (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) (n : ℕ) :
    sequentialEpochKernel U hU g hg h r σ n ∘ₘ phaseGibbs U = phaseGibbs U := by
  unfold sequentialEpochKernel
  rw [← Measure.map_comp _ _ measurable_fst, ← Measure.comp_assoc,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  change (iterateKernel (stepKernel U hU g hg h r σ) n ∘ₘ extendedTarget U).map Prod.fst = _
  rw [iterateKernel_invariant _ _ (stepKernel_invariant U hU hi g hg h r σ hnorm)]
  simp [extendedTarget]

theorem A1.epoch_invariant {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) (n : ℕ) :
    sequentialEpochKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h
      (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) n ∘ₘ
      phaseGibbs U = phaseGibbs U := by
  apply sequentialEpochKernel_invariant U _ a.gibbs_integrable
  have he₁ : -γ * h / 2 = -(γ * h / 2) := by ring
  have he₂ : -γ * h = -2 * (γ * h / 2) := by ring
  rw [he₁, he₂]
  exact ou_coefficients (γ * h / 2) (by positivity)

end PersistencePays

#print axioms PersistencePays.stepKernel_invariant
#print axioms PersistencePays.attempted_steps_invariant
#print axioms PersistencePays.A1.adjusted_step_invariant
#print axioms PersistencePays.A1.epoch_invariant
