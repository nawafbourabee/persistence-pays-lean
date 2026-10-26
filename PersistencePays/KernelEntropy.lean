import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Invariance

/-!
Measure-level entropy facts for the verification of Persistence Pays.

These results use mathlib's actual Kullback--Leibler divergence, measure push-forward,
and Markov kernels. They do not establish invariance of the paper's sampler or its
strict entropy contraction. Invariance remains an explicit premise here until the
sampler construction proves it.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace PersistencePays

variable {S : Type*} [MeasurableSpace S]

/-- Apply a possibly time-dependent sequence of kernels, in chronological order. -/
noncomputable def evolve (K : ℕ → Kernel S S) (μ : Measure S) : ℕ → Measure S
  | 0 => μ
  | n + 1 => K n ∘ₘ evolve K μ n

@[simp] theorem evolve_zero (K : ℕ → Kernel S S) (μ : Measure S) :
    evolve K μ 0 = μ := rfl

@[simp] theorem evolve_succ (K : ℕ → Kernel S S) (μ : Measure S) (n : ℕ) :
    evolve K μ (n + 1) = K n ∘ₘ evolve K μ n := rfl

instance evolve_isProbability (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (evolve K μ n) := by
  induction n with
  | zero => simpa only [evolve_zero] using (inferInstance : IsProbabilityMeasure μ)
  | succ n ih =>
    let := ih
    simp only [evolve_succ]
    infer_instance

/-- The actual invariant measure is unchanged under any finite sequence of
    kernels preserving that measure. No reversibility assumption is used. -/
theorem evolve_invariant (K : ℕ → Kernel S S) (π : Measure S)
    (hK : ∀ n, K n ∘ₘ π = π) (n : ℕ) : evolve K π n = π := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [evolve_succ, ih] using hK n

/-- Data processing against an invariant reference measure. -/
theorem klDiv_step_le (K : Kernel S S) [IsMarkovKernel K]
    (μ π : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (hπ : K ∘ₘ π = π) : klDiv (K ∘ₘ μ) π ≤ klDiv μ π := by
  simpa only [hπ] using klDiv_comp_right_le μ π K

/-- Entropy cannot increase under any finite, possibly time-dependent sequence of
    invariant Markov transitions. This also applies between epoch refreshes. -/
theorem klDiv_evolve_le (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : ∀ n, K n ∘ₘ π = π) (n : ℕ) :
    klDiv (evolve K μ n) π ≤ klDiv μ π := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (klDiv_step_le (K n) (evolve K μ n) π (hπ n)).trans ih

/-- Finite relative entropy, including the required integrability of the
    log-likelihood ratio, propagates through invariant Markov steps. -/
theorem finite_entropy_evolve (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : ∀ n, K n ∘ₘ π = π) (hμ : klDiv μ π ≠ ∞) (n : ℕ) :
    evolve K μ n ≪ π ∧ Integrable (llr (evolve K μ n) π) (evolve K μ n) := by
  apply klDiv_ne_top_iff.mp
  exact ne_top_of_le_ne_top hμ (klDiv_evolve_le K μ π hπ n)

/-- Attaching the same fresh auxiliary random variable to both measures does not
    alter their relative entropy. This is the chain-rule statement needed for a
    fresh independent threshold or fresh Gaussian noise. -/
theorem klDiv_attach_same_kernel {T : Type*} [MeasurableSpace T]
    (μ π : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (K : Kernel S T) [IsMarkovKernel K] :
    klDiv (μ ⊗ₘ K) (π ⊗ₘ K) = klDiv μ π :=
  klDiv_compProd_left μ π K

/-- A measurable observation of the state, including projection to position,
    cannot increase relative entropy. -/
theorem klDiv_observation_le {T : Type*} [MeasurableSpace T]
    (μ π : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (f : S → T) (hf : Measurable f) :
    klDiv (μ.map f) (π.map f) ≤ klDiv μ π :=
  klDiv_map_le μ π hf

end PersistencePays

#print axioms PersistencePays.klDiv_evolve_le
#print axioms PersistencePays.finite_entropy_evolve
#print axioms PersistencePays.klDiv_attach_same_kernel
#print axioms PersistencePays.klDiv_observation_le
