import PersistencePays.OBABOProbability
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# A concrete epoch kernel with all Gaussian draws and the carried threshold

The finite product noise law supplies exactly two independent standard
Gaussian vectors per attempted step. A separate rate-one exponential draw is
made once per epoch. The map into phase space uses `actualPath`, so rejected
steps retain their threshold and reverse the intermediate velocity.
-/

namespace PersistencePays.OBABOPath

open MeasureTheory ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_actualPath
    {Ω : Type*} [MeasurableSpace Ω]
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (ξ ξ' : ℕ → Ω → E) (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : Ω → E × E) (hz : Measurable z) (ell : Ω → ℝ) (hell : Measurable ell) (n : ℕ) :
    Measurable (fun ω => actualPath U g h r σ (fun k => ξ k ω) (fun k => ξ' k ω)
      (z ω) (ell ω) n) := by
  induction n with
  | zero => exact hz.prodMk hell
  | succ n ih =>
      let state := fun ω => actualPath U g h r σ (fun k => ξ k ω) (fun k => ξ' k ω)
        (z ω) (ell ω) n
      have hd : Measurable (fun ω => energyDefect U g h r σ (fun k => ξ k ω)
          n (state ω).1) := by
        dsimp only [energyDefect, phaseEnergy, ou, verlet, kick, drift, state]
        fun_prop
      have ha : Measurable (fun ω => acceptedUpdate g h r σ
          (fun k => ξ k ω) (fun k => ξ' k ω) n (state ω).1) := by
        dsimp only [acceptedUpdate, ou, verlet, kick, drift, state]
        fun_prop
      have hr : Measurable (fun ω => rejectedUpdate r σ
          (fun k => ξ k ω) (fun k => ξ' k ω) n (state ω).1) := by
        dsimp only [rejectedUpdate, ou, velocityFlip, state]
        fun_prop
      exact Measurable.ite (measurableSet_lt hd ih.snd)
        (ha.prodMk (ih.snd.sub hd)) (hr.prodMk ih.snd)

abbrev NoiseBlock (E : Type*) (n : ℕ) := (Fin n → E) × (Fin n → E)

def firstNoise (n : ℕ) (k : ℕ) (b : NoiseBlock E n) : E :=
  if hk : k < n then b.1 ⟨k, hk⟩ else 0

def secondNoise (n : ℕ) (k : ℕ) (b : NoiseBlock E n) : E :=
  if hk : k < n then b.2 ⟨k, hk⟩ else 0

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem measurable_firstNoise (n k : ℕ) : Measurable (firstNoise (E := E) n k) := by
  unfold firstNoise
  split_ifs <;> fun_prop

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem measurable_secondNoise (n k : ℕ) : Measurable (secondNoise (E := E) n k) := by
  unfold secondNoise
  split_ifs <;> fun_prop

variable [FiniteDimensional ℝ E]

def gaussianBlock (n : ℕ) : Measure (NoiseBlock E n) :=
  (Measure.pi (fun _ : Fin n => stdGaussian E)).prod
    (Measure.pi (fun _ : Fin n => stdGaussian E))

instance gaussianBlock_probability (n : ℕ) : IsProbabilityMeasure (gaussianBlock (E := E) n) := by
  unfold gaussianBlock
  infer_instance

def epochRandomness (n : ℕ) : Measure (NoiseBlock E n × ℝ) :=
  (gaussianBlock (E := E) n).prod (expMeasure 1)

instance epochRandomness_probability (n : ℕ) : IsProbabilityMeasure (epochRandomness (E := E) n) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  unfold epochRandomness
  infer_instance

/-- The phase endpoint of one actual epoch from a fixed initial phase. -/
def epochEndpoint (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n : ℕ)
    (p : (E × E) × (NoiseBlock E n × ℝ)) : E × E :=
  (actualPath U g h r σ (fun k => firstNoise n k p.2.1)
    (fun k => secondNoise n k p.2.1) p.1 p.2.2 n).1

theorem measurable_epochEndpoint (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    Measurable (epochEndpoint U g h r σ n) := by
  exact (measurable_actualPath (Ω := (E × E) × (NoiseBlock E n × ℝ)) U hU g hg h r σ
    (fun k p => firstNoise n k p.2.1) (fun k p => secondNoise n k p.2.1)
    (fun k => (measurable_firstNoise n k).comp measurable_snd.fst)
    (fun k => (measurable_secondNoise n k).comp measurable_snd.fst)
    Prod.fst measurable_fst (fun p => p.2.2) measurable_snd.snd n).fst

/-- The exact Definition 2.2 phase-space epoch kernel. -/
def epochKernel (U : E → ℝ) (_hU : Measurable U) (g : E → E) (_hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) : Kernel (E × E) (E × E) :=
  ((Kernel.id : Kernel (E × E) (E × E)) ×ₖ
    Kernel.const (E × E) (epochRandomness (E := E) n)).map (epochEndpoint U g h r σ n)

instance epochKernel_markov (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) : IsMarkovKernel (epochKernel U hU g hg h r σ n) := by
  unfold epochKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_epochEndpoint U hU g hg h r σ n)

/-- The concrete independent Gaussian block satisfies Proposition 5.1's
exact rejection formula; there are no remaining measurability hypotheses. -/
theorem gaussian_epoch_rejection_probability
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (z : E × E) (n : ℕ) (hn : 0 < n) :
    (epochRandomness (E := E) n).real
      {p | ¬ everyMoveAccepted U g h r σ
        (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n} =
      ∫ b, 1 - Real.exp (-max
        (peak U g h r σ (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n hn) 0)
        ∂gaussianBlock n := by
  exact epoch_rejection_probability (gaussianBlock n) U hU g hg h r σ
    (firstNoise n) (secondNoise n) (measurable_firstNoise n) (measurable_secondNoise n) z n hn

end

end PersistencePays.OBABOPath
