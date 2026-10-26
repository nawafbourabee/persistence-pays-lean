import PersistencePays.OBABOPath
import PersistencePays.EpochProbability

/-!
# Exact rejection probability of an OBABO epoch

The work maximum is proved measurable from the actual OBABO maps. The result
holds for any measurable noise block, including the independent Gaussian block
in Definition 2.2. The threshold law is the actual independent Exp(1) measure.
-/

namespace PersistencePays.OBABOPath

open MeasureTheory ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_unadjustedPath
    (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (ξ ξ' : ℕ → Ω → E) (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : E × E) (n : ℕ) :
    Measurable (fun ω => unadjustedPath g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n) := by
  induction n with
  | zero => simp [unadjustedPath, EpochAcceptance.referencePath]
  | succ n ih =>
      change Measurable (fun ω => ou r σ (ξ' n ω)
        (verlet g h (ou r σ (ξ n ω)
          (unadjustedPath g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n))))
      dsimp only [ou, verlet, kick, drift]
      fun_prop

theorem measurable_work
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (ξ ξ' : ℕ → Ω → E) (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : E × E) (n : ℕ) :
    Measurable (fun ω => work U g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n) := by
  induction n with
  | zero => simp [work, EpochAcceptance.accumulatedWork]
  | succ n ih =>
      have hp := measurable_unadjustedPath g hg h r σ ξ ξ' hξ hξ' z n
      change Measurable (fun ω =>
        work U g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n +
        energyDefect U g h r σ (fun k => ξ k ω) n
          (unadjustedPath g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n))
      apply ih.add
      dsimp only [energyDefect, phaseEnergy, ou, verlet, kick, drift]
      fun_prop

def peak (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (z : E × E) (n : ℕ) (hn : 0 < n) : ℝ :=
  EpochAcceptance.peakWork (acceptedUpdate g h r σ ξ ξ')
    (energyDefect U g h r σ ξ) z n hn

theorem measurable_peak
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (ξ ξ' : ℕ → Ω → E) (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : E × E) (n : ℕ) (hn : 0 < n) :
    Measurable (fun ω => peak U g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n hn) := by
  have hm := Finset.measurable_sup' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
    (fun k _ => measurable_work U hU g hg h r σ ξ ξ' hξ hξ' z (k + 1))
  convert hm using 1
  ext ω
  simp [peak, EpochAcceptance.peakWork, work]

/-- The exact expectation formula in Proposition 5.1 for the concrete
Definition 2.2 updates, with all algorithmic measurability discharged. -/
theorem epoch_rejection_probability
    (μ : Measure Ω) (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (ξ ξ' : ℕ → Ω → E)
    (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : E × E) (n : ℕ) (hn : 0 < n) :
    (μ.prod (expMeasure 1)).real
      {p : Ω × ℝ | ¬ everyMoveAccepted U g h r σ
        (fun k => ξ k p.1) (fun k => ξ' k p.1) z p.2 n} =
      ∫ ω, 1 - Real.exp (-max
        (peak U g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) z n hn) 0) ∂μ := by
  exact EpochAcceptance.rejection_probability_independent_noise μ
    (fun ω => acceptedUpdate g h r σ (fun k => ξ k ω) (fun k => ξ' k ω))
    (fun ω => rejectedUpdate r σ (fun k => ξ k ω) (fun k => ξ' k ω))
    (fun ω => energyDefect U g h r σ (fun k => ξ k ω)) (fun _ => z) n hn
    (measurable_peak U hU g hg h r σ ξ ξ' hξ hξ' z n hn)

end

end PersistencePays.OBABOPath
