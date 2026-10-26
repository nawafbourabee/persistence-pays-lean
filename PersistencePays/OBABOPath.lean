import PersistencePays.Verlet
import PersistencePays.EpochAcceptance

/-!
# Actual OBABO maps with a fixed noise block

This instantiates the deterministic epoch theorem with exactly the update
order of Definition 2.2. The Gaussian laws and event probabilities are separate
measure-theoretic obligations, not assumptions or conclusions of this file.
-/

namespace PersistencePays.OBABOPath

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single OU half-step after fixing its Gaussian vector. -/
def ou (r σ : ℝ) (ξ : E) (z : E × E) : E × E :=
  (z.1, r • z.2 + σ • ξ)

/-- The actual accepted update, with an OU half-step on each side. -/
def acceptedUpdate (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (k : ℕ) (z : E × E) : E × E :=
  ou r σ (ξ' k) (verlet g h (ou r σ (ξ k) z))

/-- The actual rejected update, with velocity reversal between OU half-steps. -/
def rejectedUpdate (r σ : ℝ) (ξ ξ' : ℕ → E)
    (k : ℕ) (z : E × E) : E × E :=
  ou r σ (ξ' k) (velocityFlip (ou r σ (ξ k) z))

/-- Acceptance uses the Verlet energy defect after the first OU half-step. -/
def energyDefect (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ : ℕ → E)
    (k : ℕ) (z : E × E) : ℝ :=
  phaseEnergy U (verlet g h (ou r σ (ξ k) z)) - phaseEnergy U (ou r σ (ξ k) z)

def remainder (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ : ℕ → E)
    (k : ℕ) (z : E × E) : ℝ :=
  trapezoidDefect U g z.1 (verlet g h (ou r σ (ξ k) z)).1

theorem energyDefect_eq_correction_difference
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (k : ℕ) (z : E × E) :
    energyDefect U g h r σ ξ k z =
      gradientCorrection g h (acceptedUpdate g h r σ ξ ξ' k z).1 -
      gradientCorrection g h z.1 + remainder U g h r σ ξ k z := by
  exact verlet_energy_identity U g h (ou r σ (ξ k) z)

/-- The concrete Definition 2.2 path with the independent randomness fixed. -/
def actualPath (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) (ell : ℝ) : ℕ → (E × E) × ℝ :=
  EpochAcceptance.adjustedPath (acceptedUpdate g h r σ ξ ξ')
    (rejectedUpdate r σ ξ ξ') (energyDefect U g h r σ ξ) z ell

/-- The unadjusted OBABO path with exactly the same noise block. -/
def unadjustedPath (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) : ℕ → E × E :=
  EpochAcceptance.referencePath (acceptedUpdate g h r σ ξ ξ') z

def work (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) : ℕ → ℝ :=
  EpochAcceptance.accumulatedWork (acceptedUpdate g h r σ ξ ξ')
    (energyDefect U g h r σ ξ) z

def everyMoveAccepted (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) (ell : ℝ) : ℕ → Prop :=
  EpochAcceptance.allAccepted (acceptedUpdate g h r σ ξ ξ')
    (rejectedUpdate r σ ξ ξ') (energyDefect U g h r σ ξ) z ell

/-- Proposition 5.1's exact acceptance criterion for the concrete updates. -/
theorem everyMoveAccepted_iff
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) (ell : ℝ) (n : ℕ) :
    everyMoveAccepted U g h r σ ξ ξ' z ell n ↔
      ∀ j, 1 ≤ j → j ≤ n → work U g h r σ ξ ξ' z j < ell :=
  EpochAcceptance.allAccepted_iff_prefixWork _ _ _ _ _ _

/-- The actual and unadjusted states agree on the all-acceptance event. -/
theorem actualPath_eq_unadjusted_on_acceptance
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) (ell : ℝ) (n : ℕ)
    (ha : everyMoveAccepted U g h r σ ξ ξ' z ell n) :
    actualPath U g h r σ ξ ξ' z ell n =
      (unadjustedPath g h r σ ξ ξ' z n, ell - work U g h r σ ξ ξ' z n) :=
  EpochAcceptance.adjustedPath_eq_reference_of_allAccepted _ _ _ _ _ _ ha

/-- Exact telescoping of the position-only correction through both OU steps. -/
theorem work_telescope
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E × E) (n : ℕ) :
    work U g h r σ ξ ξ' z n =
      gradientCorrection g h (unadjustedPath g h r σ ξ ξ' z n).1 -
      gradientCorrection g h z.1 +
      ∑ k ∈ Finset.range n,
        remainder U g h r σ ξ k (unadjustedPath g h r σ ξ ξ' z k) := by
  apply EpochAcceptance.accumulatedWork_telescope
    (acceptedUpdate g h r σ ξ ξ') (energyDefect U g h r σ ξ)
    (remainder U g h r σ ξ) (fun z => gradientCorrection g h z.1) z
  exact energyDefect_eq_correction_difference U g h r σ ξ ξ'

end

end PersistencePays.OBABOPath
