import Mathlib

/-!
Foundations for the formalization of Persistence Pays (main_9.pdf).
This module makes no claim that the manuscript's main theorems have been verified.
-/

namespace PersistencePays

/-- One initial gradient and one new gradient per attempted integration step. -/
def gradientCost (epochs stepsPerEpoch : ℕ) : ℕ := epochs * stepsPerEpoch + 1

theorem gradientCost_eq (epochs stepsPerEpoch : ℕ) :
    gradientCost epochs stepsPerEpoch = epochs * stepsPerEpoch + 1 := rfl

end PersistencePays
