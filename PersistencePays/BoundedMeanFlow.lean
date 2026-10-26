import Mathlib.Analysis.ODE.ExistUnique

/-! Finite-interval flow existence from literal bounds on a vector field.
These are ODE foundations for the smoothed free-flight conditional mean;
the law-transport identity must be established separately. -/
noncomputable section
namespace PersistencePays
open Set Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem bounded_field_trajectory {f : ℝ → E → E} {a b : ℝ}
    (τ : Icc a b) (B K : ℝ≥0)
    (hc : Continuous f.uncurry)
    (hl : ∀ s ∈ Icc a b, LipschitzWith K (f s))
    (hb : ∀ s ∈ Icc a b, ∀ x, ‖f s x‖ ≤ B) (x : E) :
    ∃ X : ℝ → E, X τ = x ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt X (f s (X s)) (Icc a b) s := by
  let R : ℝ≥0 := B*Real.toNNReal (max (b-τ) (τ-a))
  have hd : 0 ≤ max (b-τ) (τ-a) := le_max_of_le_left (sub_nonneg.mpr τ.property.2)
  have hpl : IsPicardLindelof f τ x R 0 B K := by
    constructor
    · intro s hs
      exact (hl s hs).lipschitzOnWith
    · intro y _
      exact (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro s hs y _
      exact hb s hs y
    · simp [R,Real.coe_toNNReal _ hd]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem bounded_field_local_flow {f : ℝ → E → E} {a b : ℝ}
    (τ : Icc a b) (B K r : ℝ≥0)
    (hc : Continuous f.uncurry)
    (hl : ∀ s ∈ Icc a b, LipschitzWith K (f s))
    (hb : ∀ s ∈ Icc a b, ∀ x, ‖f s x‖ ≤ B) (x : E) :
    ∃ X : E → ℝ → E,
      (∀ y ∈ closedBall x r, X y τ = y ∧
        ∀ s ∈ Icc a b, HasDerivWithinAt (X y) (f s (X y s)) (Icc a b) s) ∧
      ∃ K' : ℝ≥0, ∀ s ∈ Icc a b, LipschitzOnWith K' (fun y => X y s) (closedBall x r) := by
  let R : ℝ≥0 := B*Real.toNNReal (max (b-τ) (τ-a))+r
  have hd : 0 ≤ max (b-τ) (τ-a) := le_max_of_le_left (sub_nonneg.mpr τ.property.2)
  have hpl : IsPicardLindelof f τ x R r B K := by
    constructor
    · intro s hs
      exact (hl s hs).lipschitzOnWith
    · intro y _
      exact (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro s hs y _
      exact hb s hs y
    · simp [R,Real.coe_toNNReal _ hd]
  exact hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith

end PersistencePays
#print axioms PersistencePays.bounded_field_trajectory
#print axioms PersistencePays.bounded_field_local_flow
