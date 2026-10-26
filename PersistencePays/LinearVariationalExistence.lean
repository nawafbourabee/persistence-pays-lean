import PersistencePays.BoundedMeanFlow
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Actual local solutions of the matrix variational equation. The time
restriction is uniform in the initial position of the nonlinear flow. -/
noncomputable section
namespace PersistencePays
open Set Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem linear_variational_trajectory {A : ℝ → E →L[ℝ] E} {a b : ℝ}
    (τ : Icc a b) (K : ℝ≥0) (hc : ContinuousOn A (Icc a b))
    (hb : ∀ t∈Icc a b, ‖A t‖≤K)
    (ht : (2*(K:ℝ))*max (b-τ) (τ-a)≤1) :
    ∃ J : ℝ → E →L[ℝ] E, J τ=ContinuousLinearMap.id ℝ E ∧
      ∀ t∈Icc a b, HasDerivWithinAt J ((A t).comp (J t)) (Icc a b) t := by
  let f : ℝ → (E →L[ℝ] E) → (E →L[ℝ] E) := fun t J => (A t).comp J
  have hpl : IsPicardLindelof f τ (ContinuousLinearMap.id ℝ E) 1 0 (2*K) K := by
    constructor
    · intro t ht
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro J J'
      simp only [f,dist_eq_norm]
      change ‖(A t).comp J-(A t).comp J'‖≤(K:ℝ)*‖J-J'‖
      rw [← ContinuousLinearMap.comp_sub]
      exact ((A t).opNorm_comp_le (J-J')).trans
        (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _))
    · intro J hJ
      exact (ContinuousLinearMap.compL ℝ E E E).continuous₂.comp_continuousOn
        (hc.prodMk continuousOn_const)
    · intro t ht J hJ
      have hJ' : ‖J‖≤2 := by
        have hdist : ‖J-ContinuousLinearMap.id ℝ E‖≤1 := by
          simpa only [mem_closedBall,dist_eq_norm,NNReal.coe_one] using hJ
        calc
          ‖J‖ ≤ ‖J-ContinuousLinearMap.id ℝ E‖+‖ContinuousLinearMap.id ℝ E‖ :=
            by simpa only [sub_add_cancel] using norm_add_le (J-ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
          _ ≤ 1+1 := add_le_add hdist ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      calc
        ‖f t J‖ ≤ ‖A t‖*‖J‖ := (A t).opNorm_comp_le J
        _ ≤ (K:ℝ)*2 := mul_le_mul (hb t ht) hJ' (norm_nonneg _) K.property
        _ = ((2*K:ℝ≥0):ℝ) := by simp; ring
    · simpa using ht
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end PersistencePays
#print axioms PersistencePays.linear_variational_trajectory
