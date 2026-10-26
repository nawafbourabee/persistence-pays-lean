import PersistencePays.StoppedFlightPrefix
import PersistencePays.ClippedBudget
import PersistencePays.EpochCoupling

/-! The actual finite-epoch rejection bound used in Proposition 6.1. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem maximalEnergyEvent_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ : ℝ) (n : ℕ) (z : E×E) (s : ℝ) :
    MeasurableSet (maximalEnergyEvent U (gradient U) h r σ n z s) := by
  have hU := a.twice_contDiff.continuous.measurable
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hH : Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop
  have hi (k : ℕ) : MeasurableSet {b : NoiseBlock E n | k ≤ n ∧
      s < phaseEnergy U (unadjustedPath (gradient U) h r σ
        (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k)} := by
    by_cases hk : k ≤ n
    · simpa only [hk, true_and, Function.comp_def] using measurableSet_lt measurable_const
        (hH.comp (measurable_unadjustedPath (gradient U) hg h r σ (firstNoise n)
          (secondNoise n) (measurable_firstNoise n) (measurable_secondNoise n) z k))
    · simp only [hk, false_and, setOf_false, MeasurableSet.empty]
  simpa only [maximalEnergyEvent, setOf_exists] using MeasurableSet.iUnion hi

theorem remainder_le_cubic_flight {U : E → ℝ} {L LH h : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hh : 0 ≤ h)
    (r σ : ℝ) (n k : ℕ) (z : E×E) (b : NoiseBlock E n) :
    |remainder U (gradient U) h r σ (fun j => firstNoise n j b) k
      (unadjustedPath (gradient U) h r σ (fun j => firstNoise n j b)
        (fun j => secondNoise n j b) z k)| ≤
      LH*h^3/12 * ‖stepFlight (gradient U) h r σ n k z b‖^3 := by
  have ht := (lemma_2_1 a a2 hh (ou r σ (firstNoise n k b)
    (unadjustedPath (gradient U) h r σ (fun j => firstNoise n j b)
      (fun j => secondNoise n j b) z k))).2.2.1
  convert ht using 1 <;> simp only [remainder, stepFlight, ou] <;> ring

theorem rejectionBudget_le_on_energy {U : E → ℝ} {L LH h : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hh : 0 ≤ h)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (r σ : ℝ) (n : ℕ) (z : E×E) (s : ℝ) (b : NoiseBlock E n)
    (hb : b ∉ maximalEnergyEvent U (gradient U) h r σ n z s) :
    rejectionBudget U (U a.minimizer) L (gradient U) h r σ
      (fun j => firstNoise n j b) (fun j => secondNoise n j b) z n ≤
      h^2*L/4*s + LH*h^3/12 * ∑ k ∈ Finset.range n,
        ‖stepFlight (gradient U) h r σ n k z b‖^3 := by
  have hp : potentialPeak U (U a.minimizer) (gradient U) h r σ
      (fun j => firstNoise n j b) (fun j => secondNoise n j b) z n ≤ s := by
    apply Finset.sup'_le
    intro k hk
    have ht : phaseEnergy U (unadjustedPath (gradient U) h r σ
        (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k) ≤ s := by
      apply le_of_not_gt
      intro hs
      exact hb ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), hs⟩
    simp only [hstar, hzero, sub_zero]
    unfold phaseEnergy at ht
    rw [real_inner_self_eq_norm_sq] at ht
    nlinarith [sq_nonneg (‖(unadjustedPath (gradient U) h r σ
      (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k).2‖)]
  unfold rejectionBudget
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hp (by have := a.L_pos.le; positivity)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => remainder_le_cubic_flight a a2 hh r σ n k z b

theorem stopped_cubic_budget_lintegral
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar n z,
      ENNReal.ofReal (LH*h^3/12 * ∑ k ∈ Finset.range n,
        ‖stepFlight (gradient U) h r σ n k z b‖^3) ∂gaussianBlock n) ≤
      ENNReal.ofReal ((n:ℝ)*(LH*h^3/12)*((6.6:ℝ)*Q)^(3/2:ℝ)) := by
  dsimp only
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hc : 0 ≤ LH*h^3/12 := by positivity
  have hsum (b : NoiseBlock E n) :
      ENNReal.ofReal (∑ k ∈ Finset.range n,
        ‖stepFlight (gradient U) h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) n k z b‖^3) =
      ∑ k ∈ Finset.range n, ENNReal.ofReal
        (‖stepFlight (gradient U) h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) n k z b‖^3) :=
    ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)
  simp_rw [ENNReal.ofReal_mul hc, hsum]
  have hm (k : ℕ) : Measurable (fun b : NoiseBlock E n => ENNReal.ofReal
      (‖stepFlight (gradient U) h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) n k z b‖^3)) :=
    ENNReal.measurable_ofReal.comp ((measurable_stepFlight (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) n k z).norm.pow_const 3)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ (fun k _ => hm k)]
  calc
    _ ≤ ENNReal.ofReal (LH*h^3/12) * ∑ _k ∈ Finset.range n,
        ENNReal.ofReal (((6.6:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50))^(3/2:ℝ)) := by
      gcongr with k hk
      exact stopped_stepFlight_third_lintegral a a2 hstar hzero hh hL hv hLH hscale hR z hz
        (Finset.mem_range.mp hk)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ← ENNReal.ofReal_mul hc]
      congr 1
      ring

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stopped_cubic_budget_lintegral
