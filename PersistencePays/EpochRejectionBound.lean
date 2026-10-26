import PersistencePays.EpochKernel
import PersistencePays.Assumptions

/-!
# Proposition 5.1: the clipped expected rejection bound

The probability formula is connected to the signed telescoping energy error
and the actual potential bound. The clipped integrands are bounded, so this
step needs no unproved moment or integrability hypothesis.
-/

noncomputable section
namespace PersistencePays.OBABOPath

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def potentialPeak (U : E → ℝ) (Ustar : ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (z : E × E) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
    (fun k => U (unadjustedPath g h r σ ξ ξ' z k).1 - Ustar)

def rejectionBudget (U : E → ℝ) (Ustar L : ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (z : E × E) (n : ℕ) : ℝ :=
  (h ^ 2 * L / 4) * potentialPeak U Ustar g h r σ ξ ξ' z n +
    ∑ k ∈ Finset.range n, |remainder U g h r σ ξ k (unadjustedPath g h r σ ξ ξ' z k)|

theorem potential_le_peak
    (U : E → ℝ) (Ustar : ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (z : E × E) (n k : ℕ) (hk : k ≤ n) :
    U (unadjustedPath g h r σ ξ ξ' z k).1 - Ustar ≤
      potentialPeak U Ustar g h r σ ξ ξ' z n := by
  unfold potentialPeak
  exact Finset.le_sup' (s := Finset.range (n + 1))
    (fun j => U (unadjustedPath g h r σ ξ ξ' z j).1 - Ustar)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem rejectionBudget_nonnegative {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (ξ ξ' : ℕ → E) (z : E × E) (n : ℕ) :
    0 ≤ rejectionBudget U (U a.minimizer) L (gradient U) h r σ ξ ξ' z n := by
  have hpeak : 0 ≤ potentialPeak U (U a.minimizer) (gradient U) h r σ ξ ξ' z n :=
    (sub_nonneg.mpr (a.minimizer_le _)).trans
      (potential_le_peak U (U a.minimizer) (gradient U) h r σ ξ ξ' z n 0 (Nat.zero_le n))
  unfold rejectionBudget
  have hL := a.L_pos.le
  positivity

theorem work_le_rejectionBudget {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (ξ ξ' : ℕ → E) (z : E × E) (n k : ℕ) (hk : k ≤ n) :
    work U (gradient U) h r σ ξ ξ' z k ≤
      rejectionBudget U (U a.minimizer) L (gradient U) h r σ ξ ξ' z n := by
  have hG0 : 0 ≤ gradientCorrection (gradient U) h z.1 := by
    rw [gradientCorrection_eq_norm]
    positivity
  have hw := EpochAcceptance.accumulatedWork_le_corrector_add_abs_remainder
    (acceptedUpdate (gradient U) h r σ ξ ξ') (energyDefect U (gradient U) h r σ ξ)
    (remainder U (gradient U) h r σ ξ)
    (fun p => gradientCorrection (gradient U) h p.1) z
    (energyDefect_eq_correction_difference U (gradient U) h r σ ξ ξ') hG0 k
  have hG := (lemma_2_1_A1 (h := h) a (unadjustedPath (gradient U) h r σ ξ ξ' z k)).2.2.2
  have hpot := potential_le_peak U (U a.minimizer) (gradient U) h r σ ξ ξ' z n k hk
  have hcoef : 0 ≤ h ^ 2 * L / 4 := by have hL := a.L_pos.le; positivity
  have hs : (∑ j ∈ Finset.range k,
      |remainder U (gradient U) h r σ ξ j (unadjustedPath (gradient U) h r σ ξ ξ' z j)|) ≤
      ∑ j ∈ Finset.range n,
      |remainder U (gradient U) h r σ ξ j (unadjustedPath (gradient U) h r σ ξ ξ' z j)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (by intros; positivity)
  exact hw.trans (add_le_add (hG.trans (mul_le_mul_of_nonneg_left hpot hcoef)) hs)

theorem peak_le_rejectionBudget {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (ξ ξ' : ℕ → E) (z : E × E) (n : ℕ) (hn : 0 < n) :
    peak U (gradient U) h r σ ξ ξ' z n hn ≤
      rejectionBudget U (U a.minimizer) L (gradient U) h r σ ξ ξ' z n := by
  unfold peak EpochAcceptance.peakWork
  apply Finset.sup'_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
  intro k hk
  exact work_le_rejectionBudget a h r σ ξ ξ' z n (k + 1)
    (by simpa only [Finset.mem_range, Nat.succ_le_iff] using hk)

theorem exponential_loss_nonnegative (s : ℝ) : 0 ≤ 1 - Real.exp (-max s 0) := by
  have he : Real.exp (-max s 0) ≤ 1 := Real.exp_le_one_iff.mpr (by simp)
  linarith

theorem exponential_loss_le (s b : ℝ) (hb : 0 ≤ b) (hs : s ≤ b) :
    1 - Real.exp (-max s 0) ≤ min 1 b := by
  apply le_min
  · linarith [Real.exp_pos (-max s 0)]
  · have hm : max s 0 ≤ b := max_le hs hb
    have he := Real.add_one_le_exp (-max s 0)
    linarith

theorem measurable_rejectionBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (U : E → ℝ) (hU : Measurable U) (Ustar L : ℝ)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (ξ ξ' : ℕ → Ω → E) (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : E × E) (n : ℕ) :
    Measurable (fun ω => rejectionBudget U Ustar L g h r σ
      (fun k => ξ k ω) (fun k => ξ' k ω) z n) := by
  have hp (k : ℕ) := measurable_unadjustedPath g hg h r σ ξ ξ' hξ hξ' z k
  have hpeak : Measurable (fun ω => potentialPeak U Ustar g h r σ
      (fun k => ξ k ω) (fun k => ξ' k ω) z n) := by
    have hm := Finset.measurable_sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
      (fun k _ => (hU.comp (hp k).fst).sub_const Ustar)
    convert hm using 1
    ext ω
    simp [potentialPeak]
  have hsum : Measurable (fun ω => ∑ k ∈ Finset.range n,
      |remainder U g h r σ (fun j => ξ j ω) k
        (unadjustedPath g h r σ (fun j => ξ j ω) (fun j => ξ' j ω) z k)|) := by
    apply Finset.measurable_sum
    intro k hk
    dsimp only [remainder, trapezoidDefect, ou, verlet, kick, drift]
    fun_prop
  exact (measurable_const.mul hpeak).add hsum

theorem integrable_unit_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ω)] using h1 ω

/-- Proposition 5.1's full expectation inequality with the actual Gaussian
block, actual gradient, and the minimizer constructed from (A1). -/
theorem gaussian_epoch_rejection_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (z : E × E) (n : ℕ) (hn : 0 < n) :
    (epochRandomness (E := E) n).real
      {p | ¬ everyMoveAccepted U (gradient U) h r σ
        (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n} ≤
      ∫ b, min 1 (rejectionBudget U (U a.minimizer) L (gradient U) h r σ
        (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n) ∂gaussianBlock n := by
  have hU := a.twice_contDiff.continuous.measurable
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  rw [gaussian_epoch_rejection_probability U hU (gradient U) hg h r σ z n hn]
  have hp := measurable_peak U hU (gradient U) hg h r σ (firstNoise n) (secondNoise n)
    (measurable_firstNoise n) (measurable_secondNoise n) z n hn
  have hb := measurable_rejectionBudget U hU (U a.minimizer) L (gradient U) hg h r σ
    (firstNoise n) (secondNoise n) (measurable_firstNoise n) (measurable_secondNoise n) z n
  apply integral_mono
  · apply integrable_unit_bounded (gaussianBlock n)
    · exact measurable_const.sub ((hp.max measurable_const).neg.exp)
    · intro b; exact exponential_loss_nonnegative _
    · intro b
      exact (exponential_loss_le _ _
        (rejectionBudget_nonnegative a h r σ _ _ z n)
        (peak_le_rejectionBudget a h r σ _ _ z n hn)).trans (min_le_left _ _)
  · apply integrable_unit_bounded (gaussianBlock n) _ (measurable_const.min hb)
    · intro b; exact le_min (by norm_num) (rejectionBudget_nonnegative a h r σ _ _ z n)
    · intro b; exact min_le_left _ _
  · intro b
    exact exponential_loss_le _ _ (rejectionBudget_nonnegative a h r σ _ _ z n)
      (peak_le_rejectionBudget a h r σ _ _ z n hn)

end PersistencePays.OBABOPath

#print axioms PersistencePays.OBABOPath.gaussian_epoch_rejection_bound
