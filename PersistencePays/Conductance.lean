import PersistencePays.WarmStart
import PersistencePays.CouplingTV

/-! The stationary one-step crossing reduction, without reversibility or
independence assumptions on later states. -/

namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]

noncomputable def stationaryFlow (K : Kernel S S) (π : Measure S) (A : Set S) : ℝ≥0∞ :=
  ∫⁻ x in A, K x Aᶜ ∂π

/-- One-step escape probability is bounded by the mass already outside plus
the stationary outward flow multiplied by the density cap. -/
theorem crossing_step_bound (K : Kernel S S) [IsMarkovKernel K]
    (π μ : Measure S) (c : ℝ≥0∞) (hμ : μ ≤ c • π)
    (A : Set S) (hA : MeasurableSet A) :
    (K ∘ₘ μ) Aᶜ ≤ μ Aᶜ + c * stationaryFlow K π A := by
  rw [Measure.bind_apply hA.compl K.aemeasurable,
    ← lintegral_add_compl (fun x => K x Aᶜ) hA]
  have hleft : (∫⁻ x in A, K x Aᶜ ∂μ) ≤ c * stationaryFlow K π A := by
    calc
      (∫⁻ x in A, K x Aᶜ ∂μ) ≤ ∫⁻ x in A, K x Aᶜ ∂(c • π) :=
        lintegral_mono' (Measure.restrict_mono_measure hμ A) le_rfl
      _ = _ := by simp [stationaryFlow, Measure.restrict_smul, lintegral_smul_measure]
  have hright : (∫⁻ x in Aᶜ, K x Aᶜ ∂μ) ≤ μ Aᶜ := by
    calc
      (∫⁻ x in Aᶜ, K x Aᶜ ∂μ) ≤ ∫⁻ _ in Aᶜ, 1 ∂μ :=
        lintegral_mono (fun _ => prob_le_one)
      _ = _ := by simp
  simpa [add_comm] using add_le_add hleft hright

/-- The stationary crossing bound applies at every time because invariance
propagates the initial density cap. The kernels may vary with time. -/
theorem crossing_evolve_bound (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (π μ : Measure S) (hinv : ∀ n, K n ∘ₘ π = π)
    (c q : ℝ≥0∞) (hμ : μ ≤ c • π)
    (A : Set S) (hA : MeasurableSet A) (hstart : μ Aᶜ = 0)
    (hflow : ∀ j, stationaryFlow (K j) π A ≤ q) (n : ℕ) :
    evolve K μ n Aᶜ ≤ (n : ℝ≥0∞) * c * q := by
  induction n with
  | zero => simp [hstart]
  | succ n ih =>
    calc
      evolve K μ (n + 1) Aᶜ ≤ evolve K μ n Aᶜ + c * stationaryFlow (K n) π A :=
        crossing_step_bound (K n) π _ c (evolve_warm_bound K π hinv μ c hμ n) A hA
      _ ≤ (n : ℝ≥0∞) * c * q + c * q :=
        add_le_add ih (by simpa [mul_comm] using mul_le_mul_left (hflow n) c)
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * c * q := by push_cast; ring

/-- A lower bound for position TV needs only a position event; it does not
require the position projection itself to be a Markov chain. -/
theorem observation_probabilityTV_lower {T : Type*} [MeasurableSpace T]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : S → T) (hf : Measurable f) (B : Set T) (hB : MeasurableSet B) :
    ENNReal.ofReal (π.real (f ⁻¹' B) - μ.real (f ⁻¹' B)) ≤
      probabilityTV (μ.map f) (π.map f) := by
  calc
    ENNReal.ofReal (π.real (f ⁻¹' B) - μ.real (f ⁻¹' B))
      ≤ ENNReal.ofReal |μ.real (f ⁻¹' B) - π.real (f ⁻¹' B)| := by
        apply ENNReal.ofReal_le_ofReal
        rw [abs_sub_comm]
        exact le_abs_self _
    _ = ENNReal.ofReal |(μ.map f).real B - (π.map f).real B| := by
      simp only [Measure.real, Measure.map_apply hf hB]
    _ ≤ _ := by
      unfold probabilityTV
      exact le_iSup₂_of_le B hB le_rfl

/-- The half-mass test set gives strict TV separation when the escape mass
is strictly below one quarter, including for a non-Markovian observation. -/
theorem observation_probabilityTV_gt_quarter {T : Type*} [MeasurableSpace T]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : S → T) (hf : Measurable f) (B : Set T) (hB : MeasurableSet B)
    (hπ : π (f ⁻¹' B) = (1 / 2 : ℝ≥0∞)) (hμ : μ (f ⁻¹' B) < (1 / 4 : ℝ≥0∞)) :
    (1 / 4 : ℝ≥0∞) < probabilityTV (μ.map f) (π.map f) := by
  have hπr : π.real (f ⁻¹' B) = (1 / 2 : ℝ) := by simp [Measure.real, hπ]
  have hμr : μ.real (f ⁻¹' B) < (1 / 4 : ℝ) := by
    have hh := ENNReal.toReal_strict_mono (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ∞) hμ
    simpa only [Measure.real, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hh
  have hd : (1 / 4 : ℝ) < π.real (f ⁻¹' B) - μ.real (f ⁻¹' B) := by linarith
  have he : (1 / 4 : ℝ≥0∞) < ENNReal.ofReal (π.real (f ⁻¹' B) - μ.real (f ⁻¹' B)) := by
    have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hd
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hh
  exact he.trans_le (observation_probabilityTV_lower μ π f hf B hB)

theorem half_conditioned_probability (π : Measure S) [IsProbabilityMeasure π]
    (A : Set S) (hπA : π A = (1 / 2 : ℝ≥0∞)) :
    IsProbabilityMeasure ((2 : ℝ≥0∞) • π.restrict A) := by
  constructor
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, hπA, smul_eq_mul, one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem half_conditioned_outside (π : Measure S) (A : Set S) (hA : MeasurableSet A) :
    ((2 : ℝ≥0∞) • π.restrict A) Aᶜ = 0 := by
  rw [Measure.smul_apply, Measure.restrict_apply hA.compl]
  simp

/-- Complete conductance reduction for a half-space-conditioned warm start.
Only the one-step stationary flow estimate remains to be specialized. -/
theorem half_conditioned_observation_TV_gt_quarter
    {T : Type*} [MeasurableSpace T]
    (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (π : Measure S) [IsProbabilityMeasure π] (hinv : ∀ n, K n ∘ₘ π = π)
    (f : S → T) (hf : Measurable f) (B : Set T) (hB : MeasurableSet B)
    (hπB : π (f ⁻¹' B) = (1 / 2 : ℝ≥0∞))
    (q : ℝ≥0∞) (hflow : ∀ j, stationaryFlow (K j) π (f ⁻¹' B) ≤ q)
    (n : ℕ) (hn : (n : ℝ≥0∞) * 2 * q < 1 / 4) :
    (1 / 4 : ℝ≥0∞) <
      probabilityTV ((evolve K ((2 : ℝ≥0∞) • π.restrict (f ⁻¹' B)) n).map f) (π.map f) := by
  let ν : Measure S := (2 : ℝ≥0∞) • π.restrict (f ⁻¹' B)
  let : IsProbabilityMeasure ν := half_conditioned_probability π (f ⁻¹' B) hπB
  have hν : ν ≤ (2 : ℝ≥0∞) • π := smul_le_smul_left _ Measure.restrict_le_self
  have hcross := crossing_evolve_bound K π ν hinv 2 q hν (f ⁻¹' B) (hf hB)
    (half_conditioned_outside π (f ⁻¹' B) (hf hB)) hflow n
  apply observation_probabilityTV_gt_quarter (evolve K ν n) π f hf Bᶜ hB.compl
  · rw [Set.preimage_compl, measure_compl (hf hB) (measure_ne_top _ _), hπB]
    norm_num
  · simpa only [Set.preimage_compl] using hcross.trans_lt hn

end PersistencePays

#print axioms PersistencePays.crossing_evolve_bound
#print axioms PersistencePays.observation_probabilityTV_lower
#print axioms PersistencePays.half_conditioned_observation_TV_gt_quarter
