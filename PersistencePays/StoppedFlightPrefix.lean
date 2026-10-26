import PersistencePays.StoppedFlightPath

/-! Prefix consistency and stopped velocity moments on a single full noise block. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def prefixBlock {k n : ℕ} (hk : k ≤ n) (b : NoiseBlock E n) : NoiseBlock E k :=
  (FiniteNoise.prefixNoise hk b.1, FiniteNoise.prefixNoise hk b.2)

theorem prefixBlock_preserving {k n : ℕ} (hk : k ≤ n) :
    MeasurePreserving (prefixBlock (E:=E) hk) (gaussianBlock n) (gaussianBlock k) := by
  exact (FiniteNoise.prefixNoise_preserving (stdGaussian E) hk).prod
    (FiniteNoise.prefixNoise_preserving (stdGaussian E) hk)

theorem zipNoise_prefixBlock {k n : ℕ} (hk : k ≤ n) (b : NoiseBlock E n) :
    zipNoise k (prefixBlock hk b) = FiniteNoise.prefixNoise hk (zipNoise n b) := rfl

theorem unadjustedPath_prefixBlock (g : E → E) (h r σ : ℝ)
    {k n j : ℕ} (hk : k ≤ n) (hj : j ≤ k) (z : E×E) (b : NoiseBlock E n) :
    unadjustedPath g h r σ (fun i => firstNoise k i (prefixBlock hk b))
      (fun i => secondNoise k i (prefixBlock hk b)) z j =
    unadjustedPath g h r σ (fun i => firstNoise n i b) (fun i => secondNoise n i b) z j := by
  rw [← prefix_trajectory_eq_unadjustedPath g h r σ hj,
    ← prefix_trajectory_eq_unadjustedPath g h r σ (hj.trans hk), zipNoise_prefixBlock]
  rfl

theorem stoppedBlockEvent_prefix (U : E → ℝ) (g : E → E) (h r σ vstar : ℝ)
    {k n : ℕ} (hk : k ≤ n) (z : E×E) :
    stoppedBlockEvent U g h r σ vstar n z ⊆
      prefixBlock hk ⁻¹' stoppedBlockEvent U g h r σ vstar k z := by
  intro b hb
  rw [stoppedBlockEvent_eq] at hb ⊢
  change zipNoise k (prefixBlock hk b) ∈
    FiniteNoise.goodBlock (unadjustedStepWithNoise g h r σ) (stoppedOBABOGood U σ vstar) k z
  rw [zipNoise_prefixBlock]
  exact FiniteNoise.goodBlock_prefix _ _ hk z (zipNoise n b) hb

theorem prefixBlock_stopped_lintegral_le {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) {k n : ℕ} (hk : k ≤ n) (z : E×E)
    (F : NoiseBlock E k → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar n z,
      F (prefixBlock hk b) ∂gaussianBlock n) ≤
    ∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar k z, F b ∂gaussianBlock k := by
  calc
    _ ≤ ∫⁻ b in prefixBlock hk ⁻¹' stoppedBlockEvent U (gradient U) h r σ vstar k z,
        F (prefixBlock hk b) ∂gaussianBlock n :=
      lintegral_mono' (Measure.restrict_mono
        (stoppedBlockEvent_prefix U (gradient U) h r σ vstar hk z) le_rfl) le_rfl
    _ = _ := by
      rw [← lintegral_map hF (prefixBlock_preserving hk).measurable,
        ← Measure.restrict_map (prefixBlock_preserving hk).measurable
          (stoppedBlockEvent_measurable a h r σ vstar k z),
        (prefixBlock_preserving hk).map_eq]

def stepFlight (g : E → E) (h r σ : ℝ) (n k : ℕ) (z : E×E) (b : NoiseBlock E n) : E :=
  flightVelocity g h (ou r σ (firstNoise n k b)
    (unadjustedPath g h r σ (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k))

theorem stepFlight_eq_lastFlight (g : E → E) (h r σ : ℝ) {n k : ℕ}
    (hk : k < n) (z : E×E) (b : NoiseBlock E n) :
    stepFlight g h r σ n k z b =
      lastFlight g h r σ k z (prefixBlock (Nat.succ_le_of_lt hk) b) := by
  unfold stepFlight lastFlight
  rw [unadjustedPath_prefixBlock g h r σ _ (Nat.le_succ k)]
  simp [firstNoise, prefixBlock, FiniteNoise.prefixNoise, hk]

theorem measurable_stepFlight (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (n k : ℕ) (z : E×E) : Measurable (stepFlight g h r σ n k z) := by
  have hp := measurable_unadjustedPath g hg h r σ (firstNoise n) (secondNoise n)
    (measurable_firstNoise n) (measurable_secondNoise n) z k
  have hξ := measurable_firstNoise (E:=E) n k
  unfold stepFlight flightVelocity ou
  fun_prop

theorem stopped_stepFlight_third_lintegral
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R)
    {n k : ℕ} (hk : k < n) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar n z,
      ENNReal.ofReal (‖stepFlight (gradient U) h r σ n k z b‖^3) ∂gaussianBlock n) ≤
        ENNReal.ofReal (((6.6:ℝ)*Q)^(3/2:ℝ)) := by
  dsimp only
  simp_rw [stepFlight_eq_lastFlight (gradient U) _ _ _ hk]
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  exact (prefixBlock_stopped_lintegral_le a _ _ _ _ (Nat.succ_le_of_lt hk) z
    (fun b => ENNReal.ofReal (‖lastFlight (gradient U) h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) k z b‖^3))
    (ENNReal.measurable_ofReal.comp
      ((measurable_lastFlight (gradient U) hg _ _ _ k z).norm.pow_const 3))).trans
      (stopped_lastFlight_third_lintegral a a2 hstar hzero hh hL hv hLH hscale hR z hz k)

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stopped_stepFlight_third_lintegral
