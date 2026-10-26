import PersistencePays.StoppedRejection

/-! Rejection in Proposition 6.1: actual finite paths, thresholds, and all
exceptional events are integrated on the original probability space. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stopped_rejection_bound
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (hn : 0 < n) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    let R'' := (1.27:ℝ)*(Q0+20*Real.log (100*((n:ℝ)+1)))
    (epochRandomness (E:=E) n)
      {p | ¬ everyMoveAccepted U (gradient U) h r σ
        (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n} ≤
      2 * gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ +
        ENNReal.ofReal (0.01:ℝ) + ENNReal.ofReal (h^2*L/4*R'') +
        ENNReal.ofReal ((n:ℝ)*(LH*h^3/12)*((6.6:ℝ)*(Q0+50))^(3/2:ℝ)) := by
  dsimp only
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
  let R'' := (1.27:ℝ)*(Q0+20*Real.log (100*((n:ℝ)+1)))
  let B := stoppedBlockEvent U (gradient U) h r σ vstar n z
  let M := maximalEnergyEvent U (gradient U) h r σ n z R''
  let f : NoiseBlock E n → ℝ := fun b =>
    rejectionBudget U (U a.minimizer) L (gradient U) h r σ
      (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n
  let g : NoiseBlock E n → ℝ := fun b => LH*h^3/12 * ∑ k ∈ Finset.range n,
    ‖stepFlight (gradient U) h r σ n k z b‖^3
  have hU := a.twice_contDiff.continuous.measurable
  have hgrad := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hf : Measurable f := measurable_rejectionBudget U hU (U a.minimizer) L
    (gradient U) hgrad h r σ (firstNoise n) (secondNoise n)
    (measurable_firstNoise n) (measurable_secondNoise n) z n
  have hf0 (b : NoiseBlock E n) : 0 ≤ f b := rejectionBudget_nonnegative a h r σ _ _ z n
  have hfi : Integrable (fun b => min 1 (f b)) (gaussianBlock n) :=
    integrable_unit_bounded (gaussianBlock n) _ (measurable_const.min hf)
      (fun b => le_min (by norm_num) (hf0 b)) (fun _ => min_le_left _ _)
  have hc : 0 ≤ h^2*L/4*R'' := by
    have hl : 0 ≤ Real.log (100*((n:ℝ)+1)) := Real.log_nonneg (by
      have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); nlinarith)
    have hpos := a.L_pos.le
    dsimp [R'', Q0]
    positivity
  have hb := clipped_budget_lintegral (gaussianBlock n) B M
    (stoppedBlockEvent_measurable a h r σ vstar n z)
    (maximalEnergyEvent_measurable a h r σ n z R'') f g (h^2*L/4*R'') hc
    (fun b _ hb => rejectionBudget_le_on_energy a a2 hh hstar hzero r σ n z R'' b hb)
    (fun _ => by dsimp [g]; positivity)
  have htail := stopped_path_maximal_energy_threshold a a2 hstar hzero hh hL hv hLH
    hscale hR z hz n
  have hcubic := stopped_cubic_budget_lintegral a a2 hstar hzero hh hL hv hLH
    hscale hR z hz n
  calc
    _ = ENNReal.ofReal ((epochRandomness (E:=E) n).real
        {p | ¬ everyMoveAccepted U (gradient U) h r σ
          (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n}) :=
      (ENNReal.ofReal_toReal (by finiteness)).symm
    _ ≤ ENNReal.ofReal (∫ b, min 1 (f b) ∂gaussianBlock n) :=
      ENNReal.ofReal_le_ofReal (gaussian_epoch_rejection_bound a h r σ z n hn)
    _ = ∫⁻ b, ENNReal.ofReal (min 1 (f b)) ∂gaussianBlock n :=
      ofReal_integral_eq_lintegral_ofReal hfi
        (Filter.Eventually.of_forall fun b => le_min (by norm_num) (hf0 b))
    _ ≤ gaussianBlock n Bᶜ + gaussianBlock n M + ENNReal.ofReal (h^2*L/4*R'') +
        ∫⁻ b in B, ENNReal.ofReal (g b) ∂gaussianBlock n := hb
    _ ≤ gaussianBlock n Bᶜ + (gaussianBlock n Bᶜ + ENNReal.ofReal (0.01:ℝ)) +
        ENNReal.ofReal (h^2*L/4*R'') +
        ENNReal.ofReal ((n:ℝ)*(LH*h^3/12)*((6.6:ℝ)*(Q0+50))^(3/2:ℝ)) :=
      add_le_add (add_le_add (add_le_add le_rfl htail) le_rfl) hcubic
    _ = _ := by change _ = 2*gaussianBlock n Bᶜ + _ + _ + _; ring

theorem rejection_numeric_budget {L LH h R : ℝ} (hLpos : 0 ≤ L)
    (hLH : 0 ≤ LH) (hh : 0 ≤ h) (d n : ℕ)
    (hQ : 0 ≤ (1.2:ℝ)*R+27*(d:ℝ)+50)
    (ha : h^2*L*((1.2:ℝ)*R+27*(d:ℝ)+50+20*Real.log (100*((n:ℝ)+1))) ≤ 1/5000)
    (hb : LH*h^2*((6.6:ℝ)*((1.2:ℝ)*R+27*(d:ℝ)+50))^(3/2:ℝ)*(1+(n:ℝ)*h) ≤ 1/1000) :
    h^2*L/4*((1.27:ℝ)*((1.2:ℝ)*R+27*(d:ℝ)+20*Real.log (100*((n:ℝ)+1)))) ≤ 1.27/(4*5000) ∧
    (n:ℝ)*(LH*h^3/12)*((6.6:ℝ)*((1.2:ℝ)*R+27*(d:ℝ)+50))^(3/2:ℝ) ≤ 1/12000 := by
  constructor
  · have hc : 0 ≤ h^2*L := mul_nonneg (sq_nonneg h) hLpos
    nlinarith
  · have hc : 0 ≤ LH*h^2*((6.6:ℝ)*((1.2:ℝ)*R+27*(d:ℝ)+50))^(3/2:ℝ) := by positivity
    nlinarith

/-- The rejection conclusion used in Proposition 6.1. The explicit small-exit
hypothesis is proved from condition (d) separately. -/
theorem proposition_6_1_rejection
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (hn : 0 < n)
    (ha : h^2*L*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50+
        20*Real.log (100*((n:ℝ)+1))) ≤ 1/5000)
    (hb : LH*h^2*((6.6:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50))^(3/2:ℝ)*
        (1+(n:ℝ)*h) ≤ 1/1000)
    (hexit : gaussianBlock n (stoppedBlockEvent U (gradient U) h (Real.exp (-h))
        (Real.sqrt (1-Real.exp (-2*h))) vstar n z)ᶜ ≤ ENNReal.ofReal (1/100000:ℝ)) :
    (epochRandomness (E:=E) n).real
      {p | ¬ everyMoveAccepted U (gradient U) h (Real.exp (-h))
        (Real.sqrt (1-Real.exp (-2*h)))
        (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n} ≤ (0.0102:ℝ) := by
  obtain ⟨hc₁, hc₂⟩ := rejection_numeric_budget a.L_pos.le hLH hh (Module.finrank ℝ E) n
    (by positivity) ha hb
  have ht := stopped_rejection_bound a a2 hstar hzero hh hL hv hLH hscale hR z hz n hn
  have ht' : (epochRandomness (E:=E) n)
      {p | ¬ everyMoveAccepted U (gradient U) h (Real.exp (-h))
        (Real.sqrt (1-Real.exp (-2*h)))
        (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n} ≤
        ENNReal.ofReal (0.0102:ℝ) := by
    apply ht.trans
    calc
      _ ≤ 2*ENNReal.ofReal (1/100000:ℝ) + ENNReal.ofReal (0.01:ℝ) +
          ENNReal.ofReal (1.27/(4*5000):ℝ) + ENNReal.ofReal (1/12000:ℝ) := by
        gcongr
      _ ≤ _ := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
  have ht'' := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht'
  simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 0.0102)] using ht''

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stopped_rejection_bound
#print axioms PersistencePays.OBABOPath.proposition_6_1_rejection
