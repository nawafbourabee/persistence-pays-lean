import PersistencePays.StoppedKernel
import PersistencePays.LyapunovDrift
import PersistencePays.StoppedMomentConversion

/-! The stopped OBABO kernel and its uniform exponential moment. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def stoppedOBABOGood (U : E → ℝ) (σ vstar : ℝ) : Set ((E × E) × (E × E)) :=
  {p | phaseEnergy U p.1 ≤ vstar^2/32 ∧ ‖σ • p.2.1‖ ≤ vstar/2}

theorem stoppedOBABOGood_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (σ vstar : ℝ) : MeasurableSet (stoppedOBABOGood U σ vstar) := by
  have hU := a.twice_contDiff.continuous.measurable
  have hH : Measurable (fun p : (E × E) × (E × E) => phaseEnergy U p.1) := by
    unfold phaseEnergy
    fun_prop
  have hN : Measurable (fun p : (E × E) × (E × E) => ‖σ • p.2.1‖) := by fun_prop
  exact (measurableSet_le hH measurable_const).inter
    (measurableSet_le hN measurable_const)

theorem unadjustedNoiseStep_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ : ℝ) : Measurable (fun p : (E × E) × (E × E) =>
      unadjustedNoiseStep U h r σ p.1 p.2) := by
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  unfold unadjustedNoiseStep OBABOPath.ou verlet kick drift
  fun_prop

theorem lyapunov_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L) (h : ℝ) :
    Measurable (lyapunov U h) := by
  have hU := a.twice_contDiff.continuous.measurable
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  unfold lyapunov modifiedEnergy phaseEnergy gradientCorrection
  fun_prop

def stoppedOBABOKernel {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) : Kernel (E × E) (E × E) :=
  stoppedNoiseKernel ((stdGaussian E).prod (stdGaussian E))
    (fun p => unadjustedNoiseStep U h r σ p.1 p.2)
    (stoppedOBABOGood U σ vstar) (stoppedOBABOGood_measurable a σ vstar)

theorem stoppedOBABOKernel_mass_le_one {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (z : E × E) :
    stoppedOBABOKernel a h r σ vstar z univ ≤ 1 :=
  stoppedNoiseKernel_mass_le_one _ _ (unadjustedNoiseStep_measurable a h r σ) _ _ z

theorem stoppedOBABOKernel_mass {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (z : E × E) :
    stoppedOBABOKernel a h r σ vstar z univ =
      if phaseEnergy U z ≤ vstar^2/32 then
        stdGaussian E {ξ | ‖σ•ξ‖ ≤ vstar/2} else 0 := by
  have hf : Measurable (fun η : E × E => unadjustedNoiseStep U h r σ z η) :=
    (unadjustedNoiseStep_measurable a h r σ).comp (measurable_const.prodMk measurable_id)
  rw [stoppedOBABOKernel, stoppedNoiseKernel_apply _ _
    (unadjustedNoiseStep_measurable a h r σ), Measure.map_apply hf MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  split_ifs with hz
  · have he : {η : E × E | (z,η) ∈ stoppedOBABOGood U σ vstar} =
        {ξ : E | ‖σ•ξ‖ ≤ vstar/2} ×ˢ univ := by
      ext η
      simp [stoppedOBABOGood, hz]
    rw [he, Measure.prod_prod]
    simp
  · have he : {η : E × E | (z,η) ∈ stoppedOBABOGood U σ vstar} = ∅ := by
      ext η
      simp [stoppedOBABOGood, hz]
    simp [he]

theorem stoppedOBABOKernel_loss {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (z : E × E) :
    1-stoppedOBABOKernel a h r σ vstar z univ ≤
      {w : E × E | vstar^2/32 < phaseEnergy U w}.indicator (fun _ => 1) z+
        stdGaussian E {ξ | vstar/2 < ‖σ•ξ‖} := by
  have hG : MeasurableSet {ξ : E | ‖σ•ξ‖ ≤ vstar/2} :=
    measurableSet_le (measurable_id.const_smul σ).norm measurable_const
  rw [stoppedOBABOKernel_mass]
  split_ifs with hz
  · have hc : {ξ : E | vstar/2 < ‖σ•ξ‖} = {ξ : E | ‖σ•ξ‖ ≤ vstar/2}ᶜ := by
      ext ξ
      simp
    rw [hc, measure_compl hG (measure_ne_top _ _), measure_univ]
    simp [Set.indicator, not_lt.mpr hz]
  · simp [Set.indicator, lt_of_not_ge hz]

theorem stoppedOBABOKernel_exp {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (z : E × E) :
    (∫⁻ w, ENNReal.ofReal (Real.exp ((1/20:ℝ)*lyapunov U h w))
      ∂stoppedOBABOKernel a h r σ vstar z) =
    if phaseEnergy U z ≤ vstar^2/32 then
      ∫⁻ η, ENNReal.ofReal (stoppedLyapunovExp U h r σ vstar z η)
        ∂(stdGaussian E).prod (stdGaussian E) else 0 := by
  have hG : MeasurableSet {η : E × E | (z,η) ∈ stoppedOBABOGood U σ vstar} :=
    (stoppedOBABOGood_measurable a σ vstar).preimage
      (measurable_const.prodMk measurable_id)
  rw [stoppedOBABOKernel, stoppedNoiseKernel_lintegral _ _
    (unadjustedNoiseStep_measurable a h r σ) _ _ _ _
    (((lyapunov_measurable a h).const_mul (1/20:ℝ)).exp.ennreal_ofReal),
    ← lintegral_indicator hG]
  split_ifs with hz
  · apply lintegral_congr
    intro η
    by_cases hη : ‖σ•η.1‖ ≤ vstar/2
    · simp [stoppedOBABOGood, hz, hη, stoppedLyapunovExp]
    · simp [stoppedOBABOGood, hz, hη, stoppedLyapunovExp]
  · have he : {η : E × E | (z,η) ∈ stoppedOBABOGood U σ vstar} = ∅ := by
      ext η
      simp [stoppedOBABOGood, hz]
    simp [he]

/-- Lemma 5.6(i) for the literal killed OBABO kernel.  The path-law identity
with `B_k` is established separately, so no stochastic recurrence is assumed. -/
theorem stoppedOBABO_exponential_moment
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    (∫⁻ w, ENNReal.ofReal (Real.exp ((1/20:ℝ)*lyapunov U h w))
      ∂iterateKernel (stoppedOBABOKernel a h r σ vstar) n z) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*Q0)) := by
  dsimp only
  have hhmax : h ≤ 1/8 := by
    have := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith

  obtain ⟨hrpos, hr, hspos, hnorm, hrh, hrsq, _, hσ⟩ := normalized_ou_coefficients h hh
  have hrnorm : (Real.exp (-h))^2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt (1-Real.exp (-2*h)))]
  apply iterateKernel_exponential_bound _ (stoppedOBABOKernel_mass_le_one a h _ _ vstar)
    (fun w => (1/20:ℝ)*lyapunov U h w) ((lyapunov_measurable a h).const_mul _)
    (a := (0.076:ℝ)*h)
    (b := (2.04:ℝ)*(1/20:ℝ)*h*(Module.finrank ℝ E : ℝ))
    (by positivity) (by nlinarith) _ _ z _ n
  · have hd : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    nlinarith [mul_nonneg hh hR, mul_nonneg hh hd]
  · intro w
    rw [stoppedOBABOKernel_exp]
    split_ifs with hw
    · convert lyapunov_drift_lintegral a a2 hstar hzero hh hhmax hL hr hrh hrsq
        hrnorm hσ hv hLH hscale w hw using 1 <;> congr 2 <;> ring
    · exact bot_le
  · have hb := (lyapunov_energy_bounds a hstar hzero hL z).2.1
    have hd : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    nlinarith

theorem stoppedOBABO_energy_tail
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (s : ℝ) :
    let K := stoppedOBABOKernel a h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    iterateKernel K n z {w | s < phaseEnergy U w} ≤
      ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*s-Q0))) := by
  dsimp only
  have hm := stoppedOBABO_exponential_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz n
  apply (measure_mono (t := {w | (0.79:ℝ)*s < lyapunov U h w}) _).trans
    (exponential_tail_of_lintegral_bound _ _ (lyapunov_measurable a h)
      (by norm_num : (0:ℝ) ≤ 1/20) hm)
  intro w hw
  have hb := (lyapunov_energy_bounds a hstar hzero hL w).1
  change s < phaseEnergy U w at hw
  change (0.79:ℝ)*s < lyapunov U h w
  linarith

/-- Lemma 5.6(iii), before the elementary Gaussian norm-tail simplification:
the exact probability mass removed by stopping has the paper's bound. -/
theorem stoppedOBABO_exit_bound
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let K := stoppedOBABOKernel a h (Real.exp (-h)) σ vstar
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    1-iterateKernel K n z univ ≤ (n : ℝ≥0∞)*
      (ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-Q0)))+
        stdGaussian E {ξ | vstar/2 < ‖σ•ξ‖}) := by
  dsimp only
  apply iterateKernel_loss_bound _ (stoppedOBABOKernel_mass_le_one a h _ _ vstar) _ z _ n
  intro k
  have hU := a.twice_contDiff.continuous.measurable
  have hH : Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop
  have hA : MeasurableSet {w : E × E | vstar^2/32 < phaseEnergy U w} :=
    measurableSet_lt measurable_const hH
  calc
    _ ≤ ∫⁻ w, {v : E × E | vstar^2/32 < phaseEnergy U v}.indicator (fun _ => 1) w+
        stdGaussian E {ξ | vstar/2 < ‖Real.sqrt (1-Real.exp (-2*h))•ξ‖}
        ∂iterateKernel (stoppedOBABOKernel a h (Real.exp (-h))
          (Real.sqrt (1-Real.exp (-2*h))) vstar) k z :=
      lintegral_mono (stoppedOBABOKernel_loss a h _ _ vstar)
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hA),
        lintegral_indicator_const hA, one_mul, lintegral_const]
    _ ≤ _ := by
      apply add_le_add
      · simpa only [mul_div_assoc] using stoppedOBABO_energy_tail a a2 hstar hzero hh hL
          hv hLH hscale hR z hz k (vstar^2/32)
      · have hm := iterateKernel_mass_le_one _
          (stoppedOBABOKernel_mass_le_one a h (Real.exp (-h))
            (Real.sqrt (1-Real.exp (-2*h))) vstar) k z
        simpa only [mul_one] using mul_le_mul_right hm
          (stdGaussian E {ξ | vstar/2 < ‖Real.sqrt (1-Real.exp (-2*h))•ξ‖})

theorem stoppedOBABO_energy_moment
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ)
    (ω : ℝ) (hω : 0 ≤ ω) (hωmax : ω ≤ 2) :
    let K := stoppedOBABOKernel a h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    Integrable (fun w => (phaseEnergy U w)^ω) (iterateKernel K n z) ∧
      (∫ w, (phaseEnergy U w)^ω ∂iterateKernel K n z) ≤
        ((1.266:ℝ)*(Q0+50))^ω := by
  dsimp only
  have hU := a.twice_contDiff.continuous.measurable
  have hH : Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop
  exact stopped_energy_moment _
    (iterateKernel_mass_le_one _ (stoppedOBABOKernel_mass_le_one a h _ _ vstar) n z)
    (phaseEnergy U) (lyapunov U h) hH (lyapunov_measurable a h)
    (a.normalized_energy_nonnegative hstar hzero)
    (fun w => (lyapunov_energy_bounds a hstar hzero hL w).1) _ (by positivity)
    (stoppedOBABO_exponential_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz n)
    ω hω hωmax

end PersistencePays

#print axioms PersistencePays.stoppedOBABO_exponential_moment
#print axioms PersistencePays.stoppedOBABO_exit_bound
#print axioms PersistencePays.stoppedOBABO_energy_moment
