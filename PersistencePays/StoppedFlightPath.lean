import PersistencePays.StoppedFreshNoise
import PersistencePays.StoppedPathBounds
import PersistencePays.StoppedFlightMoment

/-! Lemma 5.6(v) for the actual Gaussian noise arrays. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def lastFlight (g : E → E) (h r σ : ℝ) (n : ℕ) (z : E×E) (b : NoiseBlock E (n+1)) : E :=
  flightVelocity g h (ou r σ (firstNoise (n+1) n b)
    (unadjustedPath g h r σ (fun j => firstNoise (n+1) j b) (fun j => secondNoise (n+1) j b) z n))

theorem lastFlight_eq (g : E → E) (h r σ : ℝ) (n : ℕ) (z : E×E) (b : NoiseBlock E (n+1)) :
    lastFlight g h r σ n z b =
      flightVelocity g h (ou r σ
        (FiniteNoise.beforeLastStep (unadjustedStepWithNoise g h r σ) n z (zipNoise (n+1) b)).2.1
        (FiniteNoise.beforeLastStep (unadjustedStepWithNoise g h r σ) n z (zipNoise (n+1) b)).1) := by
  have ht := prefix_trajectory_eq_unadjustedPath g h r σ (Nat.le_succ n) z b
  have hp : (fun i : Fin n => zipNoise (n+1) b i.castSucc) =
      FiniteNoise.prefixNoise (Nat.le_succ n) (zipNoise (n+1) b) := rfl
  simp only [FiniteNoise.beforeLastStep, hp, ht]
  unfold lastFlight firstNoise zipNoise
  simp [Fin.last]

theorem stopped_beforeLastStep_law {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    ((gaussianBlock (n+1)).restrict (stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z)).map
      (FiniteNoise.beforeLastStep (unadjustedStepWithNoise (gradient U) h r σ) n z ∘ zipNoise (n+1)) =
      ((iterateKernel (stoppedOBABOKernel a h r σ vstar) n z).prod
        ((stdGaussian E).prod (stdGaussian E))).restrict (stoppedOBABOGood U σ vstar) := by
  have hf : Measurable (unadjustedStepWithNoise (gradient U) h r σ) :=
    unadjustedNoiseStep_measurable a h r σ
  have hG := stoppedOBABOGood_measurable a σ vstar
  rw [stoppedBlockEvent_eq,
    ← Measure.map_map (FiniteNoise.measurable_beforeLastStep _ hf n z)
      (zipNoise_preserving (n+1)).measurable,
    ← Measure.restrict_map (zipNoise_preserving (n+1)).measurable
      (FiniteNoise.measurable_goodBlock _ hf _ hG (n+1) z),
    (zipNoise_preserving (n+1)).map_eq]
  exact FiniteNoise.stopped_fresh_noise_law_next _ _ hf _ hG n z

theorem stopped_lastFlight_third_lintegral
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z,
      ENNReal.ofReal (‖lastFlight (gradient U) h r σ n z b‖^3) ∂gaussianBlock (n+1)) ≤
        ENNReal.ofReal (((6.6:ℝ)*Q)^(3/2:ℝ)) := by
  dsimp only
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let ν := iterateKernel (stoppedOBABOKernel a h r σ vstar) n z
  let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
  have hνmass : ν univ ≤ 1 := iterateKernel_mass_le_one _
    (stoppedOBABOKernel_mass_le_one a h r σ vstar) n z
  letI : IsFiniteMeasure ν := ⟨lt_of_le_of_lt hνmass (by simp)⟩
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let F : ((E×E)×E) → ℝ≥0∞ := fun p => ENNReal.ofReal
    (‖flightVelocity (gradient U) h (ou r σ p.2 p.1)‖^3)
  have hF : Measurable F := by dsimp [F, flightVelocity, ou]; fun_prop
  let project : ((E×E)×(E×E)) → (E×E)×E := fun p => (p.1,p.2.1)
  have hp : Measurable project := measurable_fst.prodMk measurable_snd.fst
  have hf : Measurable (unadjustedStepWithNoise (gradient U) h r σ) :=
    unadjustedNoiseStep_measurable a h r σ
  have he : Measurable (FiniteNoise.beforeLastStep
      (unadjustedStepWithNoise (gradient U) h r σ) n z ∘ zipNoise (n+1)) :=
    (FiniteNoise.measurable_beforeLastStep _ hf n z).comp (zipNoise_preserving (n+1)).measurable
  have hmap : (ν.prod ((stdGaussian E).prod (stdGaussian E))).map project = ν.prod (stdGaussian E) := by
    have hh := Measure.map_prod_map ν ((stdGaussian E).prod (stdGaussian E)) measurable_id measurable_fst
    have heproject : Prod.map (id : E×E → E×E) (Prod.fst : E×E → E) = project := rfl
    rw [heproject, Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] at hh
    exact hh.symm
  have hhmax : h ≤ 1/8 := by
    have := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  obtain ⟨_, _, hspos, hnorm, _, _, _, hσ⟩ := normalized_ou_coefficients h hh
  have hr : r^2 ≤ 1 := by dsimp [r]; nlinarith [sq_nonneg (Real.sqrt (1-Real.exp (-2*h)))]
  have hs : σ^2 ≤ 1/4 := by dsimp [σ]; nlinarith
  have hmom := stoppedOBABO_energy_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz n
    (3/2:ℝ) (by norm_num) (by norm_num)
  have hH : Measurable (fun w : E×E => (phaseEnergy U w)^(3/2:ℝ)) := by
    have hU := a.twice_contDiff.continuous.measurable
    unfold phaseEnergy
    fun_prop
  have hmoment : (∫⁻ w, ENNReal.ofReal ((phaseEnergy U w)^(3/2:ℝ)) ∂ν) ≤
      ENNReal.ofReal (((1.266:ℝ)*Q)^(3/2:ℝ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmom.1
      (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (a.normalized_energy_nonnegative hstar hzero w) _)]
    exact ENNReal.ofReal_le_ofReal hmom.2
  have hb := noisy_flight_third_lintegral a hstar hzero hL hr hs ν
    (iterateKernel_mass_le_one _ (stoppedOBABOKernel_mass_le_one a h r σ vstar) n z)
    (show 27*(Module.finrank ℝ E : ℝ)+50 ≤ Q by dsimp [Q]; linarith) hmoment
  calc
    _ = ∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z,
        (F ∘ project) ((FiniteNoise.beforeLastStep (unadjustedStepWithNoise (gradient U) h r σ) n z ∘
          zipNoise (n+1)) b) ∂gaussianBlock (n+1) := by
      apply lintegral_congr
      intro b
      exact congrArg (fun v : E => ENNReal.ofReal (‖v‖^3)) (lastFlight_eq (gradient U) h r σ n z b)
    _ = ∫⁻ p, (F ∘ project) p ∂(ν.prod ((stdGaussian E).prod (stdGaussian E))).restrict
        (stoppedOBABOGood U σ vstar) := by
      rw [← lintegral_map (hF.comp hp) he, stopped_beforeLastStep_law]
    _ ≤ ∫⁻ p, (F ∘ project) p ∂ν.prod ((stdGaussian E).prod (stdGaussian E)) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ p, F p ∂ν.prod (stdGaussian E) := by
      change (∫⁻ p, F (project p) ∂ν.prod ((stdGaussian E).prod (stdGaussian E))) = _
      rw [← lintegral_map hF hp, hmap]
    _ ≤ _ := hb


theorem measurable_lastFlight (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (n : ℕ) (z : E×E) : Measurable (lastFlight g h r σ n z) := by
  have he : lastFlight g h r σ n z =
      (fun p : (E×E)×(E×E) => flightVelocity g h (ou r σ p.2.1 p.1)) ∘
        (FiniteNoise.beforeLastStep (unadjustedStepWithNoise g h r σ) n z ∘ zipNoise (n+1)) :=
    funext (lastFlight_eq g h r σ n z)
  rw [he]
  have houter : Measurable (fun p : (E×E)×(E×E) => flightVelocity g h (ou r σ p.2.1 p.1)) := by
    unfold flightVelocity ou
    fun_prop
  exact houter.comp ((FiniteNoise.measurable_beforeLastStep _
    (measurable_unadjustedStepWithNoise g hg h r σ) n z).comp (zipNoise_preserving (n+1)).measurable)

theorem stopped_lastFlight_third_moment
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    Integrable (fun b => ‖lastFlight (gradient U) h r σ n z b‖^3)
      ((gaussianBlock (n+1)).restrict (stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z)) ∧
    (∫ b in stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z,
      ‖lastFlight (gradient U) h r σ n z b‖^3 ∂gaussianBlock (n+1)) ≤ ((6.6:ℝ)*Q)^(3/2:ℝ) := by
  dsimp only
  have hb := stopped_lastFlight_third_lintegral a a2 hstar hzero hh hL hv hLH hscale hR z hz n
  have hm := (measurable_lastFlight (gradient U)
    (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) n z).norm.pow_const 3
  have hn (b : NoiseBlock E (n+1)) :
      0 ≤ ‖lastFlight (gradient U) h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) n z b‖^3 := by positivity
  constructor
  · refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    exact ht

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stopped_lastFlight_third_lintegral

#print axioms PersistencePays.OBABOPath.stopped_lastFlight_third_moment
