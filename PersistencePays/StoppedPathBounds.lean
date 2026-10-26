import PersistencePays.FiniteNoisePrefix
import PersistencePays.StoppedOBABOLaw
import PersistencePays.GaussianNormTail

/-! Lemma 5.6 for the literal, finite-array unadjusted OBABO implementation. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stopped_path_exponential_moment
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    (∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar n z,
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*lyapunov U h
        (unadjustedEpochEndpoint (gradient U) h r σ n (z,b)))) ∂gaussianBlock n) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*Q0)) := by
  dsimp only
  rw [stoppedOBABO_block_lintegral a _ _ _ _ _ _ _
    (((lyapunov_measurable a h).const_mul (1/20:ℝ)).exp.ennreal_ofReal)]
  exact stoppedOBABO_exponential_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz n


theorem stopped_path_energy_moment
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ)
    (ω : ℝ) (hω : 0 ≤ ω) (hωmax : ω ≤ 2) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    Integrable (fun b => (phaseEnergy U
      (unadjustedEpochEndpoint (gradient U) h r σ n (z,b)))^ω)
        ((gaussianBlock n).restrict (stoppedBlockEvent U (gradient U) h r σ vstar n z)) ∧
    (∫ b in stoppedBlockEvent U (gradient U) h r σ vstar n z,
      (phaseEnergy U (unadjustedEpochEndpoint (gradient U) h r σ n (z,b)))^ω ∂gaussianBlock n) ≤
        ((1.266:ℝ)*Q)^ω := by
  dsimp only
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  have hi := stoppedOBABO_energy_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz n ω hω hωmax
  have hU := a.twice_contDiff.continuous.measurable
  have hH : Measurable (fun w : E×E => (phaseEnergy U w)^ω) := by
    unfold phaseEnergy
    fun_prop
  have he : Measurable (fun b : NoiseBlock E n =>
      unadjustedEpochEndpoint (gradient U) h r σ n (z,b)) :=
    (measurable_unadjustedEpochEndpoint (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ n).comp (f:=fun b : NoiseBlock E n => (z,b)) measurable_prodMk_left
  dsimp only at hi
  rw [← stoppedOBABO_block_law a h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) vstar n z] at hi
  exact ⟨(integrable_map_measure hH.aestronglyMeasurable he.aemeasurable).mp hi.1,
    (integral_map he.aemeasurable hH.aestronglyMeasurable).symm.trans_le hi.2⟩

theorem stopped_path_exit_bound
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ ≤ (n : ℝ≥0∞)*
      (ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-Q0)))+
        stdGaussian E {ξ | vstar/2 < ‖σ•ξ‖}) := by
  dsimp only
  rw [measure_compl (stoppedBlockEvent_measurable a _ _ _ _ _ _) (measure_ne_top _ _),
    measure_univ, ← stoppedOBABO_block_mass]
  exact stoppedOBABO_exit_bound a a2 hstar hzero hh hL hv hLH hscale hR z hz n

theorem stopped_path_exit_bound_simple
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hd : 4*(Module.finrank ℝ E : ℝ) ≤ vstar^2)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ ≤
      2*(n : ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-Q0))) := by
  dsimp only
  have hhmax : h ≤ 1/8 := by
    have := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  obtain ⟨_, _, hspos, _, _, _, _, hσ⟩ := normalized_ou_coefficients h hh
  have hsmax : Real.sqrt (1-Real.exp (-2*h)) ≤ 1/2 := by nlinarith
  have htail := stdGaussian_scaled_norm_tail (E:=E) _ vstar hspos hsmax hv hd
  have he : ENNReal.ofReal (Real.exp (-vstar^2/8)) ≤
      ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-
        ((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ))))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg vstar, (Nat.cast_nonneg (Module.finrank ℝ E) : (0:ℝ) ≤ Module.finrank ℝ E)]
  calc
    _ ≤ _ := stopped_path_exit_bound a a2 hstar hzero hh hL hv hLH hscale hR z hz n
    _ ≤ (n : ℝ≥0∞)*(ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-
        ((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)))))+
      ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-
        ((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)))))) :=
      mul_le_mul_right (add_le_add le_rfl (htail.trans he)) _
    _ = _ := by ring

theorem prefix_trajectory_eq_unadjustedPath (g : E → E) (h r σ : ℝ)
    {k n : ℕ} (hk : k ≤ n) (z : E×E) (b : NoiseBlock E n) :
    FiniteNoise.trajectory (unadjustedStepWithNoise g h r σ) k z
      (FiniteNoise.prefixNoise hk (zipNoise n b)) =
      unadjustedPath g h r σ (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k := by
  rw [← trajectory_eq_unadjustedPath g h r σ (fun j => firstNoise n j b)
    (fun j => secondNoise n j b) z k]
  congr 1
  funext i
  simp [FiniteNoise.prefixNoise, zipNoise, firstNoise, secondNoise, Fin.castLE, lt_of_lt_of_le i.isLt hk]

/-- An event in the actual finite Gaussian block, including time zero and the endpoint. -/
def maximalEnergyEvent (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n : ℕ) (z : E×E) (s : ℝ) :
    Set (NoiseBlock E n) :=
  {b | ∃ k≤n, s < phaseEnergy U (unadjustedPath g h r σ
      (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k)}


theorem stopped_path_maximal_energy_bound
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (s : ℝ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    gaussianBlock n (maximalEnergyEvent U (gradient U) h r σ n z s) ≤
      gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ+
      (n+1 : ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*s-Q0))) := by
  dsimp only
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let f := unadjustedStepWithNoise (gradient U) h r σ
  let G := stoppedOBABOGood U σ vstar
  let A : Set (E×E) := {w | s < phaseEnergy U w}
  have hf : Measurable f := unadjustedNoiseStep_measurable a h r σ
  have hG : MeasurableSet G := stoppedOBABOGood_measurable a σ vstar
  have hU := a.twice_contDiff.continuous.measurable
  have hH : Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop
  have hA : MeasurableSet A := measurableSet_lt measurable_const hH
  let M : Set (Fin n → E×E) := {b | ∃ k : Fin (n+1),
    FiniteNoise.trajectory f k z (FiniteNoise.prefixNoise (Nat.le_of_lt_succ k.isLt) b) ∈ A}
  have hM : MeasurableSet M := by
    have hi : ∀ k : Fin (n+1), MeasurableSet {b : Fin n → E×E |
        FiniteNoise.trajectory f k z (FiniteNoise.prefixNoise (Nat.le_of_lt_succ k.isLt) b) ∈ A} := by
      intro k
      exact ((FiniteNoise.measurable_trajectory_fixed f hf k z).comp
        (FiniteNoise.prefixNoise_preserving ((stdGaussian E).prod (stdGaussian E))
          (Nat.le_of_lt_succ k.isLt)).measurable) hA
    convert MeasurableSet.iUnion hi using 1
    ext b
    simp [M]
  have he : maximalEnergyEvent U (gradient U) h r σ n z s = zipNoise n ⁻¹' M := by
    ext b
    change (∃ k≤n, s < phaseEnergy U (unadjustedPath (gradient U) h r σ
      (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k)) ↔ _
    constructor
    · rintro ⟨k,hk,henergy⟩
      refine ⟨⟨k,Nat.lt_succ_of_le hk⟩, ?_⟩
      change s < phaseEnergy U (FiniteNoise.trajectory f k z (FiniteNoise.prefixNoise hk (zipNoise n b)))
      rw [prefix_trajectory_eq_unadjustedPath]
      exact henergy
    · rintro ⟨k,henergy⟩
      refine ⟨k,Nat.le_of_lt_succ k.isLt, ?_⟩
      change s < phaseEnergy U (FiniteNoise.trajectory f k z
        (FiniteNoise.prefixNoise (Nat.le_of_lt_succ k.isLt) (zipNoise n b))) at henergy
      rw [prefix_trajectory_eq_unadjustedPath] at henergy
      exact henergy
  have hB : (Measure.pi (fun _ : Fin n => (stdGaussian E).prod (stdGaussian E)))
      (FiniteNoise.goodBlock f G n z)ᶜ =
        gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ := by
    rw [← (zipNoise_preserving n).map_eq,
      Measure.map_apply (zipNoise_preserving n).measurable
        (FiniteNoise.measurable_goodBlock f hf G hG n z).compl]
    congr 1
    rw [preimage_compl, stoppedBlockEvent_eq]
  change gaussianBlock n (maximalEnergyEvent U (gradient U) h r σ n z s) ≤ _
  rw [he, ← Measure.map_apply (zipNoise_preserving n).measurable hM,
    (zipNoise_preserving n).map_eq, ← hB]
  apply FiniteNoise.stopped_maximal_event_bound _ f hf G hG n z A hA
  intro k hk
  exact stoppedOBABO_energy_tail a a2 hstar hzero hh hL hv hLH hscale hR z hz k s


theorem maximal_energy_tail_threshold (Q0 : ℝ) (hQ0 : 0 ≤ Q0) (n : ℕ) :
    (n+1 : ℝ≥0∞)*ENNReal.ofReal
      (Real.exp (-(1/20:ℝ)*((0.79:ℝ)*((1.27:ℝ)*(Q0+20*Real.log (100*((n:ℝ)+1))))-Q0))) ≤
        ENNReal.ofReal (0.01:ℝ) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hl : 0 ≤ Real.log (100*((n:ℝ)+1)) := Real.log_nonneg (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hx : Real.exp (-(1/20:ℝ)*((0.79:ℝ)*((1.27:ℝ)*(Q0+20*Real.log (100*((n:ℝ)+1))))-Q0)) ≤
      1/(100*((n:ℝ)+1)) := by
    calc
      _ ≤ Real.exp (-Real.log (100*((n:ℝ)+1))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hcast : (n+1 : ℝ≥0∞) = ENNReal.ofReal ((n:ℝ)+1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg n) (by norm_num)]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((n:ℝ)+1)*(1/(100*((n:ℝ)+1))) := mul_le_mul_of_nonneg_left hx hn.le
    _ = (0.01:ℝ) := by field_simp; ring

theorem stopped_path_maximal_energy_threshold
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let Q0 := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)
    let R'' := (1.27:ℝ)*(Q0+20*Real.log (100*((n:ℝ)+1)))
    gaussianBlock n (maximalEnergyEvent U (gradient U) h r σ n z R'') ≤
      gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ+
        ENNReal.ofReal (0.01:ℝ) := by
  dsimp only
  exact (stopped_path_maximal_energy_bound a a2 hstar hzero hh hL hv hLH hscale hR z hz n _).trans
    (add_le_add le_rfl (maximal_energy_tail_threshold _ (by positivity) n))

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stopped_path_exponential_moment
#print axioms PersistencePays.OBABOPath.stopped_path_exit_bound_simple

#print axioms PersistencePays.OBABOPath.stopped_path_maximal_energy_threshold
