import PersistencePays.CappedFlightConditioning
import PersistencePays.ConditionalDensityBound
import PersistencePays.DensityCapPropagation

/-! Uniform energy and conditioned entropy bounds along the actual capped flight. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.normalized_potential_add_bound {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (x z:E) :
    U (x+z)≤2*U x+L*‖z‖^2 := by
  have hd := potential_descent_bound U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian L a.upper x (x+z)
  rw [add_sub_cancel_left] at hd
  have hg := a.normalized_gradient_bound hstar hzero x
  have hi := real_inner_le_norm (gradient U x) z
  have hp := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*L by positivity [a.L_pos])
  have hs := sq_nonneg (‖gradient U x‖-L*‖z‖)
  have hy : ⟪gradient U x,z⟫_ℝ≤U x+L/2*‖z‖^2 := by
    nlinarith [a.L_pos]
  linarith

theorem cappedFlight_position_time {h vstar s:ℝ} (hh:0 ≤ h) (hs:0 ≤ s) (hsh:s ≤ h) (z:E×E) :
    ∃u:ℝ,0 ≤ u ∧ u ≤ h ∧ (cappedFlightEquiv h vstar s z).1=z.1+u•z.2 := by
  by_cases hm:s ≤ h/2
  · refine ⟨s,hs,hsh,?_⟩
    simp only [cappedFlightEquiv,hm,ite_true]
    rfl
  · by_cases hf:vstar<‖z.2‖
    · refine ⟨h-s,by linarith,by linarith,?_⟩
      simp only [cappedFlightEquiv,hm,ite_false,MeasurableEquiv.trans_apply]
      change (freeTransport (s-h/2) (speedFlip vstar (freeTransport (h/2) z))).1=_
      simp only [freeTransport,drift,speedFlip,hf,ite_true,velocityFlip]
      module
    · refine ⟨s,hs,hsh,?_⟩
      rw [cappedFlight_slow (not_lt.mp hf)]
      rfl

theorem A1.cappedFlight_energy_bound {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 ≤ h) (hL:L*h^2≤1/2)
    (vstar s:ℝ) (hs:0 ≤ s) (hsh:s ≤ h) (z:E×E) :
    phaseEnergy U (cappedFlightEquiv h vstar s z)≤2*U z.1+‖z.2‖^2 := by
  obtain ⟨u,hu,huh,hx⟩ := cappedFlight_position_time hh hs hsh z
  rw [phaseEnergy_eq_norm,hx,cappedFlight_snd_norm]
  have hb := a.normalized_potential_add_bound hstar hzero z.1 (u•z.2)
  have hu2 : u^2≤h^2 := by nlinarith
  have hv2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 a.L_pos.le) (sq_nonneg ‖z.2‖)
  have hv3 := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖z.2‖)
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hb
  nlinarith

theorem A1.normalized_phase_log_normalizer {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) :
    Real.log (∫z,Real.exp (-phaseEnergy U z)∂((volume:Measure E).prod volume))≤
      (Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi) := by
  have hz := a.log_gibbs_normalizer_le
  rw [hstar,hzero] at hz
  simp only [neg_zero,div_one,zero_add] at hz
  rw [phase_gibbs_normalizer,Real.log_mul (integral_exp_pos a.gibbs_integrable).ne'
    (integral_exp_pos (kinetic_gibbs_integrable (E:=E))).ne',kinetic_normalizer_real,
    Real.log_rpow (by positivity : 0 < 2*Real.pi)]
  linarith

theorem cappedFlight_setIntegral (μ:Measure (E×E)) (h vstar s:ℝ)
    (f:E×E→ℝ) (hf:Measurable f) :
    (∫z in fastVelocitySet vstar,f z∂cappedFlightLaw μ h vstar s)=
      ∫z in fastVelocitySet vstar,f (cappedFlightEquiv h vstar s z)∂μ := by
  have hA := fastVelocitySet_measurable (E:=E) vstar
  rw [←integral_indicator hA,←integral_indicator hA]
  unfold cappedFlightLaw
  rw [integral_map (cappedFlightEquiv h vstar s).measurable.aemeasurable
    (hf.indicator hA).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with z
  have hp : cappedFlightEquiv h vstar s z ∈ fastVelocitySet vstar ↔ z∈fastVelocitySet vstar := by
    simp only [fastVelocitySet,mem_setOf_eq,cappedFlight_snd_norm]
  by_cases hz:z∈fastVelocitySet vstar
  · simp only [indicator_of_mem hz,indicator_of_mem (hp.mpr hz)]
  · simp only [indicator_of_notMem hz,indicator_of_notMem (not_congr hp |>.mpr hz)]

theorem A1.cappedFlight_exceptional_energy {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 ≤ h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (vstar s:ℝ) (hs:0 ≤ s) (hsh:s ≤ h) :
    (∫z in fastVelocitySet vstar,phaseEnergy U z∂cappedFlightLaw μ h vstar s)≤
      ∫z in fastVelocitySet vstar,(2*U z.1+‖z.2‖^2)∂μ := by
  rw [cappedFlight_setIntegral μ h vstar s _
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)]
  exact integral_mono (a.phaseEnergy_integrable (cappedFlight_memLp hμ h vstar s)).restrict
    (((a.potential_integrable hμ.fst).const_mul 2).add hμ.snd.integrable_norm_pow').restrict
    (a.cappedFlight_energy_bound hstar hzero hh hL vstar s hs hsh)

theorem A1.cappedFlight_exceptional_entropy {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 ≤ h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar s:ℝ) (hs:0 ≤ s) (hsh:s ≤ h) (hpos:μ (fastVelocitySet vstar)≠0) :
    let α := (μ (fastVelocitySet vstar)).toReal
    let p := cappedFlightLaw μ h vstar s
    α*(conditionalGaussianEntropy (cond p (fastVelocitySet vstar)) (stdGaussian E) 0).toReal ≤
      (∫z in fastVelocitySet vstar,(2*U z.1+‖z.2‖^2)∂μ)+α*
        ((Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)+max (Real.log D) 0+Real.log (1/α)) := by
  let p := cappedFlightLaw μ h vstar s
  let A := fastVelocitySet (E:=E) vstar
  let α := (μ A).toReal
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  letI : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  have hA := fastVelocitySet_measurable (E:=E) vstar
  have hp : p A=μ A := cappedFlight_fast_mass μ h vstar s
  have hp0 : p A≠0 := by rwa [hp]
  letI : IsProbabilityMeasure (cond p A) := cond_isProbabilityMeasure hp0
  have hpk := a.cappedFlight_entropy_finite μ hμ hK h vstar s
  have hpcap := volume_stage_density_cap μ (ENNReal.ofReal D) hcap
    (cappedFlightEquiv h vstar s) (cappedFlight_measurePreserving h vstar s)
  have hptilt : klDiv p (((volume:Measure E).prod volume).tilted (-phaseEnergy U))≠∞ := by
    rwa [←phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable]
  have hb := conditioned_gibbs_entropy_density_cap ((volume:Measure E).prod volume)
    (phaseEnergy U) (phase_gibbs_integrable U a.gibbs_integrable) p
    (a.phaseEnergy_integrable (cappedFlightLaw_memLp μ hμ h vstar s)) hptilt D hD hpcap A hA hp0
  rw [←phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable,hp] at hb
  have hck := (conditional_klDiv p (phaseGibbs U) hpk A hA hp0).1
  have hdecomp := a.phase_entropy_eq_sum (cond p A) hck
  have hle : (conditionalGaussianEntropy (cond p A) (stdGaussian E) 0).toReal≤
      (klDiv (cond p A) (phaseGibbs U)).toReal := by
    nlinarith [ENNReal.toReal_nonneg (a:=klDiv (cond p A).fst (positionGibbs U))]
  have hscaled := mul_le_mul_of_nonneg_left hle (show 0 ≤ α from ENNReal.toReal_nonneg)
  have hZ := mul_le_mul_of_nonneg_left (a.normalized_phase_log_normalizer hstar hzero)
    (show 0 ≤ α from ENNReal.toReal_nonneg)
  have henergy := a.cappedFlight_exceptional_energy hstar hzero hh hL μ hμ vstar s hs hsh
  dsimp only at ⊢
  change α*(conditionalGaussianEntropy (cond p A) (stdGaussian E) 0).toReal≤_
  change α*(klDiv (cond p A) (phaseGibbs U)).toReal≤_ at hb
  dsimp only [α,A,p] at *
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.cappedFlight_energy_bound
