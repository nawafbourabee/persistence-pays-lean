import PersistencePays.CappedFlightConditioning
import PersistencePays.KickBalance

/-! The signed endpoint force-kick defect for the actual capped flight. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem cappedFlight_endpoint_fast {h vstar:ℝ} (hh:0 < h) (z:E×E) (hz:vstar<‖z.2‖) :
    cappedFlightEquiv h vstar h z=velocityFlip z := by
  rw [cappedFlightEquiv,if_neg (by linarith : ¬h≤h/2)]
  change freeTransport (h-h/2) (speedFlip vstar (freeTransport (h/2) z))=velocityFlip z
  simp only [freeTransport,drift,speedFlip,hz,ite_true,velocityFlip]
  ext <;> dsimp
  module

def cappedPairedKickDefect (g:E→E) (h vstar:ℝ) (z:E×E) : ℝ :=
  if vstar<‖z.2‖ then -h*⟪z.2,g z.1⟫-2*gradientCorrection g h z.1
  else pairedKickDefect g h z

theorem cappedPairedKickDefect_identity (g:E→E) (h vstar:ℝ) (hh:0 < h) (z:E×E) :
    -(kineticPotential (kick g (-h/2) z).2-kineticPotential z.2)-
      (kineticPotential (kick g (h/2) (cappedFlightEquiv h vstar h z)).2-
        kineticPotential (cappedFlightEquiv h vstar h z).2)=cappedPairedKickDefect g h vstar z := by
  by_cases hz:vstar<‖z.2‖
  · rw [cappedFlight_endpoint_fast hh z hz]
    rw [kick_kinetic_change,kick_kinetic_change]
    simp only [cappedPairedKickDefect,hz,ite_true,velocityFlip,inner_neg_left,gradientCorrection_eq_norm]
    ring
  · rw [cappedFlight_slow (not_lt.mp hz)]
    simpa only [cappedPairedKickDefect,hz,ite_false,freeTransport] using pairedKickDefect_identity g h z

theorem A1.cappedPairedKickDefect_bound {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h vstar:ℝ) (hh:0 < h) (z:E×E) :
    cappedPairedKickDefect (gradient U) h vstar z ≤
      L*h^2/2*‖z.2‖^2+(fastVelocitySet vstar).indicator (fun z=>‖z.2‖^2) z := by
  by_cases hz:vstar<‖z.2‖
  · have hs := sq_nonneg ‖z.2+(h/2)•gradient U z.1‖
    rw [norm_add_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,real_inner_smul_right] at hs
    simp only [cappedPairedKickDefect,hz,ite_true,gradientCorrection_eq_norm,
      indicator_of_mem (show z∈fastVelocitySet vstar from hz)]
    nlinarith [mul_nonneg (show 0≤L*h^2/2 by positivity [a.L_pos]) (sq_nonneg ‖z.2‖)]
  · simpa only [cappedPairedKickDefect,hz,ite_false,indicator_of_notMem
      (show z∉fastVelocitySet vstar from hz),add_zero] using a.pairedKickDefect_bound h hh.le z

/-- Exact pair of kick entropy changes for the capped flight. -/
theorem A1.capped_paired_kick_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (h vstar : ℝ) (hh : 0 < h) (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μpre := μ.map (kickEquiv (gradient U) hg (-h/2))
    let μflight := cappedFlightLaw μ h vstar h
    let μpost := μflight.map (kickEquiv (gradient U) hg (h/2))
    let ρ0 := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal -
      (conditionalGaussianEntropy μpre (stdGaussian E) 0).toReal
    let ρ1 := (conditionalGaussianEntropy μpost (stdGaussian E) 0).toReal -
      (conditionalGaussianEntropy μflight (stdGaussian E) 0).toReal
    Integrable (cappedPairedKickDefect (gradient U) h vstar) μ ∧
    ρ0-ρ1 = ∫ z, cappedPairedKickDefect (gradient U) h vstar z ∂μ ∧
    ρ0-ρ1 ≤ L*h^2/2*(∫ z, ‖z.2‖^2 ∂μ)+(∫z in fastVelocitySet vstar,‖z.2‖^2∂μ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ek := kickEquiv (gradient U) hg (-h/2)
  let ef := cappedFlightEquiv (E := E) h vstar h
  let eo := kickEquiv (gradient U) hg (h/2)
  let μf := μ.map ef
  letI : IsProbabilityMeasure μf := Measure.isProbabilityMeasure_map ef.measurable.aemeasurable
  have hμf : MemLp id 2 μf := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable ef.measurable.aemeasurable).mpr
    exact cappedFlight_memLp hμ h vstar h
  have hKf : klDiv μf (phaseGibbs U) ≠ ∞ :=
    a.volume_stage_entropy_finite μ ef (cappedFlight_measurePreserving h vstar h) hμ (cappedFlight_memLp hμ h vstar h) hK
  have h0 := a.position_stage_velocity_entropy μ ek (kick_measurePreserving (gradient U) hg (-h/2))
    (fun _ => rfl) hμ (a.kick_memLp hμ (-h/2)) hK
  have h1 := a.position_stage_velocity_entropy μf eo (kick_measurePreserving (gradient U) hg (h/2))
    (fun _ => rfl) hμf (a.kick_memLp hμf (h/2)) hKf
  have hk0 : Integrable (fun z => kineticPotential (ek z).2-kineticPotential z.2) μ :=
    (((a.kick_memLp hμ (-h/2)).snd.norm.integrable_sq).div_const 2).sub
      (hμ.snd.norm.integrable_sq.div_const 2)
  have hk1 : Integrable (fun z => kineticPotential (eo (ef z)).2-kineticPotential (ef z).2) μ :=
    (((a.kick_memLp (cappedFlight_memLp hμ h vstar h) (h/2)).snd.norm.integrable_sq).div_const 2).sub
      ((cappedFlight_memLp hμ h vstar h).snd.norm.integrable_sq.div_const 2)
  have hpair : (fun z => -(kineticPotential (ek z).2-kineticPotential z.2) -
      (kineticPotential (eo (ef z)).2-kineticPotential (ef z).2)) =
      cappedPairedKickDefect (gradient U) h vstar := by
    funext z
    exact cappedPairedKickDefect_identity (gradient U) h vstar hh z
  have hi : Integrable (cappedPairedKickDefect (gradient U) h vstar) μ := by
    rw [← hpair]
    exact hk0.neg.sub hk1
  have hm1 : Measurable (fun z => kineticPotential (eo z).2-kineticPotential z.2) := by
    unfold kineticPotential
    exact ((measurable_snd.comp eo.measurable).norm.pow_const 2 |>.div_const 2).sub
      (measurable_snd.norm.pow_const 2 |>.div_const 2)
  rw [show μf=μ.map ef from rfl, integral_map ef.measurable.aemeasurable hm1.aestronglyMeasurable] at h1
  have hid : -(∫ z, kineticPotential (ek z).2-kineticPotential z.2 ∂μ) -
      (∫ z, kineticPotential (eo (ef z)).2-kineticPotential (ef z).2 ∂μ) =
      ∫ z, cappedPairedKickDefect (gradient U) h vstar z ∂μ := by
    have hn : Integrable (fun z => -(kineticPotential (ek z).2-kineticPotential z.2)) μ := hk0.neg
    rw [← hpair, integral_sub hn hk1, integral_neg]
  dsimp only [cappedFlightLaw]
  refine ⟨hi, ?_, ?_⟩
  · linarith [h0.2, h1.2]
  · have hA := fastVelocitySet_measurable (E:=E) vstar
    have hv : Integrable (fun z:E×E=>‖z.2‖^2) μ := hμ.snd.integrable_norm_pow'
    have hb := integral_mono hi ((hv.const_mul (L*h^2/2)).add (hv.indicator hA))
      (fun z => a.cappedPairedKickDefect_bound h vstar hh z)
    change (∫z,cappedPairedKickDefect (gradient U) h vstar z∂μ)≤
      ∫z,L*h^2/2*‖z.2‖^2+(fastVelocitySet vstar).indicator (fun z=>‖z.2‖^2) z∂μ at hb
    rw [integral_add (hv.const_mul _) (hv.indicator hA),integral_const_mul,integral_indicator hA] at hb
    linarith [h0.2,h1.2]

end PersistencePays
#print axioms PersistencePays.A1.capped_paired_kick_entropy
