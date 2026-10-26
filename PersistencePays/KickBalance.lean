import PersistencePays.KickEntropy

/-! The signed pair of force-kick entropy defects, with the actual curvature bound. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.directional_gradient_increment {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (x v : E) (h : ℝ) (hh : 0 ≤ h) :
    ⟪v,gradient U (x+h•v)-gradient U x⟫ ≤ L*h*‖v‖^2 := by
  have hd (t : ℝ) := gradient_line_derivative (gradient U) (hessian U) a.hasHessianAt x v t
  have hb := image_sub_le_mul_sub_of_deriv_le (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; exact a.upper (x+t•v) v) hh
  simp only [zero_smul, add_zero, sub_zero] at hb
  rw [inner_sub_right, real_inner_comm (gradient U (x+h•v)) v, real_inner_comm (gradient U x) v]
  nlinarith

def pairedKickDefect (g : E → E) (h : ℝ) (z : E × E) : ℝ :=
  h/2*⟪z.2,g (z.1+h•z.2)-g z.1⟫ - gradientCorrection g h z.1 -
    gradientCorrection g h (z.1+h•z.2)

theorem pairedKickDefect_identity (g : E → E) (h : ℝ) (z : E × E) :
    -(kineticPotential (kick g (-h/2) z).2-kineticPotential z.2) -
      (kineticPotential (kick g (h/2) (drift h z)).2-kineticPotential (drift h z).2) =
      pairedKickDefect g h z := by
  rw [kick_kinetic_change, kick_kinetic_change]
  simp only [drift, pairedKickDefect, inner_sub_right, gradientCorrection_eq_norm]
  ring

theorem A1.pairedKickDefect_bound {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h : ℝ) (hh : 0 ≤ h) (z : E × E) :
    pairedKickDefect (gradient U) h z ≤ L*h^2/2*‖z.2‖^2 := by
  have hb := mul_le_mul_of_nonneg_left (a.directional_gradient_increment z.1 z.2 h hh)
    (show 0 ≤ h/2 by positivity)
  have hG (x : E) : 0 ≤ gradientCorrection (gradient U) h x := by
    rw [gradientCorrection_eq_norm]
    positivity
  unfold pairedKickDefect
  nlinarith [hG z.1, hG (z.1+h•z.2)]

/-- Lemma 4.9(ii), parameterized by the actual post-first-kick law μ.
The first pre-kick law is obtained by the exact inverse kick. -/
theorem A1.lemma_4_9_ii {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 ≤ h) (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μpre := μ.map (kickEquiv (gradient U) hg (-h/2))
    let μflight := μ.map (freeTransportEquiv h)
    let μpost := μflight.map (kickEquiv (gradient U) hg (h/2))
    let ρ0 := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal -
      (conditionalGaussianEntropy μpre (stdGaussian E) 0).toReal
    let ρ1 := (conditionalGaussianEntropy μpost (stdGaussian E) 0).toReal -
      (conditionalGaussianEntropy μflight (stdGaussian E) 0).toReal
    Integrable (pairedKickDefect (gradient U) h) μ ∧
    ρ0-ρ1 = ∫ z, pairedKickDefect (gradient U) h z ∂μ ∧
    ρ0-ρ1 ≤ L*h^2/2*(∫ z, ‖z.2‖^2 ∂μ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ek := kickEquiv (gradient U) hg (-h/2)
  let ef := freeTransportEquiv (E := E) h
  let eo := kickEquiv (gradient U) hg (h/2)
  let μf := μ.map ef
  letI : IsProbabilityMeasure μf := Measure.isProbabilityMeasure_map ef.measurable.aemeasurable
  have hμf : MemLp id 2 μf := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable ef.measurable.aemeasurable).mpr
    exact drift_memLp hμ h
  have hKf : klDiv μf (phaseGibbs U) ≠ ∞ :=
    a.volume_stage_entropy_finite μ ef (drift_measurePreserving h) hμ (drift_memLp hμ h) hK
  have h0 := a.position_stage_velocity_entropy μ ek (kick_measurePreserving (gradient U) hg (-h/2))
    (fun _ => rfl) hμ (a.kick_memLp hμ (-h/2)) hK
  have h1 := a.position_stage_velocity_entropy μf eo (kick_measurePreserving (gradient U) hg (h/2))
    (fun _ => rfl) hμf (a.kick_memLp hμf (h/2)) hKf
  have hk0 : Integrable (fun z => kineticPotential (ek z).2-kineticPotential z.2) μ :=
    (((a.kick_memLp hμ (-h/2)).snd.norm.integrable_sq).div_const 2).sub
      (hμ.snd.norm.integrable_sq.div_const 2)
  have hk1 : Integrable (fun z => kineticPotential (eo (ef z)).2-kineticPotential (ef z).2) μ :=
    (((a.kick_memLp (drift_memLp hμ h) (h/2)).snd.norm.integrable_sq).div_const 2).sub
      ((drift_memLp hμ h).snd.norm.integrable_sq.div_const 2)
  have hpair : (fun z => -(kineticPotential (ek z).2-kineticPotential z.2) -
      (kineticPotential (eo (ef z)).2-kineticPotential (ef z).2)) =
      pairedKickDefect (gradient U) h := by
    funext z
    exact pairedKickDefect_identity (gradient U) h z
  have hi : Integrable (pairedKickDefect (gradient U) h) μ := by
    rw [← hpair]
    exact hk0.neg.sub hk1
  have hm1 : Measurable (fun z => kineticPotential (eo z).2-kineticPotential z.2) := by
    unfold kineticPotential
    exact ((measurable_snd.comp eo.measurable).norm.pow_const 2 |>.div_const 2).sub
      (measurable_snd.norm.pow_const 2 |>.div_const 2)
  rw [show μf=μ.map ef from rfl, integral_map ef.measurable.aemeasurable hm1.aestronglyMeasurable] at h1
  have hid : -(∫ z, kineticPotential (ek z).2-kineticPotential z.2 ∂μ) -
      (∫ z, kineticPotential (eo (ef z)).2-kineticPotential (ef z).2 ∂μ) =
      ∫ z, pairedKickDefect (gradient U) h z ∂μ := by
    have hn : Integrable (fun z => -(kineticPotential (ek z).2-kineticPotential z.2)) μ := hk0.neg
    rw [← hpair, integral_sub hn hk1, integral_neg]
  dsimp only
  refine ⟨hi, ?_, ?_⟩
  · linarith [h0.2, h1.2]
  · have hb := integral_mono hi (hμ.snd.norm.integrable_sq.const_mul (L*h^2/2))
      (fun z => a.pairedKickDefect_bound h hh z)
    rw [integral_const_mul] at hb
    simp only [id_eq] at hb
    linarith [h0.2, h1.2]

end PersistencePays
#print axioms PersistencePays.A1.lemma_4_9_ii
