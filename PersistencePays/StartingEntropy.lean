import PersistencePays.OneStepDensity
import PersistencePays.PhaseGibbsDensity
import PersistencePays.ScalingEntropy
import PersistencePays.FiniteMoments
import PersistencePays.GibbsPartitionBound
import PersistencePays.OUScalarBounds

/-! Actual one-step smoothing and finite starting entropy for OBABO. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.obaboNoiseEquiv_energy_integrable {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (hh : h ≠ 0) (hσ : σ ≠ 0) (z : E × E) :
    Integrable (fun η => phaseEnergy U (obaboNoiseEquiv (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ hh hσ z η)) ((stdGaussian E).prod (stdGaussian E)) := by
  simp_rw [obaboNoiseEquiv_apply]
  apply a.phaseEnergy_integrable
  exact ou_memLp (a.verlet_memLp (ou_memLp (memLp_const z)
    (IsGaussian.memLp_two_id.comp_fst (stdGaussian E)) r σ) h)
      (IsGaussian.memLp_two_id.comp_snd (stdGaussian E)) r σ

theorem obabo_inverse_jacobian_real (h σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) :
    triangularInverseJacobian (E := E) (h*σ) σ =
      ENNReal.ofReal ((h*σ)⁻¹ ^ Module.finrank ℝ E * σ⁻¹ ^ Module.finrank ℝ E) := by
  unfold triangularInverseJacobian
  rw [abs_of_pos (inv_pos.mpr (mul_pos hh hσ)), abs_of_pos (inv_pos.mpr hσ),
    ← ENNReal.ofReal_mul (by positivity)]

theorem obabo_inverse_jacobian_log (h σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) :
    Real.log ((h*σ)⁻¹ ^ Module.finrank ℝ E * σ⁻¹ ^ Module.finrank ℝ E) =
      -(Module.finrank ℝ E : ℝ) * (Real.log h + 2 * Real.log σ) := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_inv, Real.log_inv, Real.log_mul hh.ne' hσ.ne']
  ring

/-- Exact one-step entropy identity, with every moment and absolute-continuity
premise proved from A1 and the two independent Gaussian OU noises. -/
theorem A1.obabo_starting_entropy_identity {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) (z : E × E) :
    let e := obaboNoiseEquiv (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
        h r σ hh.ne' hσ.ne' z
    let ρ := ((stdGaussian E).prod (stdGaussian E)).map e
    klDiv ρ (phaseGibbs U) ≠ ∞ ∧
      (klDiv ρ (phaseGibbs U)).toReal =
        (∫ η, phaseEnergy U (e η) ∂(stdGaussian E).prod (stdGaussian E)) +
          Real.log (∫ x, Real.exp (-U x)) -
          (Module.finrank ℝ E : ℝ)/2 * Real.log (2*Real.pi) -
          (Module.finrank ℝ E : ℝ) -
          (Module.finrank ℝ E : ℝ) * (Real.log h + 2*Real.log σ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := obaboNoiseEquiv (gradient U) hg h r σ hh.ne' hσ.ne' z
  let c := (h*σ)⁻¹ ^ Module.finrank ℝ E * σ⁻¹ ^ Module.finrank ℝ E
  have hc : 0 < c := by dsimp [c]; positivity
  have he : Measure.map e ((volume : Measure E).prod volume) =
      ENNReal.ofReal c • ((volume : Measure E).prod volume) := by
    dsimp [e, obaboNoiseEquiv]
    rw [triangularNoiseEquiv_map_volume, obabo_inverse_jacobian_real h σ hh hσ]
  have hF : Measurable (phaseEnergy (kineticPotential : E → ℝ)) :=
    phaseEnergy_measurable _ (by unfold kineticPotential; fun_prop)
  have hH := phaseEnergy_measurable U a.twice_contDiff.continuous.measurable
  have hHE := a.obaboNoiseEquiv_energy_integrable h r σ hh.ne' hσ.ne' z
  have hD : Integrable (fun η => phaseEnergy U (e η)-phaseEnergy kineticPotential η)
      (((volume : Measure E).prod volume).tilted (-phaseEnergy kineticPotential)) := by
    rw [← gaussianPair_eq_tilted]
    exact hHE.sub gaussianPair_energy_integrable
  have ht := scaled_gibbs_entropy ((volume : Measure E).prod volume)
    (phaseEnergy kineticPotential) (phaseEnergy U) hF hH
    (phase_gibbs_integrable kineticPotential kinetic_gibbs_integrable)
    (phase_gibbs_integrable U a.gibbs_integrable) e c hc he hD
  rw [← gaussianPair_eq_tilted,
    ← phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at ht
  refine ⟨ht.1, ?_⟩
  rw [ht.2, integral_sub hHE gaussianPair_energy_integrable, gaussianPair_energy,
    phase_gibbs_normalizer, phase_gibbs_normalizer]
  have hZU := integral_exp_pos a.gibbs_integrable
  have hZK := integral_exp_pos (kinetic_gibbs_integrable (E := E))
  rw [Real.log_mul hZU.ne' hZK.ne', Real.log_mul hZK.ne' hZK.ne',
    kinetic_normalizer_real, Real.log_rpow (by positivity : 0 < 2*Real.pi),
    show Real.log c = -(Module.finrank ℝ E : ℝ) * (Real.log h + 2*Real.log σ) from
      obabo_inverse_jacobian_log h σ hh hσ]
  ring


theorem obabo_step_kernel_eq_noise_map (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (hh : h ≠ 0) (hσ : σ ≠ 0) (z : E × E) :
    OBABOPath.unadjustedStepKernel g hg h r σ z =
      ((stdGaussian E).prod (stdGaussian E)).map (obaboNoiseEquiv g hg h r σ hh hσ z) := by
  rw [OBABOPath.unadjustedStepKernel, FiniteNoise.noiseKernel_apply]
  congr 1
  funext η
  exact (obaboNoiseEquiv_apply g hg h r σ hh hσ z η).symm

theorem heatConstant_square :
    heatConstant E 1 ^ 2 = ((2*Real.pi) ^ Module.finrank ℝ E)⁻¹ := by
  unfold heatConstant
  rw [mul_one, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num only [Nat.cast_ofNat]
  rw [show (-((Module.finrank ℝ E : ℝ)/2)) * (2:ℝ) =
    -(Module.finrank ℝ E : ℝ) by ring, Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem obabo_density_constant (h σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) :
    triangularInverseJacobian (E := E) (h*σ) σ * ENNReal.ofReal (heatConstant E 1 ^ 2) =
      ENNReal.ofReal (((2*Real.pi*h*σ^2) ^ Module.finrank ℝ E)⁻¹) := by
  rw [obabo_inverse_jacobian_real h σ hh hσ,
    ← ENNReal.ofReal_mul (by positivity), heatConstant_square]
  congr 1
  simp only [mul_inv_rev, mul_pow, inv_pow, pow_two]
  ring

/-- The literal unadjusted transition kernel has a measurable bounded Lebesgue
 density. The exact bound is the one in Lemma 4.14. -/
theorem obabo_step_density_bound (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) (z : E × E) :
    ∃ f : E × E → ℝ≥0∞, Measurable f ∧
      OBABOPath.unadjustedStepKernel g hg h r σ z = ((volume : Measure E).prod volume).withDensity f ∧
      ∀ w, f w ≤ ENNReal.ofReal (((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹) := by
  let e := obaboNoiseEquiv g hg h r σ hh.ne' hσ.ne' z
  let f := fun w => triangularInverseJacobian (E := E) (h*σ) σ * gaussianPairDensity (e.symm w)
  refine ⟨f, measurable_const.mul (measurable_gaussianPairDensity.comp e.symm.measurable), ?_, ?_⟩
  · rw [obabo_step_kernel_eq_noise_map g hg h r σ hh.ne' hσ.ne' z]
    exact triangularNoiseEquiv_density _ _ _ _ _ _ _
  · intro w
    calc
      f w ≤ triangularInverseJacobian (E := E) (h*σ) σ * ENNReal.ofReal (heatConstant E 1 ^ 2) :=
        mul_le_mul' le_rfl (gaussianPairDensity_le (e.symm w))
      _ = _ := obabo_density_constant h σ hh hσ

theorem A1.unadjusted_step_entropy_finite {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) (z : E × E) :
    klDiv (OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ z) (phaseGibbs U) ≠ ∞ := by
  rw [obabo_step_kernel_eq_noise_map _ _ h r σ hh.ne' hσ.ne' z]
  exact (a.obabo_starting_entropy_identity h r σ hh hσ z).1


theorem starting_entropy_scalar_bound (d m h σ : ℝ) (hd : 0 ≤ d)
    (hm : 0 < m) (hh : 0 < h) (hσ : 0 < σ) (hst : Real.sqrt m*h < 1)
    (hsq : 2*(Real.sqrt m*h)*(1-Real.sqrt m*h) ≤ σ^2) :
    d/2*Real.log (2*Real.pi/m) - d/2*Real.log (2*Real.pi) - d -
      d*(Real.log h+2*Real.log σ) ≤
      d*Real.log ((2*Real.exp 1*m*h^2*(1-Real.sqrt m*h))⁻¹) := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have h1 : 0 < 1-Real.sqrt m*h := by linarith
  have hp : 0 < 2*(Real.sqrt m*h)*(1-Real.sqrt m*h) := by positivity
  have hl := Real.log_le_log hp hsq
  rw [Real.log_pow] at hl
  rw [Real.log_mul (by positivity) h1.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (mul_ne_zero hsm.ne' hh.ne'),
    Real.log_mul hsm.ne' hh.ne', Real.log_sqrt hm.le] at hl
  have hprod := mul_le_mul_of_nonneg_left hl hd
  rw [Real.log_div (by positivity) hm.ne', Real.log_inv,
    Real.log_mul (by positivity) h1.ne', Real.log_mul (by positivity) (pow_ne_zero 2 hh.ne'),
    Real.log_mul (by positivity) hm.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_pow]
  nlinarith

/-- Lemma 4.14, in a shift-invariant form valid without assuming U*=0.
The denominator equals `2 e hbar² (1−sqrt(m)h)/κ`. -/
theorem A1.lemma_4_14 {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h : ℝ) (hh : 0 < h) (hst : Real.sqrt m*h < 1) (z : E × E) :
    let r := Real.exp (-(Real.sqrt m*h))
    let σ := Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h)))
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    klDiv (K z) (phaseGibbs U) ≠ ∞ ∧
      (klDiv (K z) (phaseGibbs U)).toReal ≤
        (∫ w, phaseEnergy U w ∂K z) - U a.minimizer +
          (Module.finrank ℝ E : ℝ) * Real.log
            ((2*Real.exp 1*m*h^2*(1-Real.sqrt m*h))⁻¹) ∧
      ∃ f : E × E → ℝ≥0∞, Measurable f ∧
        K z = ((volume : Measure E).prod volume).withDensity f ∧
        ∀ w, f w ≤ ENNReal.ofReal (((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹) := by
  let t := Real.sqrt m*h
  have ht : 0 < t := mul_pos (Real.sqrt_pos.mpr a.m_pos) hh
  let r := Real.exp (-t)
  let σ := Real.sqrt (1-Real.exp (-2*t))
  have hσ : 0 < σ := by
    apply Real.sqrt_pos.mpr
    have he : Real.exp (-2*t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := obaboNoiseEquiv (gradient U) hg h r σ hh.ne' hσ.ne' z
  have hid := a.obabo_starting_entropy_identity h r σ hh hσ z
  have hmap := obabo_step_kernel_eq_noise_map (gradient U) hg h r σ hh.ne' hσ.ne' z
  change OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z =
    ((stdGaussian E).prod (stdGaussian E)).map e at hmap
  change klDiv (OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z) (phaseGibbs U) ≠ ∞ ∧ _
  refine ⟨?_, ?_, obabo_step_density_bound (gradient U) hg h r σ hh hσ z⟩
  · rw [hmap]
    exact hid.1
  · rw [hmap, integral_map e.measurable.aemeasurable
      (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable).aestronglyMeasurable,
      hid.2]
    have hZ := a.log_gibbs_normalizer_le
    have hsq := (normalized_ou_coefficients t ht.le).2.2.2.2.2.2.1
    have hbound := starting_entropy_scalar_bound (Module.finrank ℝ E) m h σ
      (by positivity) a.m_pos hh hσ hst hsq
    linarith

end PersistencePays
#print axioms PersistencePays.A1.obabo_starting_entropy_identity
#print axioms PersistencePays.A1.lemma_4_14
#print axioms PersistencePays.obabo_step_density_bound
