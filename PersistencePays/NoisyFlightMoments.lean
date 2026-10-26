import PersistencePays.ComparisonEnergyUniform
import PersistencePays.GaussianEnergyMoment

/-! Exact conditional Gaussian second moments and L² flight bounds. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_affine_norm_square (b : E) (σ : ℝ) :
    (∫ ξ : E, ‖b+σ•ξ‖^2 ∂stdGaussian E) = ‖b‖^2+σ^2*(Module.finrank ℝ E : ℝ) := by
  have hi : Integrable (fun ξ : E => ⟪b,ξ⟫) (stdGaussian E) :=
    ((innerSL ℝ b).comp_memLp' (IsGaussian.memLp_two_id (μ:=stdGaussian E))).integrable (by norm_num)
  have he (ξ : E) : ‖b+σ•ξ‖^2 = (‖b‖^2+σ^2*‖ξ‖^2)+(2*σ)*⟪b,ξ⟫ := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [he]
  have hbase : Integrable (fun ξ : E => ‖b‖^2+σ^2*‖ξ‖^2) (stdGaussian E) :=
    (integrable_const _).add (stdGaussian_norm_square_integrable.const_mul (σ^2))
  rw [integral_add hbase
    (hi.const_mul (2*σ)), integral_add (integrable_const _)
      (stdGaussian_norm_square_integrable.const_mul (σ^2)),
    integral_const_mul, integral_const_mul, stdGaussian_norm_square]
  have hz : (∫ ξ : E, ⟪b,ξ⟫ ∂stdGaussian E) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ b)
  simp only [hz, mul_zero, add_zero, integral_const, probReal_univ, one_smul]

theorem A1.flight_square_measurable {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (h : ℝ) :
    Measurable (fun z : E×E => ‖flightVelocity (gradient U) h z‖^2) := by
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  unfold flightVelocity
  fun_prop

theorem A1.ou_flight_second {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hr : r^2 ≤ 1) (z : E×E) :
    (∫ w, ‖flightVelocity (gradient U) h w‖^2 ∂phaseOUKernel r σ z) ≤
      (257/128:ℝ)*phaseEnergy U z + σ^2*(Module.finrank ℝ E : ℝ) := by
  rw [phaseOUKernel_apply, integral_map (by unfold OBABOPath.ou; fun_prop)
    (a.flight_square_measurable h).aestronglyMeasurable]
  have he (ξ : E) : flightVelocity (gradient U) h (OBABOPath.ou r σ ξ z) =
      (r•z.2-(h/2)•gradient U z.1)+σ•ξ := by
    dsimp only [flightVelocity, OBABOPath.ou]
    simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  simp_rw [he]
  rw [stdGaussian_affine_norm_square]
  exact add_le_add (a.normalized_damped_flight_square hstar hzero hL hr z) le_rfl

theorem A1.ou_flight_second_integral {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hr : r^2 ≤ 1) (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    (∫ w, ‖flightVelocity (gradient U) h w‖^2 ∂phaseOUKernel r σ ∘ₘ μ) ≤
      (257/128:ℝ)*(∫ z, phaseEnergy U z ∂μ)+σ^2*(Module.finrank ℝ E : ℝ) := by
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  have hi : Integrable (fun w : E×E => ‖flightVelocity (gradient U) h w‖^2)
      (phaseOUKernel r σ ∘ₘ μ) := (a.kick_memLp hν (h/2)).snd.integrable_norm_pow'
  have hEc : Integrable (fun z : E×E => (257/128:ℝ)*phaseEnergy U z) μ := by
    simpa only [id_eq] using (a.phaseEnergy_integrable hμ).const_mul (257/128:ℝ)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  calc
    _ ≤ ∫ z, (257/128:ℝ)*phaseEnergy U z+σ^2*(Module.finrank ℝ E : ℝ) ∂μ :=
      integral_mono hi.integral_comp (hEc.add (integrable_const _))
        (a.ou_flight_second hstar hzero hL hr)
    _ = _ := by
      rw [integral_add hEc (integrable_const _),
        integral_const_mul, integral_const, probReal_univ, one_smul]

theorem A1.flight_square_le_modifiedEnergy {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64) (z : E×E) :
    ‖flightVelocity (gradient U) h z‖^2 ≤ (4.02:ℝ)*modifiedEnergy U h z := by
  have hf := a.normalized_flight_energy_bound hstar hzero hL z
  have hg := (lyapunov_energy_bounds a hstar hzero hL z).2.2.1
  have hn := a.normalized_energy_nonnegative hstar hzero z
  nlinarith

theorem A1.flight_square_secondMomentNorm {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 4 μ) :
    secondMomentNorm μ (fun z => ‖flightVelocity (gradient U) h z‖^2) ≤
      (4.02:ℝ)*secondMomentNorm μ (modifiedEnergy U h) := by
  have hG := a.modifiedEnergy_memLp_two hstar hzero hL μ hμ
  have hF : MemLp (fun z : E×E => ‖flightVelocity (gradient U) h z‖^2) 2 μ := by
    apply hG.of_le_mul (a.flight_square_measurable h).aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (a.modifiedEnergy_nonnegative hstar hzero hL z)] using
        a.flight_square_le_modifiedEnergy hstar hzero hL z
  have hs := Real.sq_sqrt (integral_nonneg (fun z => sq_nonneg (modifiedEnergy U h z)) (μ:=μ))
  unfold secondMomentNorm
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hb : (∫ z, (‖flightVelocity (gradient U) h z‖^2)^2 ∂μ) ≤
        (4.02:ℝ)^2*(∫ z, (modifiedEnergy U h z)^2 ∂μ) := by
      rw [← integral_const_mul]
      apply integral_mono hF.integrable_sq (hG.integrable_sq.const_mul ((4.02:ℝ)^2))
      intro z
      simpa only [mul_pow] using pow_le_pow_left₀ (sq_nonneg _)
        (a.flight_square_le_modifiedEnergy hstar hzero hL z) 2
    nlinarith

end PersistencePays
#print axioms PersistencePays.A1.ou_flight_second_integral
#print axioms PersistencePays.A1.flight_square_secondMomentNorm
