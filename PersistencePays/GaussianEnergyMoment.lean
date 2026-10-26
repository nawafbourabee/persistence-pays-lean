import PersistencePays.GaussianFourthMoment
import PersistencePays.OBABOPath

/-! Exact second moments for Gaussian affine kinetic energies. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integral_odd (f : E → ℝ) (hf : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂stdGaussian E) = 0 := by
  have hp : MeasurePreserving (fun x : E => -x) (stdGaussian E) (stdGaussian E) :=
    ⟨by fun_prop, stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  have hi := hp.integral_comp (Homeomorph.neg E).measurableEmbedding f
  simp_rw [hf] at hi
  rw [integral_neg] at hi
  linarith

theorem stdGaussian_inner_norm_square_integrable (b : E) :
    Integrable (fun x : E => ⟪b,x⟫*‖x‖^2) (stdGaussian E) := by
  have hn := ((IsGaussian.memLp_id (stdGaussian E) 3 (by norm_num)).integrable_norm_pow').const_mul ‖b‖
  apply hn.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  have hb := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm b x) (sq_nonneg ‖x‖)
  simp only [id_eq]
  nlinarith

theorem stdGaussian_quadratic_second (a c : ℝ) (b : E) :
    (∫ x : E, (a+⟪b,x⟫+c*‖x‖^2)^2 ∂stdGaussian E) =
      a^2+2*a*c*(Module.finrank ℝ E : ℝ)+‖b‖^2+
        c^2*(Module.finrank ℝ E : ℝ)*((Module.finrank ℝ E : ℝ)+2) := by
  have hlin : Integrable (fun x : E => ⟪b,x⟫) (stdGaussian E) :=
    ((innerSL ℝ b).comp_memLp' (IsGaussian.memLp_two_id (μ := stdGaussian E))).integrable (by norm_num)
  have hcross := stdGaussian_inner_norm_square_integrable b
  have hodd : Integrable (fun x : E => (2*a)*⟪b,x⟫+(2*c)*(⟪b,x⟫*‖x‖^2)) (stdGaussian E) :=
    (hlin.const_mul (2*a)).add (hcross.const_mul (2*c))
  have hbase : Integrable (fun x : E => a^2+(2*a*c)*‖x‖^2+c^2*‖x‖^4) (stdGaussian E) :=
    ((integrable_const (a^2) (μ := stdGaussian E)).add
    (stdGaussian_norm_square_integrable.const_mul (2*a*c))).add
      (stdGaussian_norm_fourth_integrable.const_mul (c^2))
  have hsq := stdGaussian_inner_square_integrable b
  have he : (fun x : E => (a+⟪b,x⟫+c*‖x‖^2)^2) =
      fun x => (a^2+(2*a*c)*‖x‖^2+c^2*‖x‖^4)+
        ((2*a)*⟪b,x⟫+(2*c)*(⟪b,x⟫*‖x‖^2))+⟪b,x⟫^2 := by
    funext x
    ring
  rw [he, integral_add (show Integrable (fun x : E =>
    (a^2+(2*a*c)*‖x‖^2+c^2*‖x‖^4)+((2*a)*⟪b,x⟫+(2*c)*(⟪b,x⟫*‖x‖^2)))
      (stdGaussian E) from hbase.add hodd) hsq, integral_add hbase hodd]
  rw [stdGaussian_integral_odd (fun x : E => (2*a)*⟪b,x⟫+(2*c)*(⟪b,x⟫*‖x‖^2))
      (by intro x; simp [inner_neg_right]; ring),
    stdGaussian_inner_square]
  rw [integral_add _ (stdGaussian_norm_fourth_integrable.const_mul (c^2)),
    integral_add (integrable_const _) (stdGaussian_norm_square_integrable.const_mul (2*a*c))]
  · simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      stdGaussian_norm_square, stdGaussian_norm_fourth]
    ring
  · exact (integrable_const _).add (stdGaussian_norm_square_integrable.const_mul (2*a*c))

theorem stdGaussian_affine_energy_second (A r σ : ℝ) (u : E) :
    (∫ ξ : E, (A+‖r•u+σ•ξ‖^2/2)^2 ∂stdGaussian E) =
      (A+r^2*‖u‖^2/2)^2 +
        (A+r^2*‖u‖^2/2)*σ^2*(Module.finrank ℝ E : ℝ)+
        r^2*σ^2*‖u‖^2+σ^4/4*(Module.finrank ℝ E : ℝ)*((Module.finrank ℝ E : ℝ)+2) := by
  have he (ξ : E) : A+‖r•u+σ•ξ‖^2/2 =
      (A+r^2*‖u‖^2/2)+⟪(r*σ)•u,ξ⟫+(σ^2/2)*‖ξ‖^2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [he]
  rw [stdGaussian_quadratic_second, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem stdGaussian_affine_energy_second_le (A r σ h : ℝ) (u : E)
    (hA : 0 ≤ A) (hr : r^2 ≤ 1) (hh : 0 ≤ h) (hσ : σ^2 ≤ 2*h) :
    (∫ ξ : E, (A+‖r•u+σ•ξ‖^2/2)^2 ∂stdGaussian E) ≤
      (A+‖u‖^2/2+h*((Module.finrank ℝ E : ℝ)+2))^2 := by
  rw [stdGaussian_affine_energy_second]
  let d : ℝ := Module.finrank ℝ E
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hu : 0 ≤ ‖u‖^2 := sq_nonneg _
  have hp : 0 ≤ A+r^2*‖u‖^2/2 := by positivity
  have hab : A+r^2*‖u‖^2/2 ≤ A+‖u‖^2/2 := by nlinarith
  have h1 := pow_le_pow_left₀ hp hab 2
  have h2 := mul_le_mul hab hσ (sq_nonneg σ) (show 0 ≤ A+‖u‖^2/2 by positivity)
  have h2' := mul_le_mul_of_nonneg_right h2 hd
  have h3 := mul_le_mul hr hσ (sq_nonneg σ) (by norm_num : (0:ℝ)≤1)
  have h3' := mul_le_mul_of_nonneg_right h3 hu
  have h4 := pow_le_pow_left₀ (sq_nonneg σ) hσ 2
  have h4' := mul_le_mul_of_nonneg_right h4 (show 0 ≤ d*(d+2) by positivity)
  change (A+r^2*‖u‖^2/2)^2+(A+r^2*‖u‖^2/2)*σ^2*d+r^2*σ^2*‖u‖^2+
    σ^4/4*d*(d+2) ≤ (A+‖u‖^2/2+h*(d+2))^2
  nlinarith [mul_nonneg hh hA, mul_nonneg (sq_nonneg h) hd]

end PersistencePays
#print axioms PersistencePays.stdGaussian_affine_energy_second
#print axioms PersistencePays.stdGaussian_affine_energy_second_le
