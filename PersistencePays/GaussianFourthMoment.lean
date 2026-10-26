import PersistencePays.GaussianSecondMoment
import Mathlib.Probability.Moments.MGFAnalytic

/-! Exact fourth norm moment of the actual standard Gaussian, obtained by
twice differentiating its already checked quadratic MGF. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem norm_square_mem_interior_integrableExpSet {t : ℝ} (ht : t < 1/2) :
    t ∈ interior (integrableExpSet (fun x : E => ‖x‖^2) (stdGaussian E)) := by
  apply mem_interior.mpr
  refine ⟨Iio (1/2), ?_, isOpen_Iio, ht⟩
  intro s hs
  change s < 1/2 at hs
  change Integrable (fun x : E => Real.exp (s*‖x‖^2)) (stdGaussian E)
  simpa only [inner_zero_left, zero_add, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using
    stdGaussian_quadratic_exp_integrable (E := E) (2*s) (by linarith) 0

theorem norm_square_mgf {t : ℝ} (ht : t < 1/2) :
    mgf (fun x : E => ‖x‖^2) (stdGaussian E) t =
      (1-2*t)^(-((Module.finrank ℝ E : ℝ)/2)) := by
  simpa only [mgf, inner_zero_left, zero_add, norm_zero,
    zero_pow (by decide : (2:ℕ)≠0), zero_div, Real.exp_zero, mul_one,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using
    stdGaussian_quadratic_mgf (E := E) (2*t) (by linarith) 0

theorem norm_square_exponential_moment {t : ℝ} (ht : t < 1/2) :
    (∫ x : E, ‖x‖^2*Real.exp (t*‖x‖^2) ∂stdGaussian E) =
      (Module.finrank ℝ E : ℝ)*(1-2*t)^(-((Module.finrank ℝ E : ℝ)/2)-1) := by
  have hd := hasDerivAt_mgf (norm_square_mem_interior_integrableExpSet (E := E) ht)
  have he : mgf (fun x : E => ‖x‖^2) (stdGaussian E) =ᶠ[𝓝 t]
      fun s => (1-2*s)^(-((Module.finrank ℝ E : ℝ)/2)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact norm_square_mgf hs
  rw [EventuallyEq.hasDerivAt_iff he] at hd
  have hd' := ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul 2)).rpow_const
    (p := -((Module.finrank ℝ E : ℝ)/2)) (Or.inl (by change 1-2*t≠0; linarith))
  have hu := hd.unique hd'
  dsimp only [Pi.sub_apply, id_eq] at hu
  convert hu using 1 <;> ring

theorem stdGaussian_norm_fourth :
    (∫ x : E, ‖x‖^4 ∂stdGaussian E) =
      (Module.finrank ℝ E : ℝ)*((Module.finrank ℝ E : ℝ)+2) := by
  have hd := hasDerivAt_integral_pow_mul_exp_real
    (norm_square_mem_interior_integrableExpSet (E := E) (t := 0) (by norm_num)) 1
  have he : (fun t => ∫ x : E, (‖x‖^2)^1*Real.exp (t*‖x‖^2) ∂stdGaussian E) =ᶠ[𝓝 (0:ℝ)]
      fun t => (Module.finrank ℝ E : ℝ)*(1-2*t)^(-((Module.finrank ℝ E : ℝ)/2)-1) := by
    filter_upwards [Iio_mem_nhds (show (0:ℝ)<1/2 by norm_num)] with t ht
    simpa only [pow_one] using norm_square_exponential_moment (E := E) ht
  rw [EventuallyEq.hasDerivAt_iff he] at hd
  have hd' := (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub ((hasDerivAt_id (0:ℝ)).const_mul 2)).rpow_const
    (p := -((Module.finrank ℝ E : ℝ)/2)-1) (Or.inl (by norm_num))).const_mul
      (Module.finrank ℝ E : ℝ)
  have hu := hd.unique hd'
  simp only [zero_mul, sub_zero, Real.one_rpow, Real.exp_zero, mul_one,
    pow_one, ← pow_mul] at hu
  norm_num at hu
  convert hu using 1 <;> ring

theorem stdGaussian_norm_fourth_integrable :
    Integrable (fun x : E => ‖x‖^4) (stdGaussian E) :=
  (IsGaussian.memLp_id (stdGaussian E) 4 (by norm_num)).integrable_norm_pow'

end PersistencePays
#print axioms PersistencePays.stdGaussian_norm_fourth
