import PersistencePays.SecondMomentKernel
import PersistencePays.GaussianEnergyMoment

/-! Actual quantitative modified-energy moments for the comparison chain. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.modifiedEnergy_measurable {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (h : ℝ) :
    Measurable (modifiedEnergy U h) := by
  have hU := a.twice_contDiff.continuous.measurable
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  unfold modifiedEnergy phaseEnergy gradientCorrection
  fun_prop

theorem A1.modifiedEnergy_nonnegative {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64) (z : E×E) :
    0 ≤ modifiedEnergy U h z := by
  have hb := (lyapunov_energy_bounds a hstar hzero hL z).2.2.1
  have hH := a.normalized_energy_nonnegative hstar hzero z
  nlinarith

theorem A1.modifiedEnergy_quadratic_bound {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64) (z : E×E) :
    ‖modifiedEnergy U h z‖ ≤ L*‖z‖^2 := by
  rw [Real.norm_of_nonneg (a.modifiedEnergy_nonnegative hstar hzero hL z)]
  have hb := (lyapunov_energy_bounds a hstar hzero hL z).2.2.2
  have hu := a.potential_upper_at_minimizer z.1
  simp only [hstar, hzero, sub_zero] at hu
  have hx := pow_le_pow_left₀ (norm_nonneg z.1) (norm_fst_le z) 2
  have hv := pow_le_pow_left₀ (norm_nonneg z.2) (norm_snd_le z) 2
  have hxx := mul_le_mul_of_nonneg_left hx a.L_pos.le
  have hLL := mul_le_mul_of_nonneg_right a.m_le_L (sq_nonneg ‖z‖)
  rw [phaseEnergy_eq_norm] at hb
  nlinarith

theorem A1.modifiedEnergy_memLp_two {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (μ : Measure (E×E)) (hμ : MemLp id 4 μ) : MemLp (modifiedEnergy U h) 2 μ := by
  have hm : MemLp (fun z : E×E => ‖z‖^2) 2 μ := by
    have he : (4:ℝ≥0∞)/2=2 := by
      rw [show (4:ℝ≥0∞)=2*2 by norm_num, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
    simpa [he] using hμ.norm_rpow_div 2
  apply hm.of_le_mul (a.modifiedEnergy_measurable h).aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_of_nonneg (sq_nonneg ‖z‖)] using
    a.modifiedEnergy_quadratic_bound hstar hzero hL z

theorem A1.ou_modifiedEnergy_second {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h) (z : E×E) :
    (∫ w, (modifiedEnergy U h w)^2 ∂phaseOUKernel r σ z) ≤
      (modifiedEnergy U h z+h*((Module.finrank ℝ E : ℝ)+2))^2 := by
  rw [phaseOUKernel_apply, integral_map (by unfold OBABOPath.ou; fun_prop)
    ((a.modifiedEnergy_measurable h).pow_const 2).aestronglyMeasurable]
  have hA : 0 ≤ U z.1-gradientCorrection (gradient U) h z.1 := by
    have hg := a.normalized_correction_bound hstar hzero hL z.1
    have hu := a.normalized_potential_nonnegative hstar hzero z.1
    linarith
  have hb := stdGaussian_affine_energy_second_le
    (U z.1-gradientCorrection (gradient U) h z.1) r σ h z.2 hA hr hh hσ
  convert hb using 1
  · congr 1
    funext ξ
    dsimp only [OBABOPath.ou, modifiedEnergy]
    rw [phaseEnergy_eq_norm]
    ring
  · unfold modifiedEnergy
    rw [phaseEnergy_eq_norm]
    ring

theorem A1.ou_modifiedEnergy_norm {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 4 μ) :
    secondMomentNorm (phaseOUKernel r σ ∘ₘ μ) (modifiedEnergy U h) ≤
      secondMomentNorm μ (modifiedEnergy U h)+h*((Module.finrank ℝ E : ℝ)+2) := by
  apply secondMomentNorm_kernel μ (modifiedEnergy U h) (phaseOUKernel r σ)
    _ (by positivity) (a.modifiedEnergy_memLp_two hstar hzero hL μ hμ)
    (a.modifiedEnergy_memLp_two hstar hzero hL _
      (phaseOUKernel_memLp μ 4 (by norm_num) hμ r σ))
  exact a.ou_modifiedEnergy_second hstar hzero hL hh hr hσ

theorem A1.verlet_modifiedEnergy_growth {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64) (z : E×E) :
    modifiedEnergy U h (verlet (gradient U) h z) ≤ (1.008:ℝ)*modifiedEnergy U h z := by
  have he := verlet_energy_identity U (gradient U) h z
  have ht := verlet_trapezoidDefect_bound U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian L h
    (fun x u => ⟨a.nonnegative_hessian x u, a.upper x u⟩) z
  have hf := a.normalized_flight_energy_bound hstar hzero hL z
  have hs := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖flightVelocity (gradient U) h z‖)
  have hb := (lyapunov_energy_bounds a hstar hzero hL z).2.2.1
  have hH := a.normalized_energy_nonnegative hstar hzero z
  have hn := le_abs_self (trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h z).1)
  unfold modifiedEnergy at hb ⊢
  nlinarith

theorem A1.sandwich_modifiedEnergy_norm {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 4 μ)
    (D : E×E → E×E) (hD : Measurable D) (c : ℝ) (hc : 0 ≤ c)
    (hmD : MemLp D 4 (phaseOUKernel r σ ∘ₘ μ))
    (hgD : ∀ z, modifiedEnergy U h (D z) ≤ c*modifiedEnergy U h z) :
    secondMomentNorm (gaussianSandwichKernel D hD r σ ∘ₘ μ) (modifiedEnergy U h) ≤
      c*(secondMomentNorm μ (modifiedEnergy U h)+h*((Module.finrank ℝ E : ℝ)+2))+
        h*((Module.finrank ℝ E : ℝ)+2) := by
  have hO := phaseOUKernel_memLp μ 4 (by norm_num) hμ r σ
  have hM : MemLp id 4 ((phaseOUKernel r σ ∘ₘ μ).map D) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hD.aemeasurable).mpr hmD
  have h₁ := a.ou_modifiedEnergy_norm hstar hzero hL hh hr hσ μ hμ
  have h₂ := secondMomentNorm_map_le (phaseOUKernel r σ ∘ₘ μ) (modifiedEnergy U h)
    hD c hc (a.modifiedEnergy_memLp_two hstar hzero hL _ hO)
    (a.modifiedEnergy_memLp_two hstar hzero hL _ hM)
    (a.modifiedEnergy_nonnegative hstar hzero hL) hgD
  letI : IsProbabilityMeasure ((phaseOUKernel r σ ∘ₘ μ).map D) :=
    Measure.isProbabilityMeasure_map hD.aemeasurable
  have h₃ := a.ou_modifiedEnergy_norm hstar hzero hL hh hr hσ _ hM
  rw [gaussianSandwichKernel_comp]
  nlinarith [mul_le_mul_of_nonneg_left h₁ hc]

theorem A1.unadjusted_modifiedEnergy_norm {U : E → ℝ} {L h r σ : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 4 μ) :
    secondMomentNorm (OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ ∘ₘ μ)
      (modifiedEnergy U h) ≤
      (1.008:ℝ)*(secondMomentNorm μ (modifiedEnergy U h)+h*((Module.finrank ℝ E : ℝ)+2))+
        h*((Module.finrank ℝ E : ℝ)+2) := by
  rw [unadjustedStepKernel_eq_sandwich]
  exact a.sandwich_modifiedEnergy_norm hstar hzero hL hh hr hσ μ hμ _ _ _ (by norm_num)
    (a.verlet_memLp (phaseOUKernel_memLp μ 4 (by norm_num) hμ r σ) h)
    (a.verlet_modifiedEnergy_growth hstar hzero hL)

theorem A1.comparison_modifiedEnergy_norm {U : E → ℝ} {L LH h r σ vstar : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (hLH : 0 ≤ LH) (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 4 μ) :
    let e := comparisonVerletEquiv (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar
    secondMomentNorm (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ) (modifiedEnergy U h) ≤
      (1+(0.081:ℝ)*h)*(secondMomentNorm μ (modifiedEnergy U h)+
        h*((Module.finrank ℝ E : ℝ)+2))+h*((Module.finrank ℝ E : ℝ)+2) := by
  dsimp only
  apply a.sandwich_modifiedEnergy_norm hstar hzero hL hh hr hσ μ hμ _ _ _ (by positivity)
    (a.comparisonVerlet_memLp (phaseOUKernel_memLp μ 4 (by norm_num) hμ r σ) h vstar)
  exact comparisonVerlet_modifiedEnergy_growth a a2 hstar hzero hh hL hLH hscale

end PersistencePays
#print axioms PersistencePays.A1.ou_modifiedEnergy_norm
#print axioms PersistencePays.A1.verlet_modifiedEnergy_growth
