import PersistencePays.ComparisonDefectUniform
import PersistencePays.ComparisonCutoffProbability

/-! Actual cutoff-event moments for the capped comparison chain. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.cutoff_energy_bound {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64) (z : E×E) :
    2*U z.1+‖flightVelocity (gradient U) h z‖^2 ≤ (6.1:ℝ)*modifiedEnergy U h z := by
  have hf := a.flight_square_le_modifiedEnergy hstar hzero hL z
  have hg := (lyapunov_energy_bounds a hstar hzero hL z).2.2.1
  have hG := a.modifiedEnergy_nonnegative hstar hzero hL z
  dsimp only [phaseEnergy] at hg
  rw [real_inner_self_eq_norm_sq] at hg
  nlinarith [sq_nonneg ‖z.2‖]

theorem A1.cutoff_set_moments {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 4 μ)
    (A : Set (E×E)) (hA : MeasurableSet A) :
    (∫ z in A, ‖flightVelocity (gradient U) h z‖^2 ∂μ) ≤
        (4.02:ℝ)*secondMomentNorm μ (modifiedEnergy U h)*Real.sqrt (μ.real A) ∧
    (∫ z in A, 2*U z.1+‖flightVelocity (gradient U) h z‖^2 ∂μ) ≤
        (6.1:ℝ)*secondMomentNorm μ (modifiedEnergy U h)*Real.sqrt (μ.real A) := by
  have hG := a.modifiedEnergy_memLp_two hstar hzero hL μ hμ
  have hGi := hG.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hF := (a.flight_square_memLp_two (h:=h) μ hμ).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hμ2 : MemLp id 2 μ := hμ.mono_exponent (by norm_num)
  have hU : Integrable (fun z : E×E => U z.1) μ := a.potential_integrable hμ2.fst
  have htail := setIntegral_le_secondMomentNorm μ (modifiedEnergy U h) hG
    (a.modifiedEnergy_nonnegative hstar hzero hL) A hA
  constructor
  · calc
      _ ≤ ∫ z in A, (4.02:ℝ)*modifiedEnergy U h z ∂μ := integral_mono hF.integrableOn
        (hGi.const_mul _).integrableOn (a.flight_square_le_modifiedEnergy hstar hzero hL)
      _ = (4.02:ℝ)*(∫ z in A, modifiedEnergy U h z ∂μ) := integral_const_mul _ _
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ∫ z in A, (6.1:ℝ)*modifiedEnergy U h z ∂μ := integral_mono
        ((hU.const_mul 2).add hF).integrableOn (hGi.const_mul _).integrableOn
          (a.cutoff_energy_bound hstar hzero hL)
      _ = (6.1:ℝ)*(∫ z in A, modifiedEnergy U h z ∂μ) := integral_const_mul _ _
      _ ≤ _ := by nlinarith

namespace OBABOPath

theorem proposition_6_1_cutoff_moments
    {U : E → ℝ} {L LH h vstar R Ψ : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (hΨ : 1 ≤ Ψ) (N : ℕ) (hN : 0 < N)
    (hΞΨ : comparisonXi R (Module.finrank ℝ E) h N ≤ Ψ)
    (hd : 41*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50+20*Real.log (2*(N:ℝ))+
      80*Real.log (Ψ/h)+922) ≤ vstar^2)
    (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (hn : n+2 ≤ N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let ν := phaseOUKernel r σ ∘ₘ comparisonChainLaw (gradient U) hg h r σ vstar n z
    let F := {w | vstar < ‖flightVelocity (gradient U) h w‖}
    ν.real F ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 ∧
      (∫ w in F, ‖flightVelocity (gradient U) h w‖^2 ∂ν) ≤ (4.1:ℝ)*(10:ℝ)^(-10:ℤ)*h^2 ∧
      (∫ w in F, 2*U w.1+‖flightVelocity (gradient U) h w‖^2 ∂ν) ≤
        (6.1:ℝ)*(10:ℝ)^(-10:ℤ)*h^2 := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
  let ν := phaseOUKernel r σ ∘ₘ μ
  let Ξ := comparisonXi R (Module.finrank ℝ E) h N
  let F := {w | vstar < ‖flightVelocity (gradient U) h w‖}
  have hhsq : h^2 ≤ 1/64 := by
    have ht := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  have hhΨ : h ≤ Ψ := by nlinarith
  have hcoef := normalized_ou_coefficients h hh.le
  have hr : r^2 ≤ 1 := by
    have ht : r^2+σ^2=1 := hcoef.2.2.2.1
    nlinarith [sq_nonneg σ]
  have he := proposition_6_1_exit a a2 hstar hzero hh hL hv hLH hscale hR hhΨ N hN hd z hz
  have hp := (comparison_cutoff_probability a hstar hzero hL hr hv n z).trans
    ((stopped_prefix_exit_le a h r σ vstar hn z).trans he)
  have hp' : ν.real F ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    have hpos : 0 ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by positivity
    rw [ENNReal.toReal_ofReal hpos] at ht
    exact ht
  have herr : Ξ*Real.sqrt (ν.real F) ≤ (10:ℝ)^(-10:ℤ)*h^2 := small_exit_weighted_sqrt
    measureReal_nonneg hh hΨ (comparisonXi_nonneg hR hh.le _ _) hΞΨ hp'
  have hμ4 : MemLp id 4 μ := comparisonChainLaw_finite_moments a h r σ vstar n z 4 (by norm_num)
  have hν4 := phaseOUKernel_memLp μ 4 (by norm_num) hμ4 r σ
  have hF : MeasurableSet F := measurableSet_lt measurable_const (by unfold flightVelocity; fun_prop)
  have htail := a.cutoff_set_moments hstar hzero hL ν hν4 F hF
  have hnorm := (a.lemma_5_11_moments a2 hstar hzero hL hh hLH hscale z hz n N (by omega)).2
  change secondMomentNorm ν (modifiedEnergy U h) ≤ Ξ at hnorm
  have hb := mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg (ν.real F))
  obtain ⟨htail1, htail2⟩ := htail
  refine ⟨hp',?_,?_⟩
  · change (∫ w in F, ‖flightVelocity (gradient U) h w‖^2 ∂ν) ≤ _
    norm_num at herr ⊢
    nlinarith [sq_nonneg h]
  · change (∫ w in F, 2*U w.1+‖flightVelocity (gradient U) h w‖^2 ∂ν) ≤ _
    norm_num at herr ⊢
    nlinarith [sq_nonneg h]

end OBABOPath
end PersistencePays
#print axioms PersistencePays.OBABOPath.proposition_6_1_cutoff_moments
