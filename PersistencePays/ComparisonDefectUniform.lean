import PersistencePays.ComparisonDefectMoment

/-! The actual cap-defect estimate of Section 6, with its numerical remainder. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem proposition_6_1_comparison_defect
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
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫ w, max (comparisonDefect U (gradient U) h vstar w) 0 ∂ν) ≤
      LH*h^3/12*((6.6:ℝ)*Q)^(3/2:ℝ) + (10:ℝ)^(-11:ℤ)*h := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let ν := phaseOUKernel r σ ∘ₘ comparisonChainLaw (gradient U) hg h r σ vstar n z
  let Ξ := comparisonXi R (Module.finrank ℝ E) h N
  let p := (gaussianBlock (n+2)).real (stoppedBlockEvent U (gradient U) h r σ vstar (n+2) z)ᶜ
  have hhsq : h^2 ≤ 1/64 := by
    have ht := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  have hhΨ : h ≤ Ψ := by nlinarith
  have he := proposition_6_1_exit a a2 hstar hzero hh hL hv hLH hscale hR hhΨ N hN hd z hz
  have hp := (stopped_prefix_exit_le a h r σ vstar hn z).trans he
  have hp' : p ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    have hpos : 0 ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by positivity
    rw [ENNReal.toReal_ofReal hpos] at ht
    exact ht
  have herr : Ξ*Real.sqrt p ≤ (10:ℝ)^(-10:ℤ)*h^2 := small_exit_weighted_sqrt
    (measureReal_nonneg : 0 ≤ p) hh hΨ (comparisonXi_nonneg hR hh.le _ _) hΞΨ hp'
  have hnorm := comparison_flight_secondMomentNorm a a2 hstar hzero hh hL hLH hscale z hz n N (by omega)
  have hm := comparison_positive_defect_moment a a2 hstar hzero hh.le hL hv hLH hscale hR z hz n
  change secondMomentNorm ν (fun w => ‖flightVelocity (gradient U) h w‖^2) ≤ (4.02:ℝ)*Ξ at hnorm
  apply hm.trans
  apply add_le_add le_rfl
  change (0.02:ℝ)*h*secondMomentNorm ν (fun w => ‖flightVelocity (gradient U) h w‖^2)*Real.sqrt p ≤ _
  calc
    _ ≤ (0.02:ℝ)*h*((4.02:ℝ)*Ξ)*Real.sqrt p := by gcongr
    _ = (0.0804:ℝ)*h*(Ξ*Real.sqrt p) := by ring
    _ ≤ (0.0804:ℝ)*h*((10:ℝ)^(-10:ℤ)*h^2) := mul_le_mul_of_nonneg_left herr (by positivity)
    _ ≤ _ := by
      have hs := mul_le_mul_of_nonneg_left hhsq hh.le
      norm_num
      nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_comparison_defect
