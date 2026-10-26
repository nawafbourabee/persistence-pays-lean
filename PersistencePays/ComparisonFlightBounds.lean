import PersistencePays.NoisyFlightMoments

/-! The actual comparison-chain flight moment bounds of Section 6. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem comparison_flight_secondMomentNorm
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E × E) (hz : phaseEnergy U z ≤ R) (n N : ℕ) (hn : n+1 ≤ N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
    secondMomentNorm (phaseOUKernel r σ ∘ₘ μ)
      (fun w => ‖flightVelocity (gradient U) h w‖^2) ≤
        (4.02:ℝ)*comparisonXi R (Module.finrank ℝ E) h N := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
  have hμ4 : MemLp id 4 μ := comparisonChainLaw_finite_moments a h r σ vstar n z 4 (by norm_num)
  have hν4 := phaseOUKernel_memLp μ 4 (by norm_num) hμ4 r σ
  have ht := a.flight_square_secondMomentNorm hstar hzero hL (phaseOUKernel r σ ∘ₘ μ) hν4
  have hb := (a.lemma_5_11_moments a2 hstar hzero hL hh hLH hscale z hz n N hn).2
  exact ht.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

theorem proposition_6_1_comparison_flight
    {U : E → ℝ} {L LH h vstar R Ψ : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (hΨ : 1 ≤ Ψ) (N : ℕ) (hN : 0 < N)
    (hΞΨ : comparisonXi R (Module.finrank ℝ E) h N ≤ Ψ)
    (hd : 41*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50+20*Real.log (2*(N:ℝ))+
      80*Real.log (Ψ/h)+922) ≤ vstar^2)
    (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (hn : n+1 ≤ N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
    let ν := phaseOUKernel r σ ∘ₘ μ
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫ w, ‖flightVelocity (gradient U) h w‖^2 ∂ν) ≤ (2.61:ℝ)*Q ∧
      secondMomentNorm ν (fun w => ‖flightVelocity (gradient U) h w‖^2) ≤
        (4.02:ℝ)*comparisonXi R (Module.finrank ℝ E) h N := by
  dsimp only
  refine ⟨?_, comparison_flight_secondMomentNorm a a2 hstar hzero hh hL hLH hscale z hz n N hn⟩
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
  have hμ2 : MemLp id 2 μ := comparisonChainLaw_finite_moments a h r σ vstar n z 2 (by norm_num)
  have hcoef := normalized_ou_coefficients h hh.le
  have hr : r^2 ≤ 1 := by
    have ht : r^2+σ^2=1 := hcoef.2.2.2.1
    nlinarith [sq_nonneg σ]
  have hσ : σ^2 ≤ 2*h := hcoef.2.2.2.2.2.2.2
  have ht := a.ou_flight_second_integral (σ:=σ) hstar hzero hL hr μ hμ2
  have henergy := proposition_6_1_comparison_energy a a2 hstar hzero hh hL hv hLH hscale hR
    hΨ N hN hΞΨ hd z hz n hn
  change (∫ w, phaseEnergy U w ∂μ) ≤ _ at henergy
  have hhsq := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
  have hhmax : h ≤ 1/8 := by nlinarith
  have hd0 := (Nat.cast_nonneg (Module.finrank ℝ E) : (0:ℝ) ≤ Module.finrank ℝ E)
  have hσd := mul_le_mul_of_nonneg_right hσ hd0
  have hhd := mul_le_mul_of_nonneg_right hhmax hd0
  nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_comparison_flight
