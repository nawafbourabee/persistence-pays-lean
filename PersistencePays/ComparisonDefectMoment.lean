import PersistencePays.ComparisonCutoffProbability

/-! Actual positive comparison defects: stopped cubic error plus a small
exceptional quadratic contribution, with no assumed moment estimates. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.comparisonDefect_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h vstar : ℝ) : Measurable (comparisonDefect U (gradient U) h vstar) := by
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hU := a.twice_contDiff.continuous.measurable
  unfold comparisonDefect
  apply Measurable.ite
  · apply measurableSet_le
    · unfold flightVelocity; fun_prop
    · exact measurable_const
  · unfold trapezoidDefect verlet kick drift; fun_prop
  · exact measurable_const

theorem comparisonDefect_cubic_bound {U : E → ℝ} {L LH h vstar : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hh : 0 ≤ h) (hLH : 0 ≤ LH) (z : E×E) :
    max (comparisonDefect U (gradient U) h vstar z) 0 ≤
      LH*h^3/12*‖flightVelocity (gradient U) h z‖^3 := by
  apply max_le
  · by_cases hz : ‖flightVelocity (gradient U) h z‖ ≤ vstar
    · simp only [comparisonDefect,hz,ite_true]
      have ht := (lemma_2_1 a a2 hh z).2.2.1
      have ha := le_abs_self (trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h z).1)
      nlinarith
    · simp only [comparisonDefect,hz,ite_false]
      positivity
  · positivity

theorem comparisonDefect_positive_quadratic {U : E → ℝ} {L LH h vstar : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hh : 0 ≤ h) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h) (z : E×E) :
    max (comparisonDefect U (gradient U) h vstar z) 0 ≤
      (0.02:ℝ)*h*‖flightVelocity (gradient U) h z‖^2 :=
  max_le (comparisonDefect_bound a a2 hh hLH hscale z) (by positivity)

theorem A1.flight_square_memLp_two {U : E → ℝ} {L h : ℝ} (a : A1 U 1 L)
    (μ : Measure (E×E)) [IsFiniteMeasure μ] (hμ : MemLp id 4 μ) :
    MemLp (fun z => ‖flightVelocity (gradient U) h z‖^2) 2 μ := by
  have he : (4:ℝ≥0∞)/2=2 := by
    rw [show (4:ℝ≥0∞)=2*2 by norm_num, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  simpa [he, flightVelocity, kick] using (a.kick_memLp hμ (h/2)).snd.norm_rpow_div 2

namespace OBABOPath

theorem comparison_positive_defect_moment
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let ν := phaseOUKernel r σ ∘ₘ comparisonChainLaw (gradient U) hg h r σ vstar n z
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫ w, max (comparisonDefect U (gradient U) h vstar w) 0 ∂ν) ≤
      LH*h^3/12*((6.6:ℝ)*Q)^(3/2:ℝ) +
      (0.02:ℝ)*h*secondMomentNorm ν (fun w => ‖flightVelocity (gradient U) h w‖^2)*
        Real.sqrt ((gaussianBlock (n+2)).real
          (stoppedBlockEvent U (gradient U) h r σ vstar (n+2) z)ᶜ) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let ν := phaseOUKernel r σ ∘ₘ comparisonChainLaw (gradient U) hg h r σ vstar n z
  let W := comparisonPreEndpoint (gradient U) h r σ vstar n z
  let A := stoppedBlockEvent U (gradient U) h r σ vstar (n+2) z
  let F : NoiseBlock E (n+2) → ℝ := fun b => max (comparisonDefect U (gradient U) h vstar (W b)) 0
  let G : NoiseBlock E (n+2) → ℝ := fun b => ‖flightVelocity (gradient U) h (W b)‖^2
  have hW : Measurable W := measurable_comparisonPreEndpoint (gradient U) hg h r σ vstar n z
  have hmap : (gaussianBlock (n+2)).map W = ν := comparison_pre_endpoint_law (gradient U) hg h r σ vstar n z
  have hν4 : MemLp id 4 ν := phaseOUKernel_memLp _ 4 (by norm_num)
    (comparisonChainLaw_finite_moments a h r σ vstar n z 4 (by norm_num)) r σ
  have hGν := a.flight_square_memLp_two (h:=h) ν hν4
  have hG : MemLp G 2 (gaussianBlock (n+2)) := by
    apply (memLp_map_measure_iff (a.flight_square_measurable h).aestronglyMeasurable hW.aemeasurable).mp
    rwa [hmap]
  have hFbase : Measurable (fun w => max (comparisonDefect U (gradient U) h vstar w) 0) :=
    (a.comparisonDefect_measurable h vstar).max measurable_const
  have hF : Measurable F := hFbase.comp hW
  have hF0 (b : NoiseBlock E (n+2)) : 0 ≤ F b := le_max_right _ _
  have hG0 (b : NoiseBlock E (n+2)) : 0 ≤ G b := sq_nonneg _
  have hbound (b : NoiseBlock E (n+2)) : F b ≤ ((0.02:ℝ)*h)*G b :=
    comparisonDefect_positive_quadratic a a2 hh hLH hscale (W b)
  have hFi : Integrable F (gaussianBlock (n+2)) :=
    ((hG.integrable (by norm_num)).const_mul ((0.02:ℝ)*h)).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 b)] using hbound b)
  have hA := stoppedBlockEvent_measurable a h r σ vstar (n+2) z
  have ht := exceptional_event_expectation (gaussianBlock (n+2)) F G F hF hG hF0 hG0
    ((0.02:ℝ)*h) (by positivity) hbound A hA (fun _ _ => rfl)
  have hcubic := stopped_lastFlight_third_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz (n+1)
  have hr : r^2 ≤ 1 := by
    have ht : r^2+σ^2=1 := (normalized_ou_coefficients h hh).2.2.2.1
    nlinarith [sq_nonneg σ]
  have hfirst : (∫ b in A, F b ∂gaussianBlock (n+2)) ≤
      LH*h^3/12*((6.6:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50))^(3/2:ℝ) := by
    calc
      _ ≤ ∫ b in A, LH*h^3/12*‖lastFlight (gradient U) h r σ (n+1) z b‖^3 ∂gaussianBlock (n+2) := by
        apply setIntegral_mono_on hFi.integrableOn (hcubic.1.const_mul (LH*h^3/12)) hA
        intro b hb
        have hb' := comparisonDefect_cubic_bound (vstar:=vstar) a a2 hh hLH (W b)
        rw [comparison_pre_flight_agree a hstar hzero hL hr hv n z b hb] at hb'
        exact hb'
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hcubic.2 (by positivity)
  have heF : (∫ b, F b ∂gaussianBlock (n+2)) =
      ∫ w, max (comparisonDefect U (gradient U) h vstar w) 0 ∂ν := by
    rw [← hmap, integral_map hW.aemeasurable hFbase.aestronglyMeasurable]
  have heG : secondMomentNorm (gaussianBlock (n+2)) G =
      secondMomentNorm ν (fun w => ‖flightVelocity (gradient U) h w‖^2) := by
    unfold secondMomentNorm
    rw [← hmap, integral_map hW.aemeasurable
      ((a.flight_square_measurable h).pow_const 2).aestronglyMeasurable]
  rw [heF, heG] at ht
  exact ht.trans (add_le_add hfirst le_rfl)

end OBABOPath
end PersistencePays
#print axioms PersistencePays.OBABOPath.comparison_positive_defect_moment
