import PersistencePays.StoppedMomentConversion

/-! The third flight moment in Lemma 5.6(v).  A deliberately coarse Gaussian
moment estimate suffices for the exact final constant `6.6`. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sq_rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : (x^2)^(3/2:ℝ)=x^3 := by
  rw [Real.rpow_div_two_eq_sqrt 3 (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_nonneg hx]
  norm_num

theorem cube_le_rpow_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x^2 ≤ y) :
    x^3 ≤ y^(3/2:ℝ) := by
  rw [← sq_rpow_three_halves x hx]
  exact Real.rpow_le_rpow (sq_nonneg _) hxy (by norm_num)

/-- A coarse, dimension-linear square-Gaussian log-MGF bound. -/
theorem stdGaussian_small_norm_mgf :
    (∫⁻ x : E, ENNReal.ofReal (Real.exp ((1/20:ℝ)*‖x‖^2)) ∂stdGaussian E) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*(2*(Module.finrank ℝ E : ℝ)))) := by
  have hi : Integrable (fun x : E => Real.exp ((1/20:ℝ)*‖x‖^2)) (stdGaussian E) := by
    simpa only [inner_zero_left, zero_add, show (1/10:ℝ)/2=1/20 by norm_num] using
      stdGaussian_quadratic_exp_integrable (E := E) (1/10) (by norm_num) 0
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have he := stdGaussian_quadratic_mgf_exp (E := E) (1/10) (by norm_num) 0
  simp only [inner_zero_left, zero_add, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0),
    zero_div, add_zero, show (1/10:ℝ)/2=1/20 by norm_num] at he
  rw [he]
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(1-(1/10:ℝ))⁻¹)
  rw [Real.log_inv] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ (Module.finrank ℝ E : ℝ)/2 by positivity)
  norm_num at hm
  nlinarith

/-- This weaker Gaussian third-moment bound is enough to preserve `6.6`. -/
theorem stdGaussian_third_norm_lintegral :
    (∫⁻ x : E, ENNReal.ofReal (‖x‖^3) ∂stdGaussian E) ≤
      ENNReal.ofReal ((2*(Module.finrank ℝ E : ℝ)+40)^(3/2:ℝ)) := by
  have h2 := exponential_second_moment (stdGaussian E) (by simp) (fun x : E => ‖x‖^2)
    (by fun_prop) (fun x => sq_nonneg ‖x‖) (2*(Module.finrank ℝ E : ℝ)) (by positivity)
    (stdGaussian_small_norm_mgf (E := E))
  have hp := lintegral_rpow_le_second_moment (stdGaussian E) (by simp)
    (fun x : E => ENNReal.ofReal (‖x‖^2)) (by fun_prop) (3/2) (by norm_num) (by norm_num)
  have he (x : E) : ENNReal.ofReal (‖x‖^2)^(3/2:ℝ) = ENNReal.ofReal (‖x‖^3) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), sq_rpow_three_halves _ (norm_nonneg _)]
  have he2 (x : E) := ENNReal.ofReal_pow (sq_nonneg ‖x‖) 2
  simp only [he, ← he2] at hp
  apply hp.trans
  calc
    _ ≤ ENNReal.ofReal ((2*(Module.finrank ℝ E : ℝ)+40)^2)^((3/2:ℝ)/2) :=
      ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

/-- The numerical inequality used after splitting the cubed flight speed. -/
theorem flight_third_constant (Q : ℝ) (hQ : 0 ≤ Q) :
    4*(((2.55:ℝ)*Q)^(3/2:ℝ)+((0.2:ℝ)*Q)^(3/2:ℝ)) ≤ ((6.6:ℝ)*Q)^(3/2:ℝ) := by
  rw [Real.mul_rpow (by norm_num) hQ, Real.mul_rpow (by norm_num) hQ, Real.mul_rpow (by norm_num) hQ]
  have hc : 4*((2.55:ℝ)^(3/2:ℝ)+(0.2:ℝ)^(3/2:ℝ)) ≤ (6.6:ℝ)^(3/2:ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt 3 (by norm_num : (0:ℝ) ≤ 2.55),
      Real.rpow_div_two_eq_sqrt 3 (by norm_num : (0:ℝ) ≤ 0.2),
      Real.rpow_div_two_eq_sqrt 3 (by norm_num : (0:ℝ) ≤ 6.6)]
    norm_num only [Real.rpow_natCast]
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num]
    simp only [Real.rpow_natCast]
    have ha := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 51/20)
    have hb := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/5)
    have hc := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 33/5)
    have hap : 0 ≤ Real.sqrt (51/20:ℝ) := Real.sqrt_nonneg _
    have hbp : 0 ≤ Real.sqrt (1/5:ℝ) := Real.sqrt_nonneg _
    have hcp : 0 ≤ Real.sqrt (33/5:ℝ) := Real.sqrt_nonneg _
    have haa : Real.sqrt (51/20:ℝ) ≤ 1.6 := by nlinarith
    have hbb : Real.sqrt (1/5:ℝ) ≤ 0.45 := by nlinarith
    have hcc : 2.56 ≤ Real.sqrt (33/5:ℝ) := by nlinarith
    have h3a := congrArg (fun t : ℝ => t*Real.sqrt (51/20:ℝ)) ha
    have h3b := congrArg (fun t : ℝ => t*Real.sqrt (1/5:ℝ)) hb
    have h3c := congrArg (fun t : ℝ => t*Real.sqrt (33/5:ℝ)) hc
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hQ (3/2))
  nlinarith

/-- Third moment of the damped deterministic part of the actual flight. -/
theorem damped_flight_third_lintegral {U : E → ℝ} {L h r Q : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1)
    (ν : Measure (E×E)) (hQ : 0 ≤ Q)
    (hmom : (∫⁻ z, ENNReal.ofReal ((phaseEnergy U z)^(3/2:ℝ)) ∂ν) ≤
      ENNReal.ofReal (((1.266:ℝ)*Q)^(3/2:ℝ))) :
    (∫⁻ z, ENNReal.ofReal (‖r•z.2-(h/2)•gradient U z.1‖^3) ∂ν) ≤
      ENNReal.ofReal (((2.55:ℝ)*Q)^(3/2:ℝ)) := by
  have hU := a.twice_contDiff.continuous.measurable
  have hHp (z : E×E) := a.normalized_energy_nonnegative hstar hzero z
  have hH : Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (((257/128:ℝ)*phaseEnergy U z)^(3/2:ℝ)) ∂ν :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (cube_le_rpow_of_sq_le (norm_nonneg _)
        (a.normalized_damped_flight_square hstar hzero hL hr z)))
    _ = ENNReal.ofReal ((257/128:ℝ)^(3/2:ℝ))*
        (∫⁻ z, ENNReal.ofReal ((phaseEnergy U z)^(3/2:ℝ)) ∂ν) := by
      have he (z : E×E) : ((257/128:ℝ)*phaseEnergy U z)^(3/2:ℝ) =
          (257/128:ℝ)^(3/2:ℝ)*(phaseEnergy U z)^(3/2:ℝ) :=
        Real.mul_rpow (by norm_num) (hHp z)
      simp_rw [he, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 257/128) (3/2))]
      exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal ((257/128:ℝ)^(3/2:ℝ))*ENNReal.ofReal (((1.266:ℝ)*Q)^(3/2:ℝ)) :=
      mul_le_mul' le_rfl hmom
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
        ← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 257/128) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      nlinarith

/-- A Gaussian-noise estimate with enough slack for the paper's final constant. -/
theorem gaussian_noise_third_lintegral (σ Q : ℝ) (hσ : σ^2 ≤ 1/4)
    (hQ : 27*(Module.finrank ℝ E : ℝ)+50 ≤ Q) :
    (∫⁻ ξ : E, ENNReal.ofReal (‖σ•ξ‖^3) ∂stdGaussian E) ≤
      ENNReal.ofReal (((0.2:ℝ)*Q)^(3/2:ℝ)) := by
  have hB : 0 ≤ 2*(Module.finrank ℝ E : ℝ)+40 := by positivity
  have he : |σ|^3*(2*(Module.finrank ℝ E : ℝ)+40)^(3/2:ℝ) =
      (σ^2*(2*(Module.finrank ℝ E : ℝ)+40))^(3/2:ℝ) := by
    rw [Real.mul_rpow (sq_nonneg _) hB]
    rw [← sq_abs σ, sq_rpow_three_halves _ (abs_nonneg _)]
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) _)]
  rw [lintegral_const_mul _ (by fun_prop)]
  calc
    _ ≤ ENNReal.ofReal (|σ|^3)*ENNReal.ofReal ((2*(Module.finrank ℝ E : ℝ)+40)^(3/2:ℝ)) :=
      mul_le_mul' le_rfl (stdGaussian_third_norm_lintegral (E := E))
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) _), he]
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      have hh := mul_le_mul_of_nonneg_right hσ hB
      have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := by positivity
      nlinarith

theorem norm_add_cube_bound (u v : E) : ‖u+v‖^3 ≤ 4*(‖u‖^3+‖v‖^3) := by
  have ht := pow_le_pow_left₀ (norm_nonneg (u+v)) (norm_add_le u v) 3
  have hp := mul_nonneg (sq_nonneg (‖u‖-‖v‖)) (add_nonneg (norm_nonneg u) (norm_nonneg v))
  nlinarith

/-- Full actual flight moment under a killed state law and the next independent
Gaussian noise. Dropping further good-noise/energy indicators only enlarges this integral. -/
theorem noisy_flight_third_lintegral {U : E → ℝ} {L h r σ Q : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 1/4)
    (ν : Measure (E×E)) [IsFiniteMeasure ν] (hmass : ν univ ≤ 1)
    (hQ : 27*(Module.finrank ℝ E : ℝ)+50 ≤ Q)
    (hmom : (∫⁻ z, ENNReal.ofReal ((phaseEnergy U z)^(3/2:ℝ)) ∂ν) ≤
      ENNReal.ofReal (((1.266:ℝ)*Q)^(3/2:ℝ))) :
    (∫⁻ p : (E×E)×E, ENNReal.ofReal
      (‖flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)‖^3)
        ∂ν.prod (stdGaussian E)) ≤ ENNReal.ofReal (((6.6:ℝ)*Q)^(3/2:ℝ)) := by
  let A : E×E → E := fun z => r•z.2-(h/2)•gradient U z.1
  let B : E → E := fun ξ => σ•ξ
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hQpos : 0 ≤ Q := by
    have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := by positivity
    linarith
  have ha := damped_flight_third_lintegral a hstar hzero hL hr ν hQpos hmom
  have hb := gaussian_noise_third_lintegral (E := E) σ Q hσ hQ
  have hIfst : (∫⁻ p : (E×E)×E, ENNReal.ofReal (‖A p.1‖^3) ∂ν.prod (stdGaussian E)) =
      ∫⁻ z, ENNReal.ofReal (‖A z‖^3) ∂ν := by
    rw [← lintegral_map (show Measurable (fun z : E×E => ENNReal.ofReal (‖A z‖^3)) by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hIsnd : (∫⁻ p : (E×E)×E, ENNReal.ofReal (‖B p.2‖^3) ∂ν.prod (stdGaussian E)) =
      ν univ*(∫⁻ ξ, ENNReal.ofReal (‖B ξ‖^3) ∂stdGaussian E) := by
    rw [← lintegral_map (show Measurable (fun ξ : E => ENNReal.ofReal (‖B ξ‖^3)) by fun_prop) measurable_snd, Measure.map_snd_prod, lintegral_smul_measure, smul_eq_mul]
  have hflight (p : (E×E)×E) : flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)=A p.1+B p.2 := by
    dsimp [A, B, flightVelocity, OBABOPath.ou]
    module
  calc
    _ ≤ ∫⁻ p : (E×E)×E, ENNReal.ofReal 4*
        (ENNReal.ofReal (‖A p.1‖^3)+ENNReal.ofReal (‖B p.2‖^3)) ∂ν.prod (stdGaussian E) := by
      apply lintegral_mono
      intro p
      dsimp only
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), hflight]
      exact ENNReal.ofReal_le_ofReal (norm_add_cube_bound _ _)
    _ = ENNReal.ofReal 4*((∫⁻ z, ENNReal.ofReal (‖A z‖^3) ∂ν)+
        ν univ*(∫⁻ ξ, ENNReal.ofReal (‖B ξ‖^3) ∂stdGaussian E)) := by
      rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop), hIfst, hIsnd]
    _ ≤ ENNReal.ofReal 4*(ENNReal.ofReal (((2.55:ℝ)*Q)^(3/2:ℝ))+
        ENNReal.ofReal (((0.2:ℝ)*Q)^(3/2:ℝ))) := by
      apply mul_le_mul' le_rfl
      apply add_le_add ha
      exact (mul_le_mul' hmass hb).trans_eq (one_mul _)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      exact ENNReal.ofReal_le_ofReal (flight_third_constant Q hQpos)

/-- Real-valued version of Lemma 5.6(v), including any additional stopping event.
Both the finite moment and its integrability are conclusions. -/
theorem noisy_flight_third_moment {U : E → ℝ} {L h r σ Q : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 1/4)
    (ν : Measure (E×E)) [IsFiniteMeasure ν] (hmass : ν univ ≤ 1)
    (hQ : 27*(Module.finrank ℝ E : ℝ)+50 ≤ Q)
    (hmom : (∫⁻ z, ENNReal.ofReal ((phaseEnergy U z)^(3/2:ℝ)) ∂ν) ≤
      ENNReal.ofReal (((1.266:ℝ)*Q)^(3/2:ℝ))) (B : Set ((E×E)×E)) :
    Integrable (fun p : (E×E)×E => ‖flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)‖^3)
      ((ν.prod (stdGaussian E)).restrict B) ∧
    (∫ p : (E×E)×E, ‖flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)‖^3
      ∂(ν.prod (stdGaussian E)).restrict B) ≤ ((6.6:ℝ)*Q)^(3/2:ℝ) := by
  have hb0 := noisy_flight_third_lintegral a hstar hzero hL hr hσ ν hmass hQ hmom
  have hb : (∫⁻ p : (E×E)×E, ENNReal.ofReal
      (‖flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)‖^3)
        ∂(ν.prod (stdGaussian E)).restrict B) ≤ ENNReal.ofReal (((6.6:ℝ)*Q)^(3/2:ℝ)) :=
    (lintegral_mono' Measure.restrict_le_self le_rfl).trans hb0
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hm : Measurable (fun p : (E×E)×E =>
      ‖flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)‖^3) := by
    unfold flightVelocity OBABOPath.ou
    fun_prop
  have hn (p : (E×E)×E) : 0 ≤ ‖flightVelocity (gradient U) h (OBABOPath.ou r σ p.2 p.1)‖^3 := by positivity
  constructor
  · refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    have hQpos : 0 ≤ Q := by
      have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := by positivity
      linarith
    have hright : 0 ≤ ((6.6:ℝ)*Q)^(3/2:ℝ) := Real.rpow_nonneg (by positivity) _
    rw [ENNReal.toReal_ofReal hright] at ht
    exact ht

end
end PersistencePays
#print axioms PersistencePays.stdGaussian_third_norm_lintegral
#print axioms PersistencePays.flight_third_constant

#print axioms PersistencePays.noisy_flight_third_lintegral

#print axioms PersistencePays.noisy_flight_third_moment
