import PersistencePays.RejectionClosure

/-! Condition (d) implies the actual small exit probability in Proposition 6.1. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem exp_neg_fortyeight_le : Real.exp (-48) ≤ (10:ℝ)^(-20:ℤ) := by
  have he : (10:ℝ) ≤ Real.exp (2.4:ℝ) := by
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2.4) 6
    norm_num [Finset.sum_range_succ] at ht
    linarith
  have hl : Real.log (10:ℝ) ≤ (2.4:ℝ) := (Real.log_le_iff_le_exp (by norm_num)).mpr he
  calc
    Real.exp (-48) ≤ Real.exp (-Real.log ((10:ℝ)^20)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow]
      norm_num
      linarith
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; norm_num

theorem exit_condition_exponential {R h Ψ vstar : ℝ} (d n : ℕ)
    (hR : 0 ≤ R) (hh : 0 < h) (hΨ : h ≤ Ψ) (hn : 0 < n)
    (hd : 41*((1.2:ℝ)*R+27*(d:ℝ)+50+20*Real.log (2*(n:ℝ))+
      80*Real.log (Ψ/h)+922) ≤ vstar^2) :
    4*(d:ℝ) ≤ vstar^2 ∧ R ≤ vstar^2/32 ∧
    2*(n:ℝ)*Real.exp (-(1/20:ℝ)*((0.79:ℝ)*vstar^2/32-
      ((1.2:ℝ)*R+27*(d:ℝ)))) ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnge : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hΨpos : 0 < Ψ := hh.trans_le hΨ
  have hy : 0 < Ψ/h := div_pos hΨpos hh
  have hlogn : 0 ≤ Real.log (2*(n:ℝ)) := Real.log_nonneg (by linarith)
  have hlogΨ : 0 ≤ Real.log (Ψ/h) := Real.log_nonneg ((one_le_div hh).mpr hΨ)
  have hd0 := (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have ha : (0.79:ℝ)*vstar^2/32 - ((1.2:ℝ)*R+27*(d:ℝ)) ≥
      20*Real.log (2*(n:ℝ))+80*Real.log (Ψ/h)+960 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h4 : Real.exp (-4*Real.log (Ψ/h)) = (h/Ψ)^4 := by
    rw [show -4*Real.log (Ψ/h) = (4:ℕ)*(-Real.log (Ψ/h)) by norm_num,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log hy, inv_div]
  calc
    _ ≤ 2*(n:ℝ)*Real.exp (-Real.log (2*(n:ℝ))-4*Real.log (Ψ/h)-48) := by
      gcongr
      nlinarith
    _ = (h/Ψ)^4 * Real.exp (-48) := by
      rw [show -Real.log (2*(n:ℝ))-4*Real.log (Ψ/h)-48 =
        -Real.log (2*(n:ℝ)) + (-4*Real.log (Ψ/h)) + (-48) by ring,
        Real.exp_add, Real.exp_add, h4, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    _ ≤ _ := by
      calc
        _ ≤ (h/Ψ)^4 * (10:ℝ)^(-20:ℤ) := mul_le_mul_of_nonneg_left exp_neg_fortyeight_le (by positivity)
        _ = _ := mul_comm _ _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem proposition_6_1_exit
    {U : E → ℝ} {L LH h vstar R Ψ : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (hΨ : h ≤ Ψ) (n : ℕ) (hn : 0 < n)
    (hd : 41*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50+20*Real.log (2*(n:ℝ))+
      80*Real.log (Ψ/h)+922) ≤ vstar^2)
    (z : E × E) (hz : phaseEnergy U z ≤ R) :
    gaussianBlock n (stoppedBlockEvent U (gradient U) h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar n z)ᶜ ≤
        ENNReal.ofReal ((10:ℝ)^(-20:ℤ)*(h/Ψ)^4) := by
  obtain ⟨hdim, _, hexp⟩ := exit_condition_exponential (Module.finrank ℝ E) n hR hh hΨ hn hd
  apply (stopped_path_exit_bound_simple a a2 hstar hzero hh.le hL hv hLH hscale
    hdim hR z hz n).trans
  rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hexp

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_exit
