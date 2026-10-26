import PersistencePays.Verlet
import PersistencePays.GaussianOU

/-! Bounds for the actual OU coefficients, without assumed scalar estimates. -/

namespace PersistencePays

theorem exp_neg_quadratic_upper (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-a) ≤ 1 - a + a ^ 2 / 2 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-a * s))
      (-a * Real.exp (-a * t)) t := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-a)).exp
  have hdd (t : ℝ) : HasDerivAt (fun s : ℝ => -a * Real.exp (-a * s))
      (a ^ 2 * Real.exp (-a * t)) t := by
    simpa only [neg_mul, mul_neg, neg_neg, pow_two, mul_assoc] using (hd t).const_mul (-a)
  have hb := scalar_descent_bound (fun t : ℝ => Real.exp (-a * t))
    (fun t => -a * Real.exp (-a * t)) (fun t => a ^ 2 * Real.exp (-a * t))
    hd hdd (by fun_prop) (a ^ 2) (fun t ht => by
      have he : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      simpa using mul_le_mul_of_nonneg_left he (sq_nonneg a))
  simpa [sub_eq_add_neg] using hb

theorem one_sub_exp_neg_le (h : ℝ) : 1 - Real.exp (-h) ≤ h := by
  have hb := Real.add_one_le_exp (-h)
  linarith

theorem normalized_ou_coefficients (h : ℝ) (hh : 0 ≤ h) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1 - Real.exp (-2 * h))
    0 < r ∧ r ≤ 1 ∧ 0 ≤ σ ∧ r ^ 2 + σ ^ 2 = 1 ∧
      1 - r ≤ h ∧ 2 * h * (1 - h) ≤ 1 - r ^ 2 ∧
      2 * h * (1 - h) ≤ σ ^ 2 ∧ σ ^ 2 ≤ 2 * h := by
  dsimp only
  have he : Real.exp (-2 * h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs : (Real.sqrt (1 - Real.exp (-2 * h))) ^ 2 = 1 - Real.exp (-2 * h) :=
    Real.sq_sqrt (by linarith)
  have hr : (Real.exp (-h)) ^ 2 = Real.exp (-2 * h) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hq := exp_neg_quadratic_upper (2 * h) (by positivity)
  have hl := one_sub_exp_neg_le (2 * h)
  simp only [neg_mul] at hs hr
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), Real.sqrt_nonneg _,
    ?_, one_sub_exp_neg_le h, ?_, ?_, ?_⟩
  all_goals
    try simp only [neg_mul]
    nlinarith

theorem normalized_ou_noise_bound (h : ℝ) (hh : 0 ≤ h) (hh' : h ≤ 1 / 8) :
    Real.sqrt (1 - Real.exp (-2 * h)) ≤ 1 / 2 := by
  have hb := (normalized_ou_coefficients h hh).2.2.2.2.2.2.2
  have hn := Real.sqrt_nonneg (1 - Real.exp (-2 * h))
  nlinarith

end PersistencePays

#print axioms PersistencePays.exp_neg_quadratic_upper
#print axioms PersistencePays.normalized_ou_coefficients
