import PersistencePays.GaussianCrossing

/-!
# The dimension factor in Proposition 2.4

Bernoulli's inequality proves the paper's uniform step-size optimization
directly, without assuming the existence or uniqueness of a critical point.
-/

noncomputable section
namespace PersistencePays.GaussianLowerBound

def gaussianRho (ω : ℝ) : ℝ := (Real.sqrt (1 + ω ^ 6 / 64))⁻¹

theorem gaussianRho_pos (ω : ℝ) : 0 < gaussianRho ω := by
  unfold gaussianRho
  have h6 : 0 ≤ ω ^ 6 := by positivity
  positivity

theorem gaussianRho_le_one (ω : ℝ) : gaussianRho ω ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1 + ω ^ 6 / 64) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [pow_nonneg (sq_nonneg ω) 3]
  simpa [gaussianRho] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs

theorem bernoulli_dimension_bound (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (hx : 0 ≤ x) :
    (d : ℝ) * x ≤ (1 + x) ^ (3 * (d - 1)) := by
  have hn : d ≤ 3 * (d - 1) := by omega
  have hcast : (d : ℝ) ≤ (3 * (d - 1) : ℕ) := by exact_mod_cast hn
  have hb := one_add_mul_le_pow (show -2 ≤ x by linarith) (3 * (d - 1))
  have hm := mul_le_mul_of_nonneg_right hcast hx
  linarith

theorem gaussian_step_optimization (d : ℕ) (hd : 2 ≤ d) (ω : ℝ) (hω : 0 < ω) :
    (1 / 2 : ℝ) * (d : ℝ) ^ (1 / 6 : ℝ) ≤
      (Real.sqrt (1 + ω ^ 6 / 64)) ^ (d - 1) / ω := by
  have hD : 0 ≤ 1 + ω ^ 6 / 64 := by positivity
  have hs := Real.sq_sqrt hD
  have hp : ((Real.sqrt (1 + ω ^ 6 / 64)) ^ (d - 1)) ^ 6 =
      (1 + ω ^ 6 / 64) ^ (3 * (d - 1)) := by
    rw [← pow_mul, show (d - 1) * 6 = 2 * (3 * (d - 1)) by omega,
      pow_mul, hs]
  have hdroot : ((d : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = d := by
    simpa using Real.rpow_inv_natCast_pow (x := (d : ℝ))
      (by positivity) (by norm_num : (6 : ℕ) ≠ 0)
  have hb := bernoulli_dimension_bound d hd (ω ^ 6 / 64) (by positivity)
  have hpow : ((1 / 2 : ℝ) * (d : ℝ) ^ (1 / 6 : ℝ)) ^ 6 ≤
      ((Real.sqrt (1 + ω ^ 6 / 64)) ^ (d - 1) / ω) ^ 6 := by
    simp only [mul_pow, hdroot, div_pow, hp]
    apply (le_div_iff₀ (pow_pos hω 6)).mpr
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (6 : ℕ) ≠ 0)).mp hpow

theorem gaussian_step_acceptance_optimization (d : ℕ) (hd : 2 ≤ d) (ω : ℝ) (hω : 0 < ω) :
    ω * (gaussianRho ω) ^ (d - 1) ≤ 2 / (d : ℝ) ^ (1 / 6 : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hroot : 0 < (d : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hdpos _
  have hs : 0 < Real.sqrt (1 + ω ^ 6 / 64) := by positivity
  have hc := gaussian_step_optimization d hd ω hω
  apply (le_div_iff₀ hroot).mpr
  rw [gaussianRho, inv_pow]
  have hcp : 0 < Real.sqrt (1 + ω ^ 6 / 64) ^ (d - 1) := pow_pos hs _
  have hc' : (1 / 2 : ℝ) * (d : ℝ) ^ (1 / 6 : ℝ) * ω ≤
      Real.sqrt (1 + ω ^ 6 / 64) ^ (d - 1) := (le_div_iff₀ hω).mp hc
  have hm := (div_le_iff₀ hcp).mpr (show ω * (d : ℝ) ^ (1 / 6 : ℝ) ≤
      2 * Real.sqrt (1 + ω ^ 6 / 64) ^ (d - 1) by nlinarith)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm

end PersistencePays.GaussianLowerBound

#print axioms PersistencePays.GaussianLowerBound.gaussian_step_optimization
#print axioms PersistencePays.GaussianLowerBound.gaussian_step_acceptance_optimization
