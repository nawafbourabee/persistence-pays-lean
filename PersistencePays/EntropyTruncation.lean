import PersistencePays.Pinsker
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Bounded entropy-dual maximizers, including zero density. -/
open Real Filter MeasureTheory InformationTheory
open scoped Topology ENNReal
namespace PersistencePays
noncomputable section

def truncatedLog (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then -(n : ℝ) else max (-(n : ℝ)) (min (n : ℝ) (log x))

def truncatedDual (n : ℕ) (x : ℝ) : ℝ :=
  x * truncatedLog n x - exp (truncatedLog n x) + 1

lemma truncatedLog_bounds (n : ℕ) (x : ℝ) :
    -(n : ℝ) ≤ truncatedLog n x ∧ truncatedLog n x ≤ n := by
  unfold truncatedLog
  split_ifs <;> constructor
  · rfl
  · nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  · exact le_max_left _ _
  · exact max_le (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]) (min_le_left _ _)

lemma measurable_truncatedLog (n : ℕ) : Measurable (truncatedLog n) := by
  unfold truncatedLog
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const (measurable_const.max (measurable_const.min measurable_log))

lemma exp_sub_one_le_mul (t : ℝ) : exp t - 1 ≤ t * exp t := by
  have hh := mul_le_mul_of_nonneg_left (add_one_le_exp (-t)) (exp_pos t).le
  rw [← exp_add] at hh
  simp only [add_neg_cancel, exp_zero] at hh
  nlinarith

lemma truncatedDual_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ truncatedDual n x := by
  by_cases hx0 : x = 0
  · subst x
    have hh : exp (-(n : ℝ)) ≤ 1 := (exp_le_one_iff).mpr (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
    simpa [truncatedDual, truncatedLog] using sub_nonneg.mpr hh
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have he := exp_sub_one_le_mul (truncatedLog n x)
    have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    by_cases hlog : 0 ≤ log x
    · have ht : truncatedLog n x = min (n : ℝ) (log x) := by
        simp only [truncatedLog, if_neg hx0]
        exact max_eq_right (le_trans (by linarith) (le_min hN hlog))
      have ht0 : 0 ≤ truncatedLog n x := by rw [ht]; exact le_min hN hlog
      have htexp : exp (truncatedLog n x) ≤ x := by
        calc
          exp (truncatedLog n x) ≤ exp (log x) := exp_le_exp.mpr (by rw [ht]; exact min_le_right _ _)
          _ = x := exp_log hxp
      have hh := mul_le_mul_of_nonneg_left htexp ht0
      unfold truncatedDual
      nlinarith
    · have ht : truncatedLog n x = max (-(n : ℝ)) (log x) := by
        simp only [truncatedLog, if_neg hx0, min_eq_right (le_trans (le_of_not_ge hlog) hN)]
      have ht0 : truncatedLog n x ≤ 0 := by rw [ht]; exact max_le (by linarith) (le_of_not_ge hlog)
      have htexp : x ≤ exp (truncatedLog n x) := by
        calc
          x = exp (log x) := (exp_log hxp).symm
          _ ≤ exp (truncatedLog n x) := exp_le_exp.mpr (by rw [ht]; exact le_max_right _ _)
      have hh := mul_le_mul_of_nonpos_left htexp ht0
      unfold truncatedDual
      nlinarith

lemma truncatedDual_le_klFun (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    truncatedDual n x ≤ klFun x := by
  have hh := mul_le_klFun_add_exp hx (truncatedLog n x)
  unfold truncatedDual
  linarith

lemma truncatedLog_eventually {x : ℝ} (hx : x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, truncatedLog n x = log x := by
  obtain ⟨N,hN⟩ := exists_nat_ge |log x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have h₁ : log x ≤ (n : ℝ) := (le_abs_self _).trans (hN.trans hnn)
  have h₂ : -(n : ℝ) ≤ log x := by
    have hh := neg_abs_le (log x)
    linarith
  simp only [truncatedLog, if_neg hx, min_eq_right h₁, max_eq_right h₂]

lemma truncatedDual_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => truncatedDual n x) atTop (𝓝 (klFun x)) := by
  by_cases hx0 : x = 0
  · subst x
    simp only [truncatedDual, truncatedLog, ite_true, zero_mul, zero_sub, klFun,
      mul_zero, zero_add, sub_zero]
    have hh : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    simpa using hh.neg.add_const 1
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    apply tendsto_const_nhds.congr'
    filter_upwards [truncatedLog_eventually hx0] with n hn
    simp only [truncatedDual, hn, exp_log hxp, klFun]
    ring

end
end PersistencePays
#print axioms PersistencePays.truncatedDual_tendsto
#print axioms PersistencePays.truncatedDual_nonneg
