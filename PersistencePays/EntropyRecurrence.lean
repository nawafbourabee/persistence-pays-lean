import PersistencePays.Basic

/-! The scalar recurrence in Proposition 4.12.  These are conditional algebraic
components: the actual entropy and transport-corrector estimates must be supplied
by the analytic modules before this yields a theorem about the sampler. -/

namespace PersistencePays

/-- A nonnegative correction telescopes through a dissipative recurrence.
The proof retains its sign, so it does not sum absolute one-step defects. -/
theorem corrected_recurrence_bound (H g : ℕ → ℝ) {a B : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hB : 0 ≤ B) (hg : ∀ k, 0 ≤ g k)
    (hstep : ∀ k, H (k+1) ≤ a*H k+(g (k+1)-g k)+B) (n : ℕ) :
    H n ≤ a^n*H 0+g n+B/(1-a) := by
  have hd : 0 < 1-a := sub_pos.mpr ha1
  have he : a*(B/(1-a))+B = B/(1-a) := by
    field_simp
    <;> ring
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have hb : 0 ≤ B/(1-a) := div_nonneg hB hd.le
    linarith [hg 0]
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih ha
    have hgn := mul_nonpos_of_nonpos_of_nonneg (show a-1 ≤ 0 by linarith) (hg n)
    have hs := hstep n
    rw [pow_succ]
    nlinarith

/-- The explicit entropy bound after the corrected recurrence.  All supplied
sequences are real scalar quantities; this lemma alone is not Theorem 2. -/
theorem entropy_recurrence_bound (Ent H g : ℕ → ℝ) {θ rate h B : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hrateh : 0 < rate*h) (hrateh1 : rate*h ≤ 1)
    (hB : 0 ≤ B) (hEnt : ∀ k, 0 ≤ Ent k) (hg : ∀ k, 0 ≤ g k)
    (hcompare : ∀ k, (1-θ)*Ent k ≤ H k ∧ H k ≤ (1+θ)*Ent k)
    (hstep : ∀ k, H (k+1) ≤ (1-rate*h)*H k+(g (k+1)-g k)+B) (n : ℕ) :
    Ent n ≤ ((1+θ)/(1-θ))*Real.exp (-rate*h*(n:ℝ))*Ent 0+
      (g n+B/(rate*h))/(1-θ) := by
  have ha : 0 ≤ 1-rate*h := sub_nonneg.mpr hrateh1
  have hb := corrected_recurrence_bound H g ha (by linarith) hB hg hstep n
  have hpow : (1-rate*h)^n ≤ Real.exp (-rate*h*(n:ℝ)) := by
    have he : 1-rate*h ≤ Real.exp (-rate*h) := by
      have := Real.add_one_le_exp (-rate*h)
      linarith
    have hp := pow_le_pow_left₀ ha he n
    rw [← Real.exp_nat_mul] at hp
    convert hp using 1 <;> congr 1 <;> ring
  have h0 : 0 ≤ H 0 := (mul_nonneg (by linarith) (hEnt 0)).trans (hcompare 0).1
  have hp0 := mul_le_mul_of_nonneg_right hpow h0
  have hc0 := mul_le_mul_of_nonneg_left (hcompare 0).2
    (Real.exp_nonneg (-rate*h*(n:ℝ)))
  have hc := (hcompare n).1
  have hd : 0 < 1-θ := by linarith
  have he : 1-(1-rate*h)=rate*h := by ring
  rw [he] at hb
  have hid : (((1+θ)/(1-θ))*Real.exp (-rate*h*(n:ℝ))*Ent 0+
      (g n+B/(rate*h))/(1-θ))*(1-θ) =
      (1+θ)*Real.exp (-rate*h*(n:ℝ))*Ent 0+g n+B/(rate*h) := by
    field_simp
    <;> ring
  have hfin : (1-θ)*Ent n ≤
      (1+θ)*Real.exp (-rate*h*(n:ℝ))*Ent 0+g n+B/(rate*h) := by
    nlinarith
  apply le_of_mul_le_mul_right (a := 1-θ) _ hd
  rw [hid]
  nlinarith

end PersistencePays

#print axioms PersistencePays.corrected_recurrence_bound
#print axioms PersistencePays.entropy_recurrence_bound
