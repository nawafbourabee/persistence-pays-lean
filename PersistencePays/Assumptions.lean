import PersistencePays.Verlet

/-!
# Actual potential hypotheses and the energy-error lemma

The Hessian here is the Fréchet derivative of mathlib's actual gradient.
No abstract force or proposed Hessian is supplied as an extra input.
-/

namespace PersistencePays

noncomputable section
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def hessian (U : E → ℝ) : E → E →L[ℝ] E := fderiv ℝ (gradient U)

/-- Assumption (A1), written using quadratic forms for the Hessian bounds. -/
structure A1 (U : E → ℝ) (m L : ℝ) : Prop where
  twice_contDiff : ContDiff ℝ 2 U
  m_pos : 0 < m
  m_le_L : m ≤ L
  lower : ∀ x u, m * ‖u‖ ^ 2 ≤ ⟪hessian U x u, u⟫_ℝ
  upper : ∀ x u, ⟪hessian U x u, u⟫_ℝ ≤ L * ‖u‖ ^ 2

/-- Assumption (A2), with the operator norm on Hessians. -/
structure A2 (U : E → ℝ) (LH : ℝ) : Prop where
  lipschitz : ∀ x y, ‖hessian U x - hessian U y‖ ≤ LH * ‖x - y‖

theorem contDiff_gradient_of_twice_contDiff (U : E → ℝ) (hU : ContDiff ℝ 2 U) :
    ContDiff ℝ 1 (gradient U) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hU.fderiv_right (by norm_num))

theorem A1.hasGradientAt {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x : E) :
    HasGradientAt U (gradient U x) x :=
  ((a.twice_contDiff.differentiable (by norm_num)) x).hasGradientAt

theorem A1.hasHessianAt {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x : E) :
    HasFDerivAt (gradient U) (hessian U x) x :=
  (((contDiff_gradient_of_twice_contDiff U a.twice_contDiff).differentiable
    (by norm_num)) x).hasFDerivAt

theorem A1.continuous_hessian {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Continuous (hessian U) :=
  (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous_fderiv (by norm_num)

theorem A1.L_pos {U : E → ℝ} {m L : ℝ} (a : A1 U m L) : 0 < L :=
  lt_of_lt_of_le a.m_pos a.m_le_L

theorem A1.nonnegative_hessian {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x u : E) :
    0 ≤ ⟪hessian U x u, u⟫_ℝ :=
  le_trans (mul_nonneg (le_of_lt a.m_pos) (sq_nonneg _)) (a.lower x u)

theorem A1.strong_lower_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x y : E) :
    U x + ⟪gradient U x, y - x⟫_ℝ + m / 2 * ‖y - x‖ ^ 2 ≤ U y := by
  have h1 : x + (1 : ℝ) • (y - x) = y := by module
  have hb := scalar_descent_bound
    (fun t : ℝ => -U (x + t • (y - x)))
    (fun t : ℝ => -⟪gradient U (x + t • (y - x)), y - x⟫_ℝ)
    (fun t : ℝ => -⟪hessian U (x + t • (y - x)) (y - x), y - x⟫_ℝ)
    (fun t => (potential_line_derivative U (gradient U) a.hasGradientAt x (y - x) t).neg)
    (fun t => (gradient_line_derivative (gradient U) (hessian U) a.hasHessianAt
      x (y - x) t).neg)
    (hessian_line_continuous (hessian U) a.continuous_hessian x (y - x)).neg
    (-(m * ‖y - x‖ ^ 2))
    (fun t _ => neg_le_neg (a.lower (x + t • (y - x)) (y - x)))
  simp only [h1, zero_smul, add_zero] at hb
  linarith

/-- Strong convexity gives an actual global minimizer in finite dimension. -/
theorem A1.exists_minimizer [FiniteDimensional ℝ E] {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) : ∃ xstar, ∀ y, U xstar ≤ U y := by
  apply a.twice_contDiff.continuous.exists_forall_le_of_isBounded (0 : E)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2 * ‖gradient U (0 : E)‖ / m, ?_⟩
  intro y hy
  have hlower := a.strong_lower_bound (0 : E) y
  simp only [sub_zero] at hlower
  have hinner : -(‖gradient U (0 : E)‖ * ‖y‖) ≤ ⟪gradient U (0 : E), y⟫_ℝ :=
    le_trans (neg_le_neg (abs_real_inner_le_norm _ _)) (neg_abs_le _)
  have hq : m * ‖y‖ ^ 2 ≤ 2 * ‖gradient U (0 : E)‖ * ‖y‖ := by
    have huy : U y ≤ U (0 : E) := hy
    nlinarith
  by_cases hn : ‖y‖ = 0
  · rw [hn]
    exact div_nonneg (by positivity) (le_of_lt a.m_pos)
  · have hnpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hm : m * ‖y‖ ≤ 2 * ‖gradient U (0 : E)‖ :=
      le_of_mul_le_mul_right (by nlinarith [hq]) hnpos
    exact (le_div_iff₀ a.m_pos).mpr (by nlinarith [hm])

noncomputable def A1.minimizer [FiniteDimensional ℝ E] {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) : E := Classical.choose a.exists_minimizer

theorem A1.minimizer_le [FiniteDimensional ℝ E] {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (y : E) : U a.minimizer ≤ U y :=
  Classical.choose_spec a.exists_minimizer y

theorem A1.gradient_minimizer [FiniteDimensional ℝ E] {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) : gradient U a.minimizer = 0 := by
  have hlocal : IsLocalMin U a.minimizer := Filter.Eventually.of_forall a.minimizer_le
  unfold gradient
  rw [hlocal.fderiv_eq_zero]
  simp

theorem A1.quadratic_lower_at_minimizer [FiniteDimensional ℝ E]
    {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x : E) :
    U a.minimizer + m / 2 * ‖x - a.minimizer‖ ^ 2 ≤ U x := by
  simpa only [a.gradient_minimizer, inner_zero_left, add_zero]
    using a.strong_lower_bound a.minimizer x

theorem A1.minimizer_unique [FiniteDimensional ℝ E] {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (x : E) (hx : ∀ y, U x ≤ U y) : x = a.minimizer := by
  have hb := a.quadratic_lower_at_minimizer x
  have hn : ‖x - a.minimizer‖ ^ 2 = 0 := by
    have hprod : m * ‖x - a.minimizer‖ ^ 2 ≤ 0 := by nlinarith [hx a.minimizer]
    have hs : ‖x - a.minimizer‖ ^ 2 ≤ 0 :=
      le_of_mul_le_mul_left (by simpa only [mul_zero] using hprod) a.m_pos
    exact le_antisymm hs (sq_nonneg _)
  have hnorm : ‖x - a.minimizer‖ = 0 := by nlinarith [norm_nonneg (x - a.minimizer)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Lemma 2.1's conclusions under the paper's actual potential assumptions.
The minimizer is supplied explicitly; its existence is a separate statement. -/
theorem lemma_2_1_at_minimizer {U : E → ℝ} {m L LH h : ℝ} (a1 : A1 U m L) (a2 : A2 U LH)
    (hh : 0 ≤ h) (xstar : E) (hstar : ∀ y, U xstar ≤ U y) (z : E × E) :
    let g := gradient U
    let z₁ := verlet g h z
    let V := flightVelocity g h z
    phaseEnergy U z₁ - phaseEnergy U z =
        gradientCorrection g h z₁.1 - gradientCorrection g h z.1 +
          trapezoidDefect U g z.1 z₁.1 ∧
    |trapezoidDefect U g z.1 z₁.1| ≤ L * h ^ 2 / 8 * ‖V‖ ^ 2 ∧
    |trapezoidDefect U g z.1 z₁.1| ≤ LH / 12 * h ^ 3 * ‖V‖ ^ 3 ∧
    0 ≤ gradientCorrection g h z.1 ∧
    gradientCorrection g h z.1 ≤ (h ^ 2 * L / 4) * (U z.1 - U xstar) := by
  dsimp only
  refine ⟨verlet_energy_identity U (gradient U) h z, ?_, ?_, ?_⟩
  · exact verlet_trapezoidDefect_bound U (gradient U) (hessian U)
      a1.hasGradientAt a1.hasHessianAt a1.continuous_hessian L h
      (fun x u => ⟨a1.nonnegative_hessian x u, a1.upper x u⟩) z
  · exact verlet_trapezoidDefect_lipschitz_bound U (gradient U) (hessian U)
      a1.hasGradientAt a1.hasHessianAt a1.continuous_hessian LH h hh a2.lipschitz z
  · exact gradientCorrection_bound U (gradient U) (hessian U)
      a1.hasGradientAt a1.hasHessianAt a1.continuous_hessian L a1.L_pos a1.upper
      (U xstar) hstar h z.1

/-- Lemma 2.1 with the minimizer constructed from (A1), in finite dimension. -/
theorem lemma_2_1 [FiniteDimensional ℝ E] {U : E → ℝ} {m L LH h : ℝ}
    (a1 : A1 U m L) (a2 : A2 U LH) (hh : 0 ≤ h) (z : E × E) :
    let g := gradient U
    let z₁ := verlet g h z
    let V := flightVelocity g h z
    phaseEnergy U z₁ - phaseEnergy U z =
        gradientCorrection g h z₁.1 - gradientCorrection g h z.1 +
          trapezoidDefect U g z.1 z₁.1 ∧
    |trapezoidDefect U g z.1 z₁.1| ≤ L * h ^ 2 / 8 * ‖V‖ ^ 2 ∧
    |trapezoidDefect U g z.1 z₁.1| ≤ LH / 12 * h ^ 3 * ‖V‖ ^ 3 ∧
    0 ≤ gradientCorrection g h z.1 ∧
    gradientCorrection g h z.1 ≤ (h ^ 2 * L / 4) * (U z.1 - U a1.minimizer) :=
  lemma_2_1_at_minimizer a1 a2 hh a1.minimizer a1.minimizer_le z

/-- The (A1)-only statements do not require (A2). -/
theorem lemma_2_1_A1 [FiniteDimensional ℝ E] {U : E → ℝ} {m L h : ℝ}
    (a1 : A1 U m L) (z : E × E) :
    let g := gradient U
    let z₁ := verlet g h z
    let V := flightVelocity g h z
    phaseEnergy U z₁ - phaseEnergy U z =
        gradientCorrection g h z₁.1 - gradientCorrection g h z.1 +
          trapezoidDefect U g z.1 z₁.1 ∧
    |trapezoidDefect U g z.1 z₁.1| ≤ L * h ^ 2 / 8 * ‖V‖ ^ 2 ∧
    0 ≤ gradientCorrection g h z.1 ∧
    gradientCorrection g h z.1 ≤ (h ^ 2 * L / 4) * (U z.1 - U a1.minimizer) := by
  dsimp only
  refine ⟨verlet_energy_identity U (gradient U) h z, ?_, ?_⟩
  · exact verlet_trapezoidDefect_bound U (gradient U) (hessian U)
      a1.hasGradientAt a1.hasHessianAt a1.continuous_hessian L h
      (fun x u => ⟨a1.nonnegative_hessian x u, a1.upper x u⟩) z
  · exact gradientCorrection_bound U (gradient U) (hessian U)
      a1.hasGradientAt a1.hasHessianAt a1.continuous_hessian L a1.L_pos a1.upper
      (U a1.minimizer) a1.minimizer_le h z.1

theorem quadratic_hasGradientAt (A : E →L[ℝ] E) (b : E) (c : ℝ)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (x : E) :
    HasGradientAt (quadraticPotential A.toLinearMap b c) (A x + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hq := (hasFDerivAt_id (𝕜 := ℝ) x).inner ℝ A.hasFDerivAt
  have hl := (innerSL ℝ b).hasFDerivAt (x := x)
  have hp := ((hq.const_smul (1 / 2 : ℝ)).add hl).add_const c
  convert! hp using 1
  · funext y
    change ⟪y, A y⟫_ℝ / 2 + ⟪b, y⟫_ℝ + c =
      (1 / 2 : ℝ) * ⟪y, A y⟫_ℝ + ⟪b, y⟫_ℝ + c
    ring
  · ext u
    simp only [InnerProductSpace.toDual_apply_apply, inner_add_left,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
      smul_eq_mul, id_eq]
    rw [hA x u, real_inner_comm (A x) u]
    rw [hA x u]
    ring

/-- The quadratic clause of Lemma 2.1, with the actual gradient of the potential. -/
theorem lemma_2_1_quadratic (A : E →L[ℝ] E) (b : E) (c : ℝ)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (x y : E) :
    trapezoidDefect (quadraticPotential A.toLinearMap b c)
      (gradient (quadraticPotential A.toLinearMap b c)) x y = 0 := by
  have hg : gradient (quadraticPotential A.toLinearMap b c) = fun z => A z + b :=
    gradient_eq (quadratic_hasGradientAt A b c hA)
  rw [hg]
  exact quadratic_trapezoidDefect A.toLinearMap b c hA x y

end
end PersistencePays

#print axioms PersistencePays.contDiff_gradient_of_twice_contDiff
#print axioms PersistencePays.A1.exists_minimizer
#print axioms PersistencePays.lemma_2_1
#print axioms PersistencePays.lemma_2_1_A1
#print axioms PersistencePays.lemma_2_1_quadratic
