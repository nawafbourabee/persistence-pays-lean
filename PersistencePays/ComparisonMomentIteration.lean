import PersistencePays.ComparisonMoments
import PersistencePays.OUScalarBounds

/-! Lemma 5.11's quantitative moments, for the actual first-unadjusted and
subsequent-comparison sequence of kernels. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem kernel_comp_dirac {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] (K : Kernel S T) (z : S) : K ∘ₘ Measure.dirac z = K z := by
  ext A hA
  rw [Measure.bind_apply hA K.aemeasurable, lintegral_dirac]

theorem memLp_id_dirac (z : E×E) (p : ℝ≥0∞) : MemLp id p (Measure.dirac z) := by
  apply (memLp_congr_ae (show (fun _ : E×E => z) =ᵐ[Measure.dirac z] id by
    change ∀ᵐ x ∂Measure.dirac z, z=x
    simp)).mp
  exact memLp_const z

theorem A1.unadjusted_point_modifiedEnergy_norm {U : E → ℝ} {L h r σ R : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0) (hL : h^2*L ≤ 1/64)
    (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (z : E×E) (hz : phaseEnergy U z ≤ R) :
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    secondMomentNorm (K z) (modifiedEnergy U h) ≤
      (1.008:ℝ)*(R+2*h*((Module.finrank ℝ E : ℝ)+2)) := by
  have hb := a.unadjusted_modifiedEnergy_norm hstar hzero hL hh hr hσ
    (Measure.dirac z) (memLp_id_dirac z 4)
  rw [kernel_comp_dirac] at hb
  have he : secondMomentNorm (Measure.dirac z) (modifiedEnergy U h) = modifiedEnergy U h z := by
    rw [secondMomentNorm, integral_dirac, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (a.modifiedEnergy_nonnegative hstar hzero hL z)]
  rw [he] at hb
  have hbound := (lyapunov_energy_bounds a hstar hzero hL z).2.2.2
  have hn : 0 ≤ h*((Module.finrank ℝ E : ℝ)+2) := by positivity
  dsimp only
  linarith

theorem A1.comparison_iterates_modifiedEnergy_norm {U : E → ℝ} {L LH h r σ vstar R : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hh : 0 ≤ h) (hr : r^2 ≤ 1) (hσ : σ^2 ≤ 2*h)
    (hLH : 0 ≤ LH) (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E×E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    let P := gaussianSandwichKernel e e.measurable r σ
    let μ₁ := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z
    secondMomentNorm (iterateKernel P n ∘ₘ μ₁) (modifiedEnergy U h) ≤
      (1.008:ℝ)*(1+(0.081:ℝ)*h)^n*(R+2*((n:ℝ)+1)*h*((Module.finrank ℝ E : ℝ)+2)) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := comparisonVerletEquiv (gradient U) hg h vstar
  let P := gaussianSandwichKernel e e.measurable r σ
  let μ₁ := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z
  let b : ℝ := h*((Module.finrank ℝ E : ℝ)+2)
  let ρ : ℝ := 1+(0.081:ℝ)*h
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith
  have hm₁ : MemLp id 4 μ₁ := by
    have hm := a.unadjusted_step_memLp (Measure.dirac z) 4 (by norm_num)
      (memLp_id_dirac z 4) h r σ
    rwa [kernel_comp_dirac] at hm
  change secondMomentNorm (iterateKernel P n ∘ₘ μ₁) (modifiedEnergy U h) ≤
    (1.008:ℝ)*ρ^n*(R+2*((n:ℝ)+1)*h*((Module.finrank ℝ E : ℝ)+2))
  induction n with
  | zero =>
    simpa only [iterateKernel, Measure.id_comp, pow_zero, mul_one, Nat.cast_zero,
      zero_add, mul_one] using a.unadjusted_point_modifiedEnergy_norm hstar hzero hL hh hr hσ z hz
  | succ n ih =>
    have hmn := a.comparison_iterates_memLp μ₁ 4 (by norm_num) hm₁ h vstar r σ n
    have hs := a.comparison_modifiedEnergy_norm a2 hstar hzero hL hh hr hσ hLH hscale
      (iterateKernel P n ∘ₘ μ₁) hmn
    change secondMomentNorm (P ∘ₘ (iterateKernel P n ∘ₘ μ₁)) (modifiedEnergy U h) ≤
      ρ*(secondMomentNorm (iterateKernel P n ∘ₘ μ₁) (modifiedEnergy U h)+b)+b at hs
    rw [iterateKernel, ← Measure.comp_assoc]
    have hp : 1 ≤ ρ^n := one_le_pow₀ hρ
    have hmul := mul_le_mul_of_nonneg_left ih (le_trans (by norm_num) hρ)
    rw [Nat.cast_succ, pow_succ]
    have hbρ := mul_nonneg hb (show 0 ≤ ρ-1 by linarith)
    have hbp := mul_nonneg hb (show 0 ≤ ρ^n-1 by linarith)
    have hbρp := mul_nonneg hb (show 0 ≤ ρ^(n+1)-1 by nlinarith [(one_le_pow₀ hρ : 1 ≤ ρ^(n+1))])
    dsimp [b] at hs hbρ hbp hbρp
    rw [pow_succ] at hbρp
    nlinarith

theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n ≤ Real.exp ((n:ℝ)*x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) n

theorem comparison_moment_constants (R d h : ℝ) (n N : ℕ)
    (hR : 0 ≤ R) (hd : 0 ≤ d) (hh : 0 ≤ h) (hhmax : h ≤ 1/8) (hn : n+1 ≤ N) :
    (1.008:ℝ)*(1+(0.081:ℝ)*h)^n*(R+2*((n:ℝ)+1)*h*(d+2))+h*(d+2) ≤
      (1.01:ℝ)*Real.exp ((0.081:ℝ)*((N:ℝ)*h))*(R+2*(d+2)*((N:ℝ)*h+1)) := by
  have hn' : (n:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hn
  have he := one_add_pow_le_exp ((0.081:ℝ)*h) (by positivity) n
  have ht : (n:ℝ)*((0.081:ℝ)*h) ≤ (0.081:ℝ)*((N:ℝ)*h) := by nlinarith
  have hp := he.trans (Real.exp_le_exp.mpr ht)
  have hexp : 1 ≤ Real.exp ((0.081:ℝ)*((N:ℝ)*h)) := Real.one_le_exp (by positivity)
  have hB : 0 ≤ R+2*((n:ℝ)+1)*h*(d+2) := by positivity
  have hBx : R+2*((n:ℝ)+1)*h*(d+2) ≤ R+2*(d+2)*((N:ℝ)*h) := by
    nlinarith [mul_nonneg (show 0 ≤ (N:ℝ)-((n:ℝ)+1) by linarith) (show 0 ≤ h*(d+2) by positivity)]
  have h1 := mul_le_mul_of_nonneg_right hp hB
  have h2 := mul_le_mul_of_nonneg_left hBx (Real.exp_nonneg ((0.081:ℝ)*((N:ℝ)*h)))
  have h3 := mul_le_mul_of_nonneg_left hexp (show 0 ≤ d+2 by positivity)
  have h4 := mul_nonneg (Real.exp_nonneg ((0.081:ℝ)*((N:ℝ)*h)))
    (show 0 ≤ R+2*(d+2)*((N:ℝ)*h) by positivity)
  have h5 := mul_le_mul_of_nonneg_right hhmax (show 0 ≤ d+2 by positivity)
  nlinarith

theorem A1.lemma_5_11_moments {U : E → ℝ} {L LH h vstar R : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hh : 0 < h) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E×E) (hz : phaseEnergy U z ≤ R) (n N : ℕ) (hn : n+1 ≤ N) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    let P := gaussianSandwichKernel e e.measurable r σ
    let μ₁ := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z
    let μ := iterateKernel P n ∘ₘ μ₁
    secondMomentNorm μ (modifiedEnergy U h) ≤
      (1.008:ℝ)*Real.exp ((0.081:ℝ)*(((n:ℝ)+1)*h))*
        (R+2*((Module.finrank ℝ E : ℝ)+2)*(((n:ℝ)+1)*h)) ∧
    secondMomentNorm (phaseOUKernel r σ ∘ₘ μ) (modifiedEnergy U h) ≤
      (1.01:ℝ)*Real.exp ((0.081:ℝ)*((N:ℝ)*h))*
        (R+2*((Module.finrank ℝ E : ℝ)+2)*((N:ℝ)*h+1)) := by
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := comparisonVerletEquiv (gradient U) hg h vstar
  let P := gaussianSandwichKernel e e.measurable r σ
  let μ₁ := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z
  let μ := iterateKernel P n ∘ₘ μ₁
  have hc := normalized_ou_coefficients h hh.le
  have hr : r^2 ≤ 1 := by
    have hnorm : r^2+σ^2=1 := hc.2.2.2.1
    nlinarith [sq_nonneg σ]
  have hσ : σ^2 ≤ 2*h := hc.2.2.2.2.2.2.2
  have hR : 0 ≤ R := le_trans (a.normalized_energy_nonnegative hstar hzero z) hz
  have hhmax : h ≤ 1/8 := by
    have hbound := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  have hb := a.comparison_iterates_modifiedEnergy_norm a2 hstar hzero hL hh.le hr hσ
    hLH hscale z hz n
  have hm₁ : MemLp id 4 μ₁ := by
    have hm := a.unadjusted_step_memLp (Measure.dirac z) 4 (by norm_num)
      (memLp_id_dirac z 4) h r σ
    rwa [kernel_comp_dirac] at hm
  have hm := a.comparison_iterates_memLp μ₁ 4 (by norm_num) hm₁ h vstar r σ n
  have hO := a.ou_modifiedEnergy_norm hstar hzero hL hh.le hr hσ μ hm
  change secondMomentNorm μ (modifiedEnergy U h) ≤ _ ∧
    secondMomentNorm (phaseOUKernel r σ ∘ₘ μ) (modifiedEnergy U h) ≤ _
  constructor
  · apply hb.trans
    have hp := (one_add_pow_le_exp ((0.081:ℝ)*h) (by positivity) n).trans
      (Real.exp_le_exp.mpr (show (n:ℝ)*((0.081:ℝ)*h) ≤ (0.081:ℝ)*(((n:ℝ)+1)*h) by nlinarith))
    have hmul := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ R+2*((n:ℝ)+1)*h*((Module.finrank ℝ E : ℝ)+2) by positivity)
    nlinarith
  · have ht := comparison_moment_constants R (Module.finrank ℝ E) h n N hR
      (by positivity) hh.le hhmax hn
    change secondMomentNorm μ (modifiedEnergy U h) ≤ _ at hb
    linarith

end PersistencePays
#print axioms PersistencePays.A1.comparison_iterates_modifiedEnergy_norm
#print axioms PersistencePays.comparison_moment_constants
#print axioms PersistencePays.A1.lemma_5_11_moments
