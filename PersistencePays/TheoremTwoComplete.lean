import PersistencePays.TheoremTwoLiteral

/-! Theorem 2 as an extended-real entropy bound. Finiteness is exported
explicitly, so no interpretation of `∞.toReal` is needed by a reader. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.theorem_two_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h : ℝ) (hh : 0 < h) (z : E×E) (n : ℕ) :
    let r := Real.exp (-(Real.sqrt m*h))
    let σ := Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h)))
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    klDiv (iterateKernel K (n+1) z) (phaseGibbs U) ≠ ∞ := by
  have ht : 0 < Real.sqrt m*h := mul_pos (Real.sqrt_pos.mpr a.m_pos) hh
  have hσ : 0 < Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h))) := by
    apply Real.sqrt_pos.mpr
    have he : Real.exp (-2*(Real.sqrt m*h)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hn := (normalized_ou_coefficients (Real.sqrt m*h) ht.le).2.2.2.1
  have hf := a.unadjusted_cold_entropy h _ _ hh hσ hn z n
  rw [OBABOPath.unadjustedEpochKernel_eq_iterate] at hf
  exact hf

theorem A1.theorem_two_ennreal {U : E → ℝ} {m L LH : ℝ}
    (a : A1 U m L) (a2 : A2 U LH)
    (h : ℝ) (hh : 0 < h) (hhmax : Real.sqrt m*h ≤ 3/16) (z : E×E) (n : ℕ) :
    let r := Real.exp (-(Real.sqrt m*h))
    let σ := Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h)))
    let rate := r^2*Real.sqrt m/(4*(16+r))
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    klDiv (iterateKernel K (n+1) z) (phaseGibbs U) ≤ ENNReal.ofReal
      ((17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*
        ((∫ w,phaseEnergy U w ∂K z)-U a.minimizer+(Module.finrank ℝ E:ℝ)*
          Real.log ((2*Real.exp 1*m*h^2*(1-Real.sqrt m*h))⁻¹))+
      (16/15:ℝ)*(h^2*L/4*(∫ w,U w.1-U a.minimizer ∂iterateKernel K (n+1) z)+
        theoremTwoMomentBound a LH h r σ rate (K z) n)) := by
  have hb := a.theorem_two a2 h hh hhmax z n
  have hf := a.theorem_two_finite h hh z n
  dsimp only at hb hf ⊢
  exact (ENNReal.le_ofReal_iff_toReal_le hf (ENNReal.toReal_nonneg.trans hb)).mpr hb

end PersistencePays
#print axioms PersistencePays.A1.theorem_two_finite
#print axioms PersistencePays.A1.theorem_two_ennreal
