import PersistencePays.TheoremTwoFiniteEntropy

/-! Cold-start Theorem 2, for the actual OBABO kernel. All density, entropy,
moment, coefficient, and finite-horizon estimates are discharged. The single
remaining analytic premise is named explicitly: the bounded-law Gaussian
free-flight theorem, constructed independently in Appendix A. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem unadjustedEntropyLaw_from_one_step {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (z : E×E) (n : ℕ) :
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    unadjustedEntropyLaw a h r σ (K z) n = iterateKernel K (n+1) z := by
  let K := OBABOPath.unadjustedStepKernel (gradient U)
    (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
  change unadjustedEntropyLaw a h r σ (K z) n = iterateKernel K (n+1) z
  induction n with
  | zero => simp [unadjustedEntropyLaw_zero,iterateKernel]
  | succ n ih =>
    rw [unadjustedEntropyLaw_succ,ih]
    rfl

/-- The manuscript's cold-start relative-entropy estimate, in shift-invariant
potential notation. `theoremTwoMomentBound` is the finite maximum of exactly
the displayed second/third flight-moment remainders (with zero included). -/
theorem A1.theorem_two_of_smoothed_free_transport {U : E → ℝ} {m L LH : ℝ}
    (a : A1 U m L) (a2 : A2 U LH) (hsm : GaussianSmoothedFreeTransportBound a)
    (h : ℝ) (hh : 0 < h) (hhmax : Real.sqrt m*h ≤ 3/16) (z : E×E) (n : ℕ) :
    let r := Real.exp (-(Real.sqrt m*h))
    let σ := Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h)))
    let rate := r^2*Real.sqrt m/(4*(16+r))
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    (klDiv (iterateKernel K (n+1) z) (phaseGibbs U)).toReal ≤
      (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*
        ((∫ w,phaseEnergy U w ∂K z)-U a.minimizer+(Module.finrank ℝ E:ℝ)*
          Real.log ((2*Real.exp 1*m*h^2*(1-Real.sqrt m*h))⁻¹))+
      (16/15:ℝ)*(h^2*L/4*(∫ w,U w.1-U a.minimizer ∂iterateKernel K (n+1) z)+
        theoremTwoMomentBound a LH h r σ rate (K z) n) := by
  let r := Real.exp (-(Real.sqrt m*h))
  let σ := Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h)))
  let rate := r^2*Real.sqrt m/(4*(16+r))
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let K := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ
  have hinit := a.lemma_4_14 h hh (by linarith) z
  have hm : MemLp id 3 (K z) := by
    have hm' := OBABOPath.unadjusted_kernel_finite_moments a h r σ 1 z 3 (by norm_num)
    rw [OBABOPath.unadjustedEpochKernel_eq_iterate] at hm'
    simpa only [iterateKernel,Kernel.comp_id] using hm'
  have hb := a.theorem_two_finite_entropy a2 hsm (K z) hm hinit.1 h hh hhmax n
  dsimp only at hb hinit ⊢
  have he := unadjustedEntropyLaw_from_one_step a h r σ z n
  dsimp only at he
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_left hinit.2.1
    (show 0 ≤ (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ)) by positivity)
  change (klDiv (iterateKernel K (n+1) z) (phaseGibbs U)).toReal ≤ _ at hb ⊢
  linarith

end PersistencePays
#print axioms PersistencePays.A1.theorem_two_of_smoothed_free_transport
