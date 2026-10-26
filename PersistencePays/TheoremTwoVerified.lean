import PersistencePays.TheoremTwo
import PersistencePays.FreeTransportTheorem

/-! Theorem 2 for the actual cold-start OBABO chain, with no unresolved
analytic premises. The full dependency closure is checked by AxiomAudit. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.theorem_two {U : E → ℝ} {m L LH : ℝ}
    (a : A1 U m L) (a2 : A2 U LH)
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
        theoremTwoMomentBound a LH h r σ rate (K z) n) :=
  a.theorem_two_of_smoothed_free_transport a2 a.gaussianSmoothedFreeTransportBound h hh hhmax z n

end PersistencePays
#print axioms PersistencePays.A1.theorem_two
