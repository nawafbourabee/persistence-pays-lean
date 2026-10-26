import PersistencePays.PropositionFiveTen
import PersistencePays.FreeTransportTheorem

/-! Unconditional manuscript Propositions 5.9 and 5.10. The smooth-flight
hypothesis of the construction modules is discharged by the proved theorem. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.proposition_5_9_verified {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 < h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar:ℝ) (hα:(μ {z|vstar<‖flightVelocity (gradient U) h z‖}).toReal<1) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let post := μ.map (comparisonVerletEquiv (gradient U) hg h vstar)
    a.corrector post-a.corrector μ ≤
      h*((13/2:ℝ)*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy post (stdGaussian E) 0).toReal)-
        (1/2:ℝ)*(klDiv μ.fst (positionGibbs U)).toReal)+h*a.comparisonCorrectorError μ h D vstar := by
  exact a.proposition_5_9 a.gaussianSmoothedFreeTransportBound hstar hzero hh hL μ hμ hK D hD hcap vstar hα

theorem A1.proposition_5_10_verified {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0)
    (hh:0<h) (hmax:h≤1/8) (hL:L*h^2≤1/2)
    (z:E×E) (D vstar T B:ℝ) (hD:0<D) (hT:0≤T) (hB:0≤B) (n:ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r:=Real.exp (-h)
    let σ:=Real.sqrt (1-Real.exp (-2*h))
    let rate:=r^2/(4*(16+r))
    let p:=fun k=>OBABOPath.comparisonChainLaw (gradient U) hg h r σ vstar k z
    let q:=fun k=>phaseOUKernel r σ ∘ₘ p k
    (∀k,k<n → q k≤ENNReal.ofReal D • ((volume:Measure E).prod volume)) →
    (∀k,k<n → ((q k) {z|vstar<‖flightVelocity (gradient U) h z‖}).toReal<1) →
    (∀k,k<n → (∫w,max (comparisonDefect U (gradient U) h vstar w) 0∂q k)≤T) →
    (∀k,k<n → a.comparisonRemainder h vstar D (q k)≤B) →
    (klDiv (p n) (phaseGibbs U)).toReal≤
      (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*
        (klDiv (OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z) (phaseGibbs U)).toReal+
      (16/15:ℝ)*(h^2*L/4*(∫w,U w.1∂p n)+T/(rate*h)+(4.79:ℝ)*B) := by
  exact a.proposition_5_10 a.gaussianSmoothedFreeTransportBound hstar hzero hh hmax hL z D vstar T B hD hT hB n

end PersistencePays
#print axioms PersistencePays.A1.proposition_5_9_verified
#print axioms PersistencePays.A1.proposition_5_10_verified
