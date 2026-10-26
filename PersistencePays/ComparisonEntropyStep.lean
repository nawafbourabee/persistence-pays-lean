import PersistencePays.CappedCorrectorError
import PersistencePays.ComparisonEnergyTelescope
import PersistencePays.UnadjustedEntropyStep

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.comparison_entropy_corrector_step {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hsm:GaussianSmoothedFreeTransportBound a) (hstar:a.minimizer=0) (hzero:U 0=0)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞)
    (r σ h θ D vstar:ℝ) (hr:0≤r) (hσ:0≤σ) (hn:r^2+σ^2=1)
    (hh:0<h) (hL:L*h^2≤1/2) (hθ:0≤θ) (hD:0<D)
    (hcap:phaseOUKernel r σ ∘ₘ μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (hα:((phaseOUKernel r σ ∘ₘ μ) {z|vstar<‖flightVelocity (gradient U) h z‖}).toReal<1)
    (hc1:θ*h*(13/2:ℝ)≤(1-r^2)/4)
    (hc2:2*θ*(1-r^2)≤r*h*(1/2:ℝ)/2)
    (hc3:θ*r*h*(1/2:ℝ)/2≤(1-r^2)/4) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    let K := gaussianSandwichKernel e e.measurable r σ
    entropyCorrector a θ (K ∘ₘ μ)≤
      (1-θ*r*(1/2:ℝ)*h/(2*(1+θ)))*entropyCorrector a θ μ+
      (expectedGradientCorrection U h (K ∘ₘ μ)-expectedGradientCorrection U h μ)+
      expectedComparisonRemainder U h vstar (phaseOUKernel r σ ∘ₘ μ)+
      θ*h*a.comparisonCorrectorError (phaseOUKernel r σ ∘ₘ μ) h D vstar := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := comparisonVerletEquiv (gradient U) hg h vstar
  let ν := phaseOUKernel r σ ∘ₘ μ
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  have hKν : klDiv ν (phaseGibbs U)≠∞ :=
    ne_top_of_le_ne_top hK (klDiv_step_le _ _ _ (phaseOUKernel_invariant U r σ hn))
  have hstage := a.proposition_5_9 hsm hstar hzero hh hL ν hν hKν D hD hcap vstar hα
  have hb := a.comparisonCorrectorError_nonneg hstar hzero ν hh D vstar
  have hs := a.sandwich_entropy_corrector_step μ e (comparisonVerlet_measurePreserving (gradient U) hg h vstar)
    r σ h (13/2) (1/2) (a.comparisonCorrectorError ν h D vstar) θ hμ
    (a.comparisonVerlet_memLp hν h vstar) hK hr hσ hn hh.le (by norm_num) (by norm_num) hb hθ
    (by simpa using hc1) (by simpa using hc2) (by simpa using hc3) hstage
  have ht := a.comparison_sandwich_energy_telescope μ hμ h r σ vstar
  dsimp only at hs ht ⊢
  rw [ht] at hs
  simpa only [entropyCorrector,Real.sqrt_one,one_mul,mul_one,add_assoc] using hs

end PersistencePays
#print axioms PersistencePays.A1.comparison_entropy_corrector_step
