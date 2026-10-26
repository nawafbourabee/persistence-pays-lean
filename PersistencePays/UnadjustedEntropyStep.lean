import PersistencePays.SandwichCorrector
import PersistencePays.VerletCorrector
import PersistencePays.GradientCorrectionExpectation
import PersistencePays.EntropyParameters

/-! The actual unadjusted OBABO one-step entropy recurrence, with the signed
G correction retained. Only the independently constructed smooth free-flight
inequality remains explicit as a hypothesis. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def entropyCorrector {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (θ : ℝ)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] : ℝ :=
  (klDiv μ (phaseGibbs U)).toReal+θ*Real.sqrt m*a.corrector μ

def expectedFlightSquare (U : E → ℝ) (h : ℝ) (μ : Measure (E×E)) : ℝ :=
  ∫ z,‖flightVelocity (gradient U) h z‖^2 ∂μ

theorem A1.unadjusted_entropy_corrector_step {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (r σ h θ : ℝ) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1) (hh : 0 < h) (hθ : 0 ≤ θ)
    (hc1 : θ*(Real.sqrt m*h)*(13/2:ℝ) ≤ (1-r^2)/4)
    (hc2 : 2*θ*(1-r^2) ≤ r*(Real.sqrt m*h)*(1/2:ℝ)/2)
    (hc3 : θ*r*(Real.sqrt m*h)*(1/2:ℝ)/2 ≤ (1-r^2)/4) :
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    entropyCorrector a θ (K ∘ₘ μ) ≤
      (1-θ*r*(1/2:ℝ)*(Real.sqrt m*h)/(2*(1+θ)))*entropyCorrector a θ μ+
      (expectedGradientCorrection U h (K ∘ₘ μ)-expectedGradientCorrection U h μ)+
      expectedVerletRemainder U h (phaseOUKernel r σ ∘ₘ μ)+
      θ*Real.sqrt m*h*((13/4:ℝ)*L*h^2*expectedFlightSquare U h (phaseOUKernel r σ ∘ₘ μ)) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := verletEquiv (gradient U) hg h
  let ν := phaseOUKernel r σ ∘ₘ μ
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  have hKν : klDiv ν (phaseGibbs U) ≠ ∞ :=
    ne_top_of_le_ne_top hK (klDiv_step_le _ _ _ (phaseOUKernel_invariant U r σ hn))
  have hstage := a.verlet_corrector_bound hsm ν hν hKν hh
  have hb : 0 ≤ (13/4:ℝ)*L*h^2*expectedFlightSquare U h ν :=
    mul_nonneg (by positivity [a.L_pos]) (integral_nonneg (fun _ => sq_nonneg _))
  have hs := a.sandwich_entropy_corrector_step μ e (verlet_measurePreserving (gradient U) hg h)
    r σ h (13/2) (1/2) ((13/4)*L*h^2*expectedFlightSquare U h ν) θ hμ
    (a.verlet_memLp hν h) hK hr hσ hn hh.le (by norm_num) (by norm_num) hb hθ hc1 hc2 hc3 hstage
  have ht := a.verlet_sandwich_energy_telescope μ hμ h r σ
  dsimp only at hs ht ⊢
  rw [ht] at hs
  have hOut : gaussianSandwichKernel e e.measurable r σ =
      OBABOPath.unadjustedStepKernel (gradient U) hg h r σ := by
    rw [unadjustedStepKernel_eq_sandwich]
    rfl
  have hOut' : gaussianSandwichKernel (verletEquiv (gradient U) hg h)
      (verletEquiv (gradient U) hg h).measurable r σ =
      OBABOPath.unadjustedStepKernel (gradient U) hg h r σ := hOut
  simp only [hOut,hOut'] at hs
  unfold entropyCorrector
  dsimp only [ν] at hs
  convert hs using 1 <;> ring

end PersistencePays
#print axioms PersistencePays.A1.unadjusted_entropy_corrector_step
