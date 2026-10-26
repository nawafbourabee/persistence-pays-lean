import PersistencePays.UnadjustedEntropyStep
import PersistencePays.EntropyFiniteHorizon

/-! Finite-horizon entropy decay for the literal numerical OBABO chain. The
signed gradient correction is telescoped, while the finite remainder bound is
kept explicit so it can be instantiated by the second/third flight moments. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unadjustedEntropyLaw {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (μ : Measure (E×E)) (n : ℕ) : Measure (E×E) :=
  iterateKernel (OBABOPath.unadjustedStepKernel (gradient U)
    (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ) n ∘ₘ μ

instance unadjustedEntropyLaw_probability {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (μ : Measure (E×E)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (unadjustedEntropyLaw a h r σ μ n) := by
  unfold unadjustedEntropyLaw
  infer_instance

@[simp] theorem unadjustedEntropyLaw_zero {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (μ : Measure (E×E)) : unadjustedEntropyLaw a h r σ μ 0=μ := by
  simp [unadjustedEntropyLaw,iterateKernel]

theorem unadjustedEntropyLaw_succ {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (μ : Measure (E×E)) [SFinite μ] (n : ℕ) :
    unadjustedEntropyLaw a h r σ μ (n+1) =
      OBABOPath.unadjustedStepKernel (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ ∘ₘ
          unadjustedEntropyLaw a h r σ μ n := by
  simp only [unadjustedEntropyLaw,iterateKernel,← Measure.comp_assoc]

def unadjustedEntropyDefect {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ θ : ℝ) (μ : Measure (E×E)) (k : ℕ) : ℝ :=
  let ν := phaseOUKernel r σ ∘ₘ unadjustedEntropyLaw a h r σ μ k
  expectedVerletRemainder U h ν+θ*Real.sqrt m*h*((13/4:ℝ)*L*h^2*expectedFlightSquare U h ν)

theorem A1.unadjusted_entropy_bound_up_to {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (r σ h θ rate B : ℝ) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1)
    (hh : 0 < h) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hc1 : θ*(Real.sqrt m*h)*(13/2:ℝ) ≤ (1-r^2)/4)
    (hc2 : 2*θ*(1-r^2) ≤ r*(Real.sqrt m*h)*(1/2:ℝ)/2)
    (hc3 : θ*r*(Real.sqrt m*h)*(1/2:ℝ)/2 ≤ (1-r^2)/4)
    (hrate : rate = θ*r*(1/2:ℝ)*Real.sqrt m/(2*(1+θ)))
    (hrateh : 0 < rate*h) (hrateh1 : rate*h ≤ 1) (hB : 0 ≤ B)
    (n : ℕ) (hdef : ∀ k, k<n → unadjustedEntropyDefect a h r σ θ μ k ≤ B) :
    (klDiv (unadjustedEntropyLaw a h r σ μ n) (phaseGibbs U)).toReal ≤
      ((1+θ)/(1-θ))*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
        (expectedGradientCorrection U h (unadjustedEntropyLaw a h r σ μ n)+B/(rate*h))/(1-θ) := by
  let p := unadjustedEntropyLaw a h r σ μ
  let Ent := fun k => (klDiv (p k) (phaseGibbs U)).toReal
  let H := fun k => entropyCorrector a θ (p k)
  let g := fun k => expectedGradientCorrection U h (p k)
  have hfin (k : ℕ) : MemLp id 2 (p k) ∧ klDiv (p k) (phaseGibbs U) ≠ ∞ :=
    a.unadjusted_entropy_iterates μ h r σ hn hμ hK k
  have hstep (k : ℕ) (hk : k<n) : H (k+1) ≤ (1-rate*h)*H k+(g (k+1)-g k)+B := by
    have hs := a.unadjusted_entropy_corrector_step hsm (p k) (hfin k).1 (hfin k).2
      r σ h θ hr hσ hn hh hθ hc1 hc2 hc3
    have he : θ*r*(1/2:ℝ)*(Real.sqrt m*h)/(2*(1+θ))=rate*h := by rw [hrate]; ring
    dsimp only at hs
    rw [he] at hs
    have hp : OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ ∘ₘ p k = p (k+1) :=
      (unadjustedEntropyLaw_succ a h r σ μ k).symm
    simp only [hp] at hs
    have hb := hdef k hk
    change expectedVerletRemainder U h (phaseOUKernel r σ ∘ₘ p k)+
      θ*Real.sqrt m*h*((13/4:ℝ)*L*h^2*expectedFlightSquare U h (phaseOUKernel r σ ∘ₘ p k)) ≤ B at hb
    change entropyCorrector a θ (p (k+1)) ≤ (1-rate*h)*entropyCorrector a θ (p k)+
      (expectedGradientCorrection U h (p (k+1))-expectedGradientCorrection U h (p k))+B
    linarith
  have hg (k : ℕ) : 0 ≤ g k := (a.expectedGradientCorrection_bounds (p k) (hfin k).1 h).1
  have hcompare (k : ℕ) : (1-θ)*Ent k ≤ H k ∧ H k ≤ (1+θ)*Ent k :=
    a.entropy_corrector_comparison (p k) (hfin k).1 (hfin k).2 θ hθ
  have hb := entropy_recurrence_bound_up_to Ent H g hθ hθ1 hrateh hrateh1 hB
    (fun _ => ENNReal.toReal_nonneg) hg hcompare n hstep
  simpa only [Ent,H,g,p,unadjustedEntropyLaw_zero] using hb

end PersistencePays
#print axioms PersistencePays.A1.unadjusted_entropy_bound_up_to
