import PersistencePays.ComparisonEntropyStep
import PersistencePays.ComparisonChainBounds
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

def comparisonEntropyLaw {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (μ : Measure (E×E)) (n : ℕ) : Measure (E×E) :=
  iterateKernel (gaussianSandwichKernel (comparisonVerlet (gradient U) h vstar)
    (comparisonVerlet_measurePreserving (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar).measurable r σ) n ∘ₘ μ

instance comparisonEntropyLaw_probability {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (μ : Measure (E×E)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (comparisonEntropyLaw a h r σ vstar μ n) := by
  unfold comparisonEntropyLaw
  infer_instance

@[simp] theorem comparisonEntropyLaw_zero {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (μ : Measure (E×E)) : comparisonEntropyLaw a h r σ vstar μ 0=μ := by
  simp [comparisonEntropyLaw,iterateKernel]

theorem comparisonEntropyLaw_succ {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (μ : Measure (E×E)) [SFinite μ] (n : ℕ) :
    comparisonEntropyLaw a h r σ vstar μ (n+1) =
      gaussianSandwichKernel (comparisonVerlet (gradient U) h vstar)
    (comparisonVerlet_measurePreserving (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar).measurable r σ ∘ₘ
          comparisonEntropyLaw a h r σ vstar μ n := by
  simp only [comparisonEntropyLaw,iterateKernel,← Measure.comp_assoc]

def comparisonEntropyDefect {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ θ D vstar : ℝ) (μ : Measure (E×E)) [IsProbabilityMeasure μ] (k : ℕ) : ℝ :=
  let ν := phaseOUKernel r σ ∘ₘ comparisonEntropyLaw a h r σ vstar μ k
  expectedComparisonRemainder U h vstar ν+θ*h*a.comparisonCorrectorError ν h D vstar

theorem A1.comparison_entropy_bound_up_to {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hsm : GaussianSmoothedFreeTransportBound a) (hstar:a.minimizer=0) (hzero:U 0=0)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (r σ h θ D vstar rate B : ℝ) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1)
    (hh : 0 < h) (hL:L*h^2≤1/2) (hD:0<D) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hc1 : θ*(h)*(13/2:ℝ) ≤ (1-r^2)/4)
    (hc2 : 2*θ*(1-r^2) ≤ r*(h)*(1/2:ℝ)/2)
    (hc3 : θ*r*(h)*(1/2:ℝ)/2 ≤ (1-r^2)/4)
    (hrate : rate = θ*r*(1/2:ℝ)/(2*(1+θ)))
    (hrateh : 0 < rate*h) (hrateh1 : rate*h ≤ 1) (hB : 0 ≤ B)
    (n : ℕ)
    (hcap:∀k,k<n → phaseOUKernel r σ ∘ₘ comparisonEntropyLaw a h r σ vstar μ k≤
      ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (hα:∀k,k<n → ((phaseOUKernel r σ ∘ₘ comparisonEntropyLaw a h r σ vstar μ k)
      {z|vstar<‖flightVelocity (gradient U) h z‖}).toReal<1)
    (hdef : ∀ k, k<n → comparisonEntropyDefect a h r σ θ D vstar μ k ≤ B) :
    (klDiv (comparisonEntropyLaw a h r σ vstar μ n) (phaseGibbs U)).toReal ≤
      ((1+θ)/(1-θ))*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
        (expectedGradientCorrection U h (comparisonEntropyLaw a h r σ vstar μ n)+B/(rate*h))/(1-θ) := by
  let p := comparisonEntropyLaw a h r σ vstar μ
  let Ent := fun k => (klDiv (p k) (phaseGibbs U)).toReal
  let H := fun k => entropyCorrector a θ (p k)
  let g := fun k => expectedGradientCorrection U h (p k)
  have hfin (k : ℕ) : MemLp id 2 (p k) ∧ klDiv (p k) (phaseGibbs U) ≠ ∞ :=
    ⟨a.comparison_iterates_memLp μ 2 (by norm_num) hμ h vstar r σ k,
      a.comparison_entropy_iterates μ h vstar r σ hn hμ hK k⟩
  have hstep (k : ℕ) (hk : k<n) : H (k+1) ≤ (1-rate*h)*H k+(g (k+1)-g k)+B := by
    have hs := a.comparison_entropy_corrector_step hsm hstar hzero (p k) (hfin k).1 (hfin k).2
      r σ h θ D vstar hr hσ hn hh hL hθ hD (hcap k hk) (hα k hk) hc1 hc2 hc3
    have he : θ*r*(1/2:ℝ)*(h)/(2*(1+θ))=rate*h := by rw [hrate]; ring
    dsimp only at hs
    rw [he] at hs
    have hp : gaussianSandwichKernel (comparisonVerlet (gradient U) h vstar)
      (comparisonVerlet_measurePreserving (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar).measurable r σ ∘ₘ p k = p (k+1) :=
      (comparisonEntropyLaw_succ a h r σ vstar μ k).symm
    change entropyCorrector a θ (gaussianSandwichKernel (comparisonVerlet (gradient U) h vstar)
      (comparisonVerlet_measurePreserving (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar).measurable r σ ∘ₘ p k) ≤ _ at hs
    have hp' : gaussianSandwichKernel (comparisonVerletEquiv (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar)
      (comparisonVerletEquiv (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h vstar).measurable r σ ∘ₘ p k = p (k+1) := hp
    simp only [hp,hp'] at hs
    have hb := hdef k hk
    change expectedComparisonRemainder U h vstar (phaseOUKernel r σ ∘ₘ p k)+
      θ*h*a.comparisonCorrectorError (phaseOUKernel r σ ∘ₘ p k) h D vstar ≤ B at hb
    change entropyCorrector a θ (p (k+1)) ≤ (1-rate*h)*entropyCorrector a θ (p k)+
      (expectedGradientCorrection U h (p (k+1))-expectedGradientCorrection U h (p k))+B
    linarith
  have hg (k : ℕ) : 0 ≤ g k := (a.expectedGradientCorrection_bounds (p k) (hfin k).1 h).1
  have hcompare (k : ℕ) : (1-θ)*Ent k ≤ H k ∧ H k ≤ (1+θ)*Ent k :=
    a.entropy_corrector_comparison (p k) (hfin k).1 (hfin k).2 θ hθ
  have hb := entropy_recurrence_bound_up_to Ent H g hθ hθ1 hrateh hrateh1 hB
    (fun _ => ENNReal.toReal_nonneg) hg hcompare n hstep
  simpa only [Ent,H,g,p,comparisonEntropyLaw_zero] using hb

end PersistencePays
#print axioms PersistencePays.A1.comparison_entropy_bound_up_to
