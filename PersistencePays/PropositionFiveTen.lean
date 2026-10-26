import PersistencePays.ComparisonEntropyDecay
import PersistencePays.ComparisonCorrectorRemainder

/-! Literal cold-start comparison-chain version of Proposition 5.10. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem comparisonEntropyLaw_cold {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (h r σ vstar:ℝ) (z:E×E) (n:ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    comparisonEntropyLaw a h r σ vstar (OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z) n=
      OBABOPath.comparisonChainLaw (gradient U) hg h r σ vstar n z := rfl

theorem A1.proposition_5_10 {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hsm:GaussianSmoothedFreeTransportBound a) (hstar:a.minimizer=0) (hzero:U 0=0)
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
  dsimp only
  intro hcap hα hTb hBb
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r:=Real.exp (-h)
  let σ:=Real.sqrt (1-Real.exp (-2*h))
  let μ:=OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z
  let p:=comparisonEntropyLaw a h r σ vstar μ
  have hσ:0<σ := Real.sqrt_pos.mpr (by
    have he:=Real.exp_lt_one_iff.mpr (show -2*h<0 by linarith)
    linarith)
  have hn:r^2+σ^2=1 := (normalized_ou_coefficients h hh.le).2.2.2.1
  have hμ:MemLp id 2 μ := by
    have ht:=OBABOPath.unadjusted_kernel_finite_moments a h r σ 1 z 2 (by norm_num)
    rw [OBABOPath.unadjustedEpochKernel_eq_iterate] at ht
    simpa only [iterateKernel,Kernel.comp_id] using ht
  have hK:klDiv μ (phaseGibbs U)≠∞ := a.unadjusted_step_entropy_finite h r σ hh hσ z
  have hTbound (k:ℕ) (hk:k<n) : expectedComparisonRemainder U h vstar (phaseOUKernel r σ ∘ₘ p k)≤T := by
    let ν:=phaseOUKernel r σ ∘ₘ p k
    have hp2:MemLp id 2 (p k) := a.comparison_iterates_memLp μ 2 (by norm_num) hμ h vstar r σ k
    have ht:=a.comparisonRemainder_integrable ν (phaseOUKernel_memLp (p k) 2 (by norm_num) hp2 r σ) h vstar
    exact (integral_mono ht (ht.sup (integrable_const 0)) (fun w=>le_max_left _ _)).trans (hTb k hk)
  have hBbound (k:ℕ) (hk:k<n) : a.comparisonCorrectorError (phaseOUKernel r σ ∘ₘ p k) h D vstar≤B := by
    rw [a.comparisonCorrectorError_eq_remainder]
    exact hBb k hk
  exact a.comparison_entropy_decay hsm hstar hzero hh hmax hL μ hμ hK D vstar T B hD hT hB n
    hcap hα hTbound hBbound

end PersistencePays
#print axioms PersistencePays.A1.proposition_5_10
