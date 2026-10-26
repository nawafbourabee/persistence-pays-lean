import PersistencePays.GaussianConditionalConvergence
import PersistencePays.TransportRegularizationCorrector
import PersistencePays.GibbsCorrector

/-! The fully checked general-law passage in Lemma 4.8. The only input in the
final reduction is the inequality for actual Gaussian smoothings of bounded
laws. That analytic inequality is kept explicit until Lemma 4.5 is assembled. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def freeTransportRHS (μ : Measure (E×E)) (ξ : Measure E) (t : ℝ) : ℝ :=
  7*(∫ s in (0:ℝ)..t, (conditionalGaussianEntropy μ (stdGaussian E) s).toReal) -
    t*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal -
    t*(boltzmannEntropy μ.fst-boltzmannEntropy ξ)

theorem regularizedGaussian_freeTransportRHS_tendsto
    (μ : ProbabilityMeasure (E×E)) (ξ : Measure E) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => freeTransportRHS
      (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) ξ t) atTop
      (𝓝 (freeTransportRHS (μ : Measure (E×E)) ξ t)) := by
  have hL := regularizedGaussian_boltzmann_tendsto μ ε hμ hK hε 0
  simp only [transportPosition_zero] at hL
  exact (((regularizedGaussian_conditional_integral_tendsto μ ε hμ hK hε ht).const_mul 7).sub
    ((regularizedGaussian_conditional_entropy_tendsto μ ε hμ hK hε 0).const_mul t)).sub
    ((hL.sub_const _).const_mul t)

theorem A1.freeTransportRHS_integral_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) {t : ℝ} (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, (6*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
      (boltzmannEntropy (transportPosition μ s)-boltzmannEntropy (positionGibbs U)))) =
      freeTransportRHS μ (positionGibbs U) t := by
  have hi := (a.lemma_4_9_i μ ht hμ hK).2.1
  have he (s : ℝ) : 6*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
      (boltzmannEntropy (transportPosition μ s)-boltzmannEntropy (positionGibbs U)) =
      7*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
        ((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
          boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) := by
    have hh := (a.free_transport_entropy_balance μ hμ hK s).2.2
    linarith
  simp_rw [he]
  rw [intervalIntegral.integral_sub (hi.const_mul 7) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,freeTransportRHS]
  ring

/-- All convergence hypotheses of the passage are proved for the displayed
actual approximants. Only their smoothed free-flight bound is an input. -/
theorem A1.free_transport_of_regularized_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E))) (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) {t : ℝ} (ht : 0 < t)
    (hb : ∀ n, a.corrector (transportJoint
      (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) t)-
      a.corrector (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) ≤
      freeTransportRHS (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) (positionGibbs U) t) :
    a.corrector (transportJoint (μ : Measure (E×E)) t)-a.corrector (μ : Measure (E×E)) ≤
      freeTransportRHS (μ : Measure (E×E)) (positionGibbs U) t := by
  have hG := a.phaseGaussian_entropy_finite (μ : Measure (E×E)) hμ hK
  have hC0 := regularizedGaussian_corrector_tendsto μ a.targetProbability ε hμ a.position_memLp_two hG hε 0
  simp only [transportJoint_zero] at hC0
  have hCt := regularizedGaussian_corrector_tendsto μ a.targetProbability ε hμ a.position_memLp_two hG hε t
  exact le_of_tendsto_of_tendsto (hCt.sub hC0)
    (regularizedGaussian_freeTransportRHS_tendsto μ (positionGibbs U) ε hμ hG hε ht)
    (Filter.Eventually.of_forall hb)

/-- Explicit boundary: this predicate is the bounded-support Gaussian-smoothed
case obtained from Lemma 4.5 and the conditional mean-entropy inequality. -/
def GaussianSmoothedFreeTransportBound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) : Prop :=
  ∀ (ν : ProbabilityMeasure (E×E)), (∃ R : ℝ, ∀ᵐ z ∂(ν : Measure (E×E)), ‖z‖ ≤ R) →
    ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 < t →
    a.corrector (transportJoint (additiveNoiseProbability ν gaussianPairProbability ε : Measure (E×E)) t)-
      a.corrector (additiveNoiseProbability ν gaussianPairProbability ε : Measure (E×E)) ≤
      freeTransportRHS (additiveNoiseProbability ν gaussianPairProbability ε : Measure (E×E)) (positionGibbs U) t

/-- Lemma 4.8 follows from precisely the smooth bounded-law case. No limiting,
entropy continuity, or optimal-coupling stability premise is left over. -/
theorem A1.free_transport_of_smoothed_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U) ≠ ∞) {t : ℝ} (ht : 0 < t) :
    a.corrector (transportJoint (μ : Measure (E×E)) t)-a.corrector (μ : Measure (E×E)) ≤
      freeTransportRHS (μ : Measure (E×E)) (positionGibbs U) t := by
  apply a.free_transport_of_regularized_bound μ (fun n => 1/((n:ℝ)+1)) hμ hK
    tendsto_one_div_add_atTop_nhds_zero_nat ht
  intro n
  exact hsm (ballTruncation μ n) ⟨_,ballTruncation_ae_bounded μ n⟩ _ (by positivity) t ht

end PersistencePays
#print axioms PersistencePays.A1.free_transport_of_smoothed_bound
