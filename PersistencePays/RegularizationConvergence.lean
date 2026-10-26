import PersistencePays.BallTruncation
import PersistencePays.TruncationCoupling
import PersistencePays.AdditiveNoiseMoments
import PersistencePays.AdditiveNoiseTransport

/-! The actual bounded-support truncation followed by vanishing independent
noise converges weakly, in quadratic moments, and in genuine transport cost. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [PolishSpace S]

def regularizedProbability (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure S := additiveNoiseProbability (ballTruncation μ n) γ (ε n)

theorem regularizedProbability_memLp (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ)
    {p : ℝ≥0∞} (hμ : MemLp id p (μ : Measure S)) (hγ : MemLp id p (γ : Measure S)) (n : ℕ) :
    MemLp id p (regularizedProbability μ γ ε n : Measure S) :=
  additiveNoiseProbability_memLp _ _ _
    (memLp_conditionedProbability μ _ _ hμ) hγ

theorem regularizedProbability_weak (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) : Tendsto (regularizedProbability μ γ ε) atTop (𝓝 μ) := by
  have hh := additiveNoiseProbability_tendsto (ballTruncation μ) μ γ ε (ballTruncation_tendsto μ) hε
  change Tendsto (fun n => additiveNoiseProbability (ballTruncation μ n) γ (ε n)) atTop (𝓝 μ)
  rw [additiveNoiseProbability_zero] at hh
  exact hh

theorem regularizedProbability_moment (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure S)) (hγ : MemLp id 2 (γ : Measure S))
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖x‖^2 ∂(regularizedProbability μ γ ε n : Measure S)) atTop
      (𝓝 (∫ x, ‖x‖^2 ∂(μ : Measure S))) :=
  additiveNoise_moment_tendsto (ballTruncation μ) μ γ ε
    (fun _ => memLp_conditionedProbability μ _ _ hμ) hγ hε
    (ballTruncation_integral_tendsto μ hμ.integrable_norm_pow')

theorem additiveNoise_cost_bound (μ ν γ : ProbabilityMeasure S) (ε : ℝ)
    (hμ : MemLp id 2 (μ : Measure S)) (hν : MemLp id 2 (ν : Measure S))
    (hγ : MemLp id 2 (γ : Measure S)) :
    (QuadraticTransport.cost (additiveNoiseProbability μ γ ε) ν).toReal ≤
      2*(QuadraticTransport.cost μ ν).toReal+2*ε^2*(∫ x, ‖x‖^2 ∂(γ : Measure S)) := by
  obtain ⟨π,hπ⟩ := QuadraticTransport.exists_optimal μ ν
  have hnew := noisyTransportPlan_mem μ ν γ π hπ.1 ε
  have hfinite := QuadraticTransport.squaredCost_finite _ _ _ hnew
    (additiveNoiseProbability_memLp μ γ ε hμ hγ).integrable_norm_pow' hν.integrable_norm_pow'
  have hlo : QuadraticTransport.cost (additiveNoiseProbability μ γ ε) ν ≤
      QuadraticTransport.squaredCost (noisyTransportPlan π γ ε) := iInf₂_le _ hnew
  have hb := (ENNReal.toReal_mono hfinite hlo).trans
    (noisyTransportPlan_cost_bound μ ν γ π hπ.1 ε hμ hν hγ)
  simpa only [hπ.2] using hb

theorem regularizedProbability_cost (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure S)) (hγ : MemLp id 2 (γ : Measure S))
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (QuadraticTransport.cost (regularizedProbability μ γ ε n) μ).toReal)
      atTop (𝓝 0) := by
  have htr := conditioned_cost_tendsto μ (truncationBall μ) (truncationBall_measurable μ)
    (truncationBall_mass_ne_zero μ) (Filter.Eventually.of_forall (truncationBall_exhausts μ)) hμ
  have heps := ((hε.pow 2).const_mul 2).mul_const (∫ x, ‖x‖^2 ∂(γ : Measure S))
  have hh := (htr.const_mul 2).add heps
  simp only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,zero_add] at hh
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hh
  intro n
  exact additiveNoise_cost_bound (ballTruncation μ n) μ γ (ε n)
    (memLp_conditionedProbability μ _ _ hμ) hμ hγ

end PersistencePays
#print axioms PersistencePays.regularizedProbability_weak
#print axioms PersistencePays.regularizedProbability_moment
#print axioms PersistencePays.regularizedProbability_cost
