import PersistencePays.QuadraticDistance
import Mathlib.Topology.Sequences

/-! Continuity of the quadratic optimum and closedness of optimal plans. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem wassersteinTwo_comm (μ ν : ProbabilityMeasure E) :
    wassersteinTwo μ ν=wassersteinTwo ν μ := by unfold wassersteinTwo; rw [cost_comm]

theorem wassersteinTwo_difference_le (μ ν ξ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hξ : MemLp id 2 (ξ : Measure E)) :
    |wassersteinTwo μ ξ-wassersteinTwo ν ξ| ≤ wassersteinTwo μ ν := by
  have h1 := wassersteinTwo_triangle μ ν ξ hμ hν hξ
  have h2 := wassersteinTwo_triangle ν μ ξ hν hμ hξ
  rw [wassersteinTwo_comm ν μ] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem wassersteinTwo_tendsto_fixed (μn : ℕ → ProbabilityMeasure E) (μ ξ : ProbabilityMeasure E)
    (hμn : ∀ n, MemLp id 2 (μn n : Measure E)) (hμ : MemLp id 2 (μ : Measure E))
    (hξ : MemLp id 2 (ξ : Measure E))
    (hd : Tendsto (fun n => wassersteinTwo (μn n) μ) atTop (𝓝 0)) :
    Tendsto (fun n => wassersteinTwo (μn n) ξ) atTop (𝓝 (wassersteinTwo μ ξ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hd ε hε
  refine ⟨N,fun n hn => ?_⟩
  have hb := wassersteinTwo_difference_le (μn n) μ ξ (hμn n) hμ hξ
  have he := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ wassersteinTwo (μn n) μ from Real.sqrt_nonneg _)] at he
  rw [Real.dist_eq]
  exact hb.trans_lt he

theorem cost_ofReal_wassersteinTwo_sq (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) :
    ENNReal.ofReal ((wassersteinTwo μ ν)^2) = cost μ ν := by
  rw [wassersteinTwo, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
  exact cost_finite μ ν hμ.integrable_norm_pow' hν.integrable_norm_pow'

theorem cost_tendsto_fixed (μn : ℕ → ProbabilityMeasure E) (μ ξ : ProbabilityMeasure E)
    (hμn : ∀ n, MemLp id 2 (μn n : Measure E)) (hμ : MemLp id 2 (μ : Measure E))
    (hξ : MemLp id 2 (ξ : Measure E))
    (hd : Tendsto (fun n => wassersteinTwo (μn n) μ) atTop (𝓝 0)) :
    Tendsto (fun n => cost (μn n) ξ) atTop (𝓝 (cost μ ξ)) := by
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((wassersteinTwo_tendsto_fixed μn μ ξ hμn hμ hξ hd).pow 2)
  simp only [Function.comp_def] at hh
  simpa only [cost_ofReal_wassersteinTwo_sq _ _ hμ hξ,
    cost_ofReal_wassersteinTwo_sq _ _ (hμn _) hξ] using hh

theorem plans_limit (μn νn : ℕ → ProbabilityMeasure E) (μ ν : ProbabilityMeasure E)
    (πn : ℕ → ProbabilityMeasure (E × E)) (π : ProbabilityMeasure (E × E))
    (hπn : ∀ n, πn n ∈ plans (μn n) (νn n))
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν))
    (hπ : Tendsto πn atTop (𝓝 π)) : π ∈ plans μ ν := by
  constructor
  · have hh := (ProbabilityMeasure.continuous_map continuous_fst).continuousAt.tendsto.comp hπ
    have he : (fun n => (πn n).map measurable_fst.aemeasurable) = μn := funext (fun n => (hπn n).1)
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact tendsto_nhds_unique hh hμ
  · have hh := (ProbabilityMeasure.continuous_map continuous_snd).continuousAt.tendsto.comp hπ
    have he : (fun n => (πn n).map measurable_snd.aemeasurable) = νn := funext (fun n => (hπn n).2)
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact tendsto_nhds_unique hh hν

theorem optimalPlan_limit (μn : ℕ → ProbabilityMeasure E) (μ ξ : ProbabilityMeasure E)
    (πn : ℕ → ProbabilityMeasure (E × E)) (π : ProbabilityMeasure (E × E))
    (hπn : ∀ n, IsOptimal (μn n) ξ (πn n))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure E)) (hμ : MemLp id 2 (μ : Measure E))
    (hξ : MemLp id 2 (ξ : Measure E))
    (hw : Tendsto μn atTop (𝓝 μ)) (hd : Tendsto (fun n => wassersteinTwo (μn n) μ) atTop (𝓝 0))
    (hπ : Tendsto πn atTop (𝓝 π)) : IsOptimal μ ξ π := by
  have hp := plans_limit μn (fun _ => ξ) μ ξ πn π (fun n => (hπn n).1) hw tendsto_const_nhds hπ
  refine ⟨hp,le_antisymm ?_ (iInf₂_le π hp)⟩
  have hc : Tendsto (fun n => squaredCost (πn n)) atTop (𝓝 (cost μ ξ)) := by
    simp_rw [(hπn _).2]
    exact cost_tendsto_fixed μn μ ξ hμn hμ hξ hd
  apply le_of_forall_lt
  intro b hb
  obtain ⟨c,hbc,hcπ⟩ := exists_between hb
  have he := hπ.eventually
    ((cost_lowerSemicontinuous (fun z : E × E => ‖z.1-z.2‖^2) (by fun_prop) π) c hcπ)
  exact hbc.trans_le (ge_of_tendsto hc (he.mono (fun _ h => h.le)))

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.optimalPlan_limit
