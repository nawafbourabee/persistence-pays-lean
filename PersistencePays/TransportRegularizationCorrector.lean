import PersistencePays.TransportApproximation

/-! The literal truncation/Gaussian approximants converge in corrector after
any fixed free flight. Actual transported couplings discharge the transport
cost hypothesis of corrector stability. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem freeTransport_sub (t : ℝ) (z w : E×E) :
    freeTransport t z-freeTransport t w = freeTransport t (z-w) := by
  ext <;> simp [freeTransport,drift,smul_sub] <;> abel

theorem transported_cost_le (μ ν : ProbabilityMeasure (E×E)) (t : ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E))) (hν : MemLp id 2 (ν : Measure (E×E))) :
    (QuadraticTransport.cost (transportProbability (μ : Measure (E×E)) t)
      (transportProbability (ν : Measure (E×E)) t)).toReal ≤
      (1+|t|)^2*(QuadraticTransport.cost μ ν).toReal := by
  obtain ⟨π,hπ⟩ := QuadraticTransport.exists_optimal μ ν
  let ρ : ProbabilityMeasure ((E×E)×(E×E)) := π.map
    (show Measurable (fun z : (E×E)×(E×E) => (freeTransport t z.1,freeTransport t z.2)) by
      unfold freeTransport drift; fun_prop).aemeasurable
  have hρ : ρ ∈ QuadraticTransport.plans (transportProbability (μ : Measure (E×E)) t)
      (transportProbability (ν : Measure (E×E)) t) := by
    constructor
    · apply Subtype.ext
      have he := congrArg (fun p : ProbabilityMeasure (E×E) => (p : Measure (E×E)).map (freeTransport t)) hπ.1.1
      simp only [ProbabilityMeasure.toMeasure_map] at he
      rw [Measure.map_map (measurable_freeTransport t) measurable_fst] at he
      change ((π : Measure ((E×E)×(E×E))).map (fun z => (freeTransport t z.1,freeTransport t z.2))).map Prod.fst = _
      rw [Measure.map_map measurable_fst (by unfold freeTransport drift; fun_prop)]
      exact he
    · apply Subtype.ext
      have he := congrArg (fun p : ProbabilityMeasure (E×E) => (p : Measure (E×E)).map (freeTransport t)) hπ.1.2
      simp only [ProbabilityMeasure.toMeasure_map] at he
      rw [Measure.map_map (measurable_freeTransport t) measurable_snd] at he
      change ((π : Measure ((E×E)×(E×E))).map (fun z => (freeTransport t z.1,freeTransport t z.2))).map Prod.snd = _
      rw [Measure.map_map measurable_snd (by unfold freeTransport drift; fun_prop)]
      exact he
  have hi := QuadraticTransport.squaredCost_integrable μ ν π hπ.1
    hμ.integrable_norm_pow' hν.integrable_norm_pow'
  have hj := QuadraticTransport.squaredCost_integrable _ _ ρ hρ
    (transportProbability_memLp _ hμ t).integrable_norm_pow' (transportProbability_memLp _ hν t).integrable_norm_pow'
  have hjf := QuadraticTransport.squaredCost_finite _ _ ρ hρ
    (transportProbability_memLp _ hμ t).integrable_norm_pow' (transportProbability_memLp _ hν t).integrable_norm_pow'
  have hlo : QuadraticTransport.cost (transportProbability (μ : Measure (E×E)) t)
      (transportProbability (ν : Measure (E×E)) t) ≤ QuadraticTransport.squaredCost ρ := iInf₂_le _ hρ
  apply (ENNReal.toReal_mono hjf hlo).trans
  rw [← hπ.2]
  unfold QuadraticTransport.squaredCost
  rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z : (E×E)×(E×E) =>
    sq_nonneg ‖z.1-z.2‖)) hj.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z : (E×E)×(E×E) =>
    sq_nonneg ‖z.1-z.2‖)) hi.aestronglyMeasurable]
  change (∫ z,‖z.1-z.2‖^2 ∂(π : Measure ((E×E)×(E×E))).map
    (fun z => (freeTransport t z.1,freeTransport t z.2))) ≤ _
  rw [integral_map (by unfold freeTransport drift; fun_prop) (by fun_prop),← integral_const_mul]
  apply integral_mono
    ((integrable_map_measure (by fun_prop) (by unfold freeTransport drift; fun_prop)).mp hj)
    (hi.const_mul _)
  intro z
  change ‖freeTransport t z.1-freeTransport t z.2‖^2 ≤ (1+|t|)^2*‖z.1-z.2‖^2
  rw [freeTransport_sub]
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (freeTransport_norm_le t (z.1-z.2))

theorem regularizedGaussian_corrector_tendsto
    (μ : ProbabilityMeasure (E×E)) (ξ : ProbabilityMeasure E) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => transportCorrector (transportJoint
      (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) t) ξ) atTop
      (𝓝 (transportCorrector (transportJoint (μ : Measure (E×E)) t) ξ)) := by
  let μn := regularizedProbability μ gaussianPairProbability ε
  have hn (n : ℕ) : MemLp id 2 (μn n : Measure (E×E)) :=
    regularizedProbability_memLp μ gaussianPairProbability ε hμ (gaussianPair_memLp 2 (by norm_num)) n
  have hKn := regularizedGaussian_entropy_finite μ ε hμ hK
  have hw := regularizedProbability_weak μ gaussianPairProbability ε hε
  have hm := regularizedProbability_moment μ gaussianPairProbability ε hμ
    (gaussianPair_memLp 2 (by norm_num)) hε
  have ha (ν : Measure (E×E)) [IsProbabilityMeasure ν] (hν : MemLp id 2 ν)
      (hk : klDiv ν (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) :
      (transportJoint ν t).fst ≪ volume := by
    have hx := (gaussian_conditional_boltzmann_identity ν hν hk t).2.1
    apply (klDiv_ne_top_iff.mp hx).1.trans
    rw [stdGaussian_eq_heatDensity]
    exact withDensity_absolutelyContinuous _ _
  have hc0 := regularizedProbability_cost μ gaussianPairProbability ε hμ
    (gaussianPair_memLp 2 (by norm_num)) hε
  have hc : Tendsto (fun n => (QuadraticTransport.cost
      (transportProbability (μn n : Measure (E×E)) t) (transportProbability (μ : Measure (E×E)) t)).toReal)
      atTop (𝓝 0) := by
    have hh := hc0.const_mul ((1+|t|)^2)
    simp only [mul_zero] at hh
    exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (fun n => transported_cost_le (μn n) μ t (hn n) hμ) hh
  exact transportCorrector_stability
    (fun n => transportProbability (μn n : Measure (E×E)) t) (transportProbability (μ : Measure (E×E)) t) ξ
    (fun n => transportProbability_memLp _ (hn n) t) (transportProbability_memLp _ hμ t) hξ
    (fun n => ha _ (hn n) (hKn n)) (ha _ hμ hK)
    (transportProbability_weak_tendsto μn μ hw t)
    (transportProbability_moment_tendsto μn μ hn hμ hw hm t) hc

end PersistencePays
#print axioms PersistencePays.regularizedGaussian_corrector_tendsto
