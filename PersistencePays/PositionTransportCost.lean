import PersistencePays.QuadraticDistance

/-! Projection to position does not increase the genuine quadratic transport cost. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem position_cost_le (μ ν : ProbabilityMeasure (E × E)) :
    cost (μ.map measurable_fst.aemeasurable) (ν.map measurable_fst.aemeasurable) ≤ cost μ ν := by
  apply le_iInf
  intro π
  apply le_iInf
  intro hπ
  let ρ : ProbabilityMeasure (E × E) := π.map
    (show Measurable (fun z : (E × E) × (E × E) => (z.1.1,z.2.1)) by fun_prop).aemeasurable
  have hρ : ρ ∈ plans (μ.map measurable_fst.aemeasurable) (ν.map measurable_fst.aemeasurable) := by
    constructor
    · apply Subtype.ext
      have he := congrArg (fun p : ProbabilityMeasure (E × E) => (p : Measure (E × E)).map Prod.fst) hπ.1
      simp only [ProbabilityMeasure.toMeasure_map] at he
      rw [Measure.map_map measurable_fst measurable_fst] at he
      change (Measure.map (fun z : (E × E) × (E × E) => (z.1.1,z.2.1)) (π : Measure _)).map Prod.fst = _
      rw [Measure.map_map measurable_fst (by fun_prop)]
      exact he
    · apply Subtype.ext
      have he := congrArg (fun p : ProbabilityMeasure (E × E) => (p : Measure (E × E)).map Prod.fst) hπ.2
      simp only [ProbabilityMeasure.toMeasure_map] at he
      rw [Measure.map_map measurable_fst measurable_snd] at he
      change (Measure.map (fun z : (E × E) × (E × E) => (z.1.1,z.2.1)) (π : Measure _)).map Prod.snd = _
      rw [Measure.map_map measurable_snd (by fun_prop)]
      exact he
  apply (iInf₂_le ρ hρ).trans
  unfold squaredCost
  change (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖^2) ∂(π : Measure _).map
    (fun z : (E × E) × (E × E) => (z.1.1,z.2.1))) ≤ _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (z.1-z.2)) 2

theorem position_wassersteinTwo_tendsto (μn : ℕ → ProbabilityMeasure (E × E))
    (μ : ProbabilityMeasure (E × E))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E × E)))
    (hμ : MemLp id 2 (μ : Measure (E × E)))
    (hc : Tendsto (fun n => (cost (μn n) μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => wassersteinTwo ((μn n).map measurable_fst.aemeasurable)
      (μ.map measurable_fst.aemeasurable)) atTop (𝓝 0) := by
  have hb : ∀ n, (cost ((μn n).map measurable_fst.aemeasurable)
      (μ.map measurable_fst.aemeasurable)).toReal ≤ (cost (μn n) μ).toReal := by
    intro n
    exact ENNReal.toReal_mono
      (cost_finite (μn n) μ (hμn n).integrable_norm_pow' hμ.integrable_norm_pow')
      (position_cost_le (μn n) μ)
  have ht := squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb hc
  simpa only [Function.comp_def, wassersteinTwo, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp ht

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.position_wassersteinTwo_tendsto
