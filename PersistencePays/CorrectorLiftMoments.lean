import PersistencePays.CorrectorLift

/-! The quadratic growth of the lifted corrector is controlled by its two actual marginals. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def liftedQuadraticMoment (z : (E × E) × E) : ℝ := 2*(‖z.1‖^2+‖z.2‖^2)

theorem liftedQuadraticMoment_integral (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E)
    (η : ProbabilityMeasure ((E × E) × E))
    (hf : η.map measurable_fst.aemeasurable=μ) (hs : η.map measurable_snd.aemeasurable=ξ)
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E)) :
    Integrable liftedQuadraticMoment (η : Measure ((E × E) × E)) ∧
    (∫ z, liftedQuadraticMoment z ∂(η : Measure ((E × E) × E))) =
      2*((∫ z, ‖z‖^2 ∂(μ : Measure (E × E)))+(∫ y, ‖y‖^2 ∂(ξ : Measure E))) := by
  have hfm : (η : Measure ((E × E) × E)).map Prod.fst=(μ : Measure (E × E)) :=
    congrArg (fun p : ProbabilityMeasure (E × E) => (p : Measure (E × E))) hf
  have hsm : (η : Measure ((E × E) × E)).map Prod.snd=(ξ : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hs
  have hp : MemLp (Prod.fst : (E × E) × E → E × E) 2 (η : Measure ((E × E) × E)) := by
    rw [← hfm] at hμ
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mp hμ
  have hq : MemLp (Prod.snd : (E × E) × E → E) 2 (η : Measure ((E × E) × E)) := by
    rw [← hsm] at hξ
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_snd.aemeasurable).mp hξ
  have hi : Integrable (fun z : (E × E) × E => ‖z.1‖^2+‖z.2‖^2) (η : Measure ((E × E) × E)) :=
    hp.integrable_norm_pow'.add hq.integrable_norm_pow'
  refine ⟨hi.const_mul 2,?_⟩
  unfold liftedQuadraticMoment
  rw [integral_const_mul,integral_add hp.integrable_norm_pow' hq.integrable_norm_pow']
  have hfi : (∫ z, ‖z.1‖^2 ∂(η : Measure ((E × E) × E))) = ∫ z, ‖z‖^2 ∂(μ : Measure (E × E)) := by
    rw [← hfm]
    exact (integral_map (μ := (η : Measure ((E × E) × E)))
      (f := fun z : E × E => ‖z‖^2) measurable_fst.aemeasurable (by fun_prop)).symm
  have hsi : (∫ z, ‖z.2‖^2 ∂(η : Measure ((E × E) × E))) = ∫ z, ‖z‖^2 ∂(ξ : Measure E) := by
    rw [← hsm]
    exact (integral_map (μ := (η : Measure ((E × E) × E)))
      (f := fun z : E => ‖z‖^2) measurable_snd.aemeasurable (by fun_prop)).symm
  rw [hfi,hsi]

theorem lifted_corrector_weak_integral_tendsto
    (μn : ℕ → ProbabilityMeasure (E × E)) (μ : ProbabilityMeasure (E × E))
    (ξ : ProbabilityMeasure E) (ηn : ℕ → ProbabilityMeasure ((E × E) × E))
    (η : ProbabilityMeasure ((E × E) × E))
    (hfn : ∀ n, (ηn n).map measurable_fst.aemeasurable=μn n)
    (hsn : ∀ n, (ηn n).map measurable_snd.aemeasurable=ξ)
    (hf : η.map measurable_fst.aemeasurable=μ) (hs : η.map measurable_snd.aemeasurable=ξ)
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E × E)))
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hη : Tendsto ηn atTop (𝓝 η))
    (hm : Tendsto (fun n => ∫ z, ‖z‖^2 ∂(μn n : Measure (E × E))) atTop
      (𝓝 (∫ z, ‖z‖^2 ∂(μ : Measure (E × E))))) :
    Tendsto (fun n => ∫ z, ⟪z.1.2,z.1.1-z.2⟫ ∂(ηn n : Measure ((E × E) × E))) atTop
      (𝓝 (∫ z, ⟪z.1.2,z.1.1-z.2⟫ ∂(η : Measure ((E × E) × E)))) := by
  have hn n := liftedQuadraticMoment_integral (μn n) ξ (ηn n) (hfn n) (hsn n) (hμn n) hξ
  have hlim := liftedQuadraticMoment_integral μ ξ η hf hs hμ hξ
  apply weak_integral_tendsto_of_continuous_dominator hη (by fun_prop)
    (show Continuous (liftedQuadraticMoment : (E × E) × E → ℝ) by unfold liftedQuadraticMoment; fun_prop)
    lifted_corrector_growth (fun n => (hn n).1) hlim.1
  simp_rw [(hn _).2,hlim.2]
  exact tendsto_const_nhds.mul (hm.add tendsto_const_nhds)

end PersistencePays
#print axioms PersistencePays.lifted_corrector_weak_integral_tendsto
