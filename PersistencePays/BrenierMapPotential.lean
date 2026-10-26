import PersistencePays.BrenierMap
import PersistencePays.FullPotential

/-! The chosen law-dependent Brenier map is the actual convex gradient a.e. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory Set Filter
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem brenierMap_gradient_ae (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hac : (μ : Measure E) ≪ volume) :
    ∃ a ∈ (optimalPlan μ ν : Measure (E × E)).support,
      let φ := rockafellarPotential (optimalPlan μ ν : Measure (E × E)).support a
      ConvexOn ℝ (potentialDomain (optimalPlan μ ν : Measure (E × E)).support a) φ ∧
      brenierMap μ ν =ᵐ[(μ : Measure E)] gradient φ := by
  have hp := optimalPlan_optimal μ ν
  have hf := squaredCost_finite μ ν (optimalPlan μ ν) hp.1
    hμ.integrable_norm_pow' hν.integrable_norm_pow'
  obtain ⟨a,ha,hconv,hm,_,hgraph⟩ := brenier_gradient μ ν (optimalPlan μ ν) hp hf volume hac
  have hs := brenierMap_spec μ ν hμ hν hac
  refine ⟨a,ha,hconv,?_⟩
  let φ := rockafellarPotential (optimalPlan μ ν : Measure (E × E)).support a
  have he : ∀ᵐ z ∂(optimalPlan μ ν : Measure (E × E)), z.2=gradient φ z.1 := by
    rw [hgraph]
    apply (ae_map_iff (measurable_id.prodMk hm).aemeasurable
      (measurableSet_eq_fun measurable_snd (hm.comp measurable_fst))).mpr
    exact Eventually.of_forall (fun _ => rfl)
  rw [hs.2.2] at he
  exact ae_of_ae_map (measurable_id.prodMk hs.1).aemeasurable he

theorem brenierMap_global_convex_gradient (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hac : (μ : Measure E) ≪ volume) (hca : volume ≪ (μ : Measure E)) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ LocallyLipschitz φ ∧
      brenierMap μ ν =ᵐ[(μ : Measure E)] gradient φ := by
  obtain ⟨a,ha,_,he⟩ := brenierMap_gradient_ae μ ν hμ hν hac
  have hp := optimalPlan_optimal μ ν
  have hf := squaredCost_finite μ ν (optimalPlan μ ν) hp.1
    hμ.integrable_norm_pow' hν.integrable_norm_pow'
  have hfst : (optimalPlan μ ν : Measure (E × E)).fst = (μ : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hp.1.1
  have hc := rockafellar_globally_convex (optimalPlan μ ν : Measure (E × E))
    (volume : Measure E) (by rwa [hfst]) (by rwa [hfst])
    (optimal_support_cyclicallyMonotone μ ν (optimalPlan μ ν) hp hf) Measure.support_mem_ae ha
  exact ⟨_,hc.1,hc.2,he⟩

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenierMap_global_convex_gradient
