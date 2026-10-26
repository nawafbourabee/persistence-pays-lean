import PersistencePays.Corrector
import PersistencePays.TransportStability
import PersistencePays.WeakMomentConvergence

/-! Optimal-plan lifts identify the actual corrector at every weak limit. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def positionLiftPlan (η : ProbabilityMeasure ((E × E) × E)) : ProbabilityMeasure (E × E) :=
  η.map (show Measurable (fun z : (E × E) × E => (z.1.1,z.2)) by fun_prop).aemeasurable

theorem positionLiftPlan_snd (η : ProbabilityMeasure ((E × E) × E)) :
    (positionLiftPlan η).map measurable_snd.aemeasurable = η.map measurable_snd.aemeasurable := by
  apply Subtype.ext
  change ((η : Measure ((E × E) × E)).map (fun z => (z.1.1,z.2))).map Prod.snd = _
  rw [Measure.map_map measurable_snd (by fun_prop)]
  rfl

theorem corrector_lift_graph (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E)
    (η : ProbabilityMeasure ((E × E) × E))
    (hfst : η.map measurable_fst.aemeasurable = μ)
    (hopt : QuadraticTransport.IsOptimal (μ.map measurable_fst.aemeasurable) ξ (positionLiftPlan η))
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : (μ : Measure (E × E)).fst ≪ volume) :
    (η : Measure ((E × E) × E)) = (μ : Measure (E × E)).map
      (fun z => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1)) := by
  have hp : MemLp id 2 (μ : Measure (E × E)).fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hT := measurable_positionBrenierMap (μ : Measure (E × E)) ξ
  have hs := QuadraticTransport.brenierMap_spec (μ.map measurable_fst.aemeasurable) ξ hp hξ hac
  have he := QuadraticTransport.brenier_unique _ _ (positionLiftPlan η)
    (QuadraticTransport.optimalPlan (μ.map measurable_fst.aemeasurable) ξ) hopt
    (QuadraticTransport.optimalPlan_optimal _ _)
    (QuadraticTransport.squaredCost_finite _ _ _ hopt.1 hp.integrable_norm_pow' hξ.integrable_norm_pow')
    volume hac
  have hgraph : ∀ᵐ z ∂(positionLiftPlan η : Measure (E × E)),
      z.2=positionBrenierMap (μ : Measure (E × E)) ξ z.1 := by
    rw [he,hs.2.2]
    apply (ae_map_iff (measurable_id.prodMk hT).aemeasurable
      (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst))).mpr
    exact Eventually.of_forall (fun _ => rfl)
  have hg := ae_of_ae_map (show Measurable (fun z : (E × E) × E => (z.1.1,z.2)) by fun_prop).aemeasurable hgraph
  have hfirst : (η : Measure ((E × E) × E)).fst = (μ : Measure (E × E)) :=
    congrArg (fun p : ProbabilityMeasure (E × E) => (p : Measure (E × E))) hfst
  calc
    (η : Measure ((E × E) × E)) = (η : Measure ((E × E) × E)).fst.map
        (fun z => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1)) := by
      rw [Measure.fst,Measure.map_map
        (show Measurable (fun z : E × E => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1)) from
          measurable_id.prodMk (hT.comp measurable_fst)) measurable_fst]
      change (η : Measure ((E × E) × E)) = (η : Measure ((E × E) × E)).map
        (fun z => (z.1,positionBrenierMap (μ : Measure (E × E)) ξ z.1.1))
      have heq : (fun z : (E × E) × E => (z.1,positionBrenierMap (μ : Measure (E × E)) ξ z.1.1)) =ᵐ[(η : Measure ((E × E) × E))] id := by
        filter_upwards [hg] with z hz
        exact Prod.ext rfl hz.symm
      rw [Measure.map_congr heq,Measure.map_id]
    _ = _ := congrArg (Measure.map (fun z => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1))) hfirst

theorem corrector_lift_integral (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E)
    (η : ProbabilityMeasure ((E × E) × E))
    (hfst : η.map measurable_fst.aemeasurable = μ)
    (hopt : QuadraticTransport.IsOptimal (μ.map measurable_fst.aemeasurable) ξ (positionLiftPlan η))
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : (μ : Measure (E × E)).fst ≪ volume) :
    (∫ z, ⟪z.1.2,z.1.1-z.2⟫ ∂(η : Measure ((E × E) × E))) =
      transportCorrector (μ : Measure (E × E)) ξ := by
  rw [corrector_lift_graph μ ξ η hfst hopt hμ hξ hac]
  exact integral_map (measurable_id.prodMk
    ((measurable_positionBrenierMap (μ : Measure (E × E)) ξ).comp measurable_fst)).aemeasurable (by fun_prop)

theorem lifted_corrector_growth (z : (E × E) × E) :
    ‖⟪z.1.2,z.1.1-z.2⟫‖ ≤ 2*(‖z.1‖^2+‖z.2‖^2) := by
  have hi := norm_inner_le_norm (𝕜 := ℝ) z.1.2 (z.1.1-z.2)
  have hx := norm_fst_le z.1
  have hv := norm_snd_le z.1
  have hn := norm_sub_le z.1.1 z.2
  have hmul := mul_le_mul_of_nonneg_left hn (norm_nonneg z.1.2)
  have hp := mul_le_mul hx hv (norm_nonneg z.1.2) (norm_nonneg z.1)
  have hc := mul_le_mul_of_nonneg_right hv (norm_nonneg z.2)
  nlinarith [sq_nonneg (‖z.1‖-‖z.2‖),sq_nonneg ‖z.1‖,sq_nonneg ‖z.2‖]

end PersistencePays
#print axioms PersistencePays.corrector_lift_integral
