import PersistencePays.CorrectorStability

/-! Canonical optimal-plan lifts and continuity of the actual corrector. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def correctorGraphLaw (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E) :
    ProbabilityMeasure ((E × E) × E) :=
  μ.map (show Measurable (fun z : E × E => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1)) from
    measurable_id.prodMk ((measurable_positionBrenierMap (μ : Measure (E × E)) ξ).comp measurable_fst)).aemeasurable

theorem correctorGraphLaw_first (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E) :
    (correctorGraphLaw μ ξ).map measurable_fst.aemeasurable=μ := by
  apply Subtype.ext
  change ((μ : Measure (E × E)).map
    (fun z => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1))).map Prod.fst = _
  have hg : Measurable (fun z : E × E =>
      (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1)) :=
    measurable_id.prodMk ((measurable_positionBrenierMap (μ : Measure (E × E)) ξ).comp measurable_fst)
  rw [Measure.map_map measurable_fst hg]
  exact Measure.map_id

theorem correctorGraphLaw_optimal (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : (μ : Measure (E × E)).fst ≪ volume) :
    QuadraticTransport.IsOptimal (μ.map measurable_fst.aemeasurable) ξ
      (positionLiftPlan (correctorGraphLaw μ ξ)) := by
  have hp : MemLp id 2 (μ.map measurable_fst.aemeasurable : Measure E) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hs := QuadraticTransport.brenierMap_spec (μ.map measurable_fst.aemeasurable) ξ hp hξ hac
  have he : positionLiftPlan (correctorGraphLaw μ ξ) =
      QuadraticTransport.optimalPlan (μ.map measurable_fst.aemeasurable) ξ := by
    apply Subtype.ext
    change (positionLiftPlan (correctorGraphLaw μ ξ) : Measure (E × E)) =
      (QuadraticTransport.optimalPlan (μ.map measurable_fst.aemeasurable) ξ : Measure (E × E))
    calc
      _ = (μ : Measure (E × E)).fst.map
          (fun x => (x,positionBrenierMap (μ : Measure (E × E)) ξ x)) := by
        change (((μ : Measure (E × E)).map
          (fun z => (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1))).map
          (fun z => (z.1.1,z.2))) = ((μ : Measure (E × E)).map Prod.fst).map
            (fun x => (x,positionBrenierMap (μ : Measure (E × E)) ξ x))
        have hg : Measurable (fun z : E × E =>
            (z,positionBrenierMap (μ : Measure (E × E)) ξ z.1)) :=
          measurable_id.prodMk ((measurable_positionBrenierMap (μ : Measure (E × E)) ξ).comp measurable_fst)
        have hT : Measurable (fun x : E => (x,positionBrenierMap (μ : Measure (E × E)) ξ x)) :=
          measurable_id.prodMk (measurable_positionBrenierMap (μ : Measure (E × E)) ξ)
        rw [Measure.map_map (by fun_prop) hg, Measure.map_map hT measurable_fst]
        rfl
      _ = _ := hs.2.2.symm
  rw [he]
  exact QuadraticTransport.optimalPlan_optimal _ _

theorem correctorGraphLaw_integral (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E) :
    (∫ z, ⟪z.1.2,z.1.1-z.2⟫ ∂(correctorGraphLaw μ ξ : Measure ((E × E) × E))) =
      transportCorrector (μ : Measure (E × E)) ξ :=
  integral_map (measurable_id.prodMk
    ((measurable_positionBrenierMap (μ : Measure (E × E)) ξ).comp measurable_fst)).aemeasurable (by fun_prop)

theorem transportCorrector_stability
    (μn : ℕ → ProbabilityMeasure (E × E)) (μ : ProbabilityMeasure (E × E)) (ξ : ProbabilityMeasure E)
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E × E)))
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hacn : ∀ n, (μn n : Measure (E × E)).fst ≪ volume) (hac : (μ : Measure (E × E)).fst ≪ volume)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ z, ‖z‖^2 ∂(μn n : Measure (E × E))) atTop
      (𝓝 (∫ z, ‖z‖^2 ∂(μ : Measure (E × E)))))
    (hc : Tendsto (fun n => (QuadraticTransport.cost (μn n) μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => transportCorrector (μn n : Measure (E × E)) ξ) atTop
      (𝓝 (transportCorrector (μ : Measure (E × E)) ξ)) := by
  have hh := corrector_lift_stability μn μ ξ (fun n => correctorGraphLaw (μn n) ξ)
    (fun n => correctorGraphLaw_first (μn n) ξ)
    (fun n => correctorGraphLaw_optimal (μn n) ξ (hμn n) hξ (hacn n))
    hμn hμ hξ hac hw hm hc
  simpa only [correctorGraphLaw_integral] using hh

end PersistencePays
#print axioms PersistencePays.transportCorrector_stability
