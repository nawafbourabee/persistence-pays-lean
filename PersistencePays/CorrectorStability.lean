import PersistencePays.CorrectorLiftMoments
import PersistencePays.VaryingCouplingCompactness
import PersistencePays.PositionTransportCost

/-! Corrector stability for arbitrary optimal-plan lifts. The convergence
hypotheses are stated explicitly: weak convergence, quadratic moment convergence,
and convergence of the genuine quadratic transport cost to zero. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem corrector_lift_stability
    (μn : ℕ → ProbabilityMeasure (E × E)) (μ : ProbabilityMeasure (E × E))
    (ξ : ProbabilityMeasure E) (ηn : ℕ → ProbabilityMeasure ((E × E) × E))
    (hfn : ∀ n, (ηn n).map measurable_fst.aemeasurable=μn n)
    (hon : ∀ n, QuadraticTransport.IsOptimal ((μn n).map measurable_fst.aemeasurable)
      ξ (positionLiftPlan (ηn n)))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E × E)))
    (hμ : MemLp id 2 (μ : Measure (E × E))) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : (μ : Measure (E × E)).fst ≪ volume)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ z, ‖z‖^2 ∂(μn n : Measure (E × E))) atTop
      (𝓝 (∫ z, ‖z‖^2 ∂(μ : Measure (E × E)))))
    (hc : Tendsto (fun n => (QuadraticTransport.cost (μn n) μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ⟪z.1.2,z.1.1-z.2⟫ ∂(ηn n : Measure ((E × E) × E))) atTop
      (𝓝 (transportCorrector (μ : Measure (E × E)) ξ)) := by
  have hsn n : (ηn n).map measurable_snd.aemeasurable=ξ := by
    rw [← positionLiftPlan_snd]
    exact (hon n).1.2
  have hp n : MemLp id 2 ((μn n).map measurable_fst.aemeasurable : Measure E) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr (hμn n).fst
  have hp0 : MemLp id 2 (μ.map measurable_fst.aemeasurable : Measure E) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hwp : Tendsto (fun n => (μn n).map measurable_fst.aemeasurable) atTop
      (𝓝 (μ.map measurable_fst.aemeasurable)) :=
    (ProbabilityMeasure.continuous_map continuous_fst).continuousAt.tendsto.comp hw
  have hdp := QuadraticTransport.position_wassersteinTwo_tendsto μn μ hμn hμ hc
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hcompact := QuadraticTransport.varying_couplings_compact_closure
    (fun n => μn (ns n)) (fun _ => ξ) μ ξ (fun n => ηn (ns n))
    (fun n => hfn (ns n)) (fun n => hsn (ns n)) (hw.comp hns) tendsto_const_nhds
  obtain ⟨η,_,ms,hms,hη⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hind : Tendsto (fun n => ns (ms n)) atTop atTop := hns.comp hms.tendsto_atTop
  have hη' : Tendsto (fun n => ηn (ns (ms n))) atTop (𝓝 η) := hη
  have hfirst : η.map measurable_fst.aemeasurable=μ := by
    have hh := (ProbabilityMeasure.continuous_map continuous_fst).continuousAt.tendsto.comp hη'
    have he : ((fun p : ProbabilityMeasure ((E × E) × E) => p.map measurable_fst.aemeasurable) ∘
        (fun n => ηn (ns (ms n)))) = fun n => μn (ns (ms n)) := funext (fun n => hfn _)
    rw [he] at hh
    exact tendsto_nhds_unique hh (hw.comp hind)
  have hsecond : η.map measurable_snd.aemeasurable=ξ := by
    have hh := (ProbabilityMeasure.continuous_map continuous_snd).continuousAt.tendsto.comp hη'
    have he : ((fun p : ProbabilityMeasure ((E × E) × E) => p.map measurable_snd.aemeasurable) ∘
        (fun n => ηn (ns (ms n)))) = fun _ : ℕ => ξ := funext (fun n => hsn _)
    rw [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hxy : Tendsto (fun n => positionLiftPlan (ηn (ns (ms n)))) atTop
      (𝓝 (positionLiftPlan η)) :=
    (ProbabilityMeasure.continuous_map (show Continuous (fun z : (E × E) × E => (z.1.1,z.2)) by fun_prop)).continuousAt.tendsto.comp hη'
  have hopt := QuadraticTransport.optimalPlan_limit
    (fun n => (μn (ns (ms n))).map measurable_fst.aemeasurable)
    (μ.map measurable_fst.aemeasurable) ξ
    (fun n => positionLiftPlan (ηn (ns (ms n)))) (positionLiftPlan η)
    (fun n => hon _) (fun n => hp _) hp0 hξ (hwp.comp hind) (hdp.comp hind) hxy
  have hi := lifted_corrector_weak_integral_tendsto
    (fun n => μn (ns (ms n))) μ ξ (fun n => ηn (ns (ms n))) η
    (fun n => hfn _) (fun n => hsn _) hfirst hsecond (fun n => hμn _) hμ hξ hη' (hm.comp hind)
  rw [corrector_lift_integral μ ξ η hfirst hopt hμ hξ hac] at hi
  exact ⟨ms,hi⟩

end PersistencePays
#print axioms PersistencePays.corrector_lift_stability
