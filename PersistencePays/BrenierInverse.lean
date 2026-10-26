import PersistencePays.BrenierMap

/-! Quadratic optimal plans are reversed by exchanging coordinates. When both
marginals have densities, the two actual Brenier maps are a.e. inverses. -/
open MeasureTheory Set Filter
open scoped ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def swapPlan (π : ProbabilityMeasure (E×E)) : ProbabilityMeasure (E×E) :=
  π.map measurable_swap.aemeasurable

lemma swapPlan_mem {μ ν : ProbabilityMeasure E} {π : ProbabilityMeasure (E×E)}
    (hπ : π ∈ plans μ ν) : swapPlan π ∈ plans ν μ := by
  constructor
  · apply Subtype.ext
    change ((π : Measure (E×E)).map Prod.swap).map Prod.fst = (ν : Measure E)
    rw [Measure.map_map measurable_fst measurable_swap]
    exact congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.2
  · apply Subtype.ext
    change ((π : Measure (E×E)).map Prod.swap).map Prod.snd = (μ : Measure E)
    rw [Measure.map_map measurable_snd measurable_swap]
    exact congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1

lemma squaredCost_swap (π : ProbabilityMeasure (E×E)) :
    squaredCost (swapPlan π)=squaredCost π := by
  unfold squaredCost swapPlan
  rw [ProbabilityMeasure.toMeasure_map,lintegral_map (by fun_prop) measurable_swap]
  change (∫⁻ z, ENNReal.ofReal (‖z.2-z.1‖^2) ∂(π : Measure (E×E))) = _
  simp only [norm_sub_rev]

theorem cost_comm (μ ν : ProbabilityMeasure E) : cost μ ν=cost ν μ := by
  have hh (α β : ProbabilityMeasure E) : cost α β ≤ cost β α := by
    apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    have hi : cost α β ≤ squaredCost (swapPlan π) := iInf₂_le _ (swapPlan_mem hπ)
    simpa only [squaredCost_swap] using hi
  exact le_antisymm (hh μ ν) (hh ν μ)

lemma swapPlan_optimal {μ ν : ProbabilityMeasure E} {π : ProbabilityMeasure (E×E)}
    (hπ : IsOptimal μ ν π) : IsOptimal ν μ (swapPlan π) := by
  refine ⟨swapPlan_mem hπ.1,?_⟩
  rw [squaredCost_swap,hπ.2,cost_comm]

theorem optimalPlan_swap (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hνac : (ν : Measure E) ≪ volume) :
    swapPlan (optimalPlan μ ν)=optimalPlan ν μ := by
  apply brenier_unique ν μ _ _ (swapPlan_optimal (optimalPlan_optimal μ ν))
    (optimalPlan_optimal ν μ) _ volume hνac
  rw [squaredCost_swap]
  exact squaredCost_finite μ ν _ (optimalPlan_optimal μ ν).1
    hμ.integrable_norm_pow' hν.integrable_norm_pow'

theorem brenierMap_inverse_ae (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hνac : (ν : Measure E) ≪ volume) :
    ∀ᵐ x ∂(μ : Measure E), brenierMap ν μ (brenierMap μ ν x)=x := by
  have hs := brenierMap_spec μ ν hμ hν hμac
  have hr := brenierMap_spec ν μ hν hμ hνac
  have hinv : ∀ᵐ z ∂(optimalPlan ν μ : Measure (E×E)), z.2=brenierMap ν μ z.1 := by
    rw [hr.2.2]
    apply (ae_map_iff (measurable_id.prodMk hr.1).aemeasurable
      (measurableSet_eq_fun measurable_snd (hr.1.comp measurable_fst))).mpr
    exact Eventually.of_forall (fun _ => rfl)
  rw [← optimalPlan_swap μ ν hμ hν hνac] at hinv
  have hinv' := ae_of_ae_map measurable_swap.aemeasurable hinv
  change ∀ᵐ z ∂(optimalPlan μ ν : Measure (E×E)), z.1=brenierMap ν μ z.2 at hinv'
  rw [hs.2.2] at hinv'
  exact (ae_of_ae_map (measurable_id.prodMk hs.1).aemeasurable hinv').mono (fun _ h => h.symm)

theorem brenierMap_injectiveOn_full (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hνac : (ν : Measure E) ≪ volume) :
    ∃ s : Set E, MeasurableSet s ∧ (μ : Measure E) sᶜ=0 ∧ InjOn (brenierMap μ ν) s := by
  let s := {x | brenierMap ν μ (brenierMap μ ν x)=x}
  refine ⟨s,?_,?_,?_⟩
  · exact measurableSet_eq_fun
      ((measurable_brenierMap ν μ).comp (measurable_brenierMap μ ν)) measurable_id
  · exact ae_iff.mp (brenierMap_inverse_ae μ ν hμ hν hμac hνac)
  · intro x hx y hy hxy
    exact hx.symm.trans ((congrArg (brenierMap ν μ) hxy).trans hy)

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenierMap_inverse_ae
