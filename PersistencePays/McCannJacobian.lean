import PersistencePays.DensityJacobian
import PersistencePays.BrenierInverse
import PersistencePays.BrenierMapPotential

/-! The genuine Brenier density Jacobian, derived from convex proximal
regularity and the area formula, for an everywhere-positive source density.
No Jacobian identity or differentiability of the Brenier map is assumed. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem brenierMap_regular_domain (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hμca : volume ≪ (μ : Measure E))
    (hνac : (ν : Measure E) ≪ volume) :
    ∃ s : Set E, MeasurableSet s ∧ volume sᶜ=0 ∧
      InjOn (brenierMap μ ν) s ∧ DifferentiableOn ℝ (brenierMap μ ν) s := by
  obtain ⟨φ,hφ,_,he⟩ := brenierMap_global_convex_gradient μ ν hμ hν hμac hμca
  obtain ⟨s,hs,hs0,_,hds⟩ :=
    convex_gradient_measurable_differentiability_domain (volume : Measure E) φ hφ
  obtain ⟨r,hr,hr0,hri⟩ := brenierMap_injectiveOn_full μ ν hμ hν hμac hνac
  let e : Set E := {x | brenierMap μ ν x=gradient φ x}
  have hem : MeasurableSet e :=
    measurableSet_eq_fun (measurable_brenierMap μ ν) (measurable_gradient φ)
  have hea : ∀ᵐ x ∂(volume : Measure E), x ∈ e := hμca.ae_le he
  let t := (s∩r)∩e
  have ht : t ⊆ s := fun _ hx => hx.1.1
  refine ⟨t,(hs.inter hr).inter hem,?_,hri.mono (fun _ hx => hx.1.2),?_⟩
  · apply mem_ae_iff.mp
    filter_upwards [mem_ae_iff.mpr hs0,mem_ae_iff.mpr (hμca hr0),hea] with x hx hrx hex
    exact ⟨⟨hx,hrx⟩,hex⟩
  · intro x hx
    have hd := (hds x (ht hx)).mono ht
    exact hd.congr (fun y hy => hy.2) hx.2

/-- McCann's density identity for the canonical, actual quadratic transport.
The derivative is relative to a measurable full-Lebesgue-measure set. -/
theorem brenier_density_jacobian (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hμca : volume ≪ (μ : Measure E))
    (hνac : (ν : Measure E) ≪ volume) :
    ∃ s : Set E, MeasurableSet s ∧ volume sᶜ=0 ∧
      InjOn (brenierMap μ ν) s ∧ DifferentiableOn ℝ (brenierMap μ ν) s ∧
      (μ : Measure E).rnDeriv volume =ᵐ[volume] fun x =>
        ENNReal.ofReal |(fderivWithin ℝ (brenierMap μ ν) s x).det| *
          (ν : Measure E).rnDeriv volume (brenierMap μ ν x) := by
  obtain ⟨s,hs,hs0,hinj,hd⟩ := brenierMap_regular_domain μ ν hμ hν hμac hμca hνac
  refine ⟨s,hs,hs0,hinj,hd,?_⟩
  exact density_jacobian_ae volume μ ν hμac hνac (measurable_brenierMap μ ν)
    (brenierMap_spec μ ν hμ hν hμac).2.1 hs hs0 hinj
    (fun x hx => (hd x hx).hasFDerivWithinAt)

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenier_density_jacobian
