import PersistencePays.ConvexHessian
import PersistencePays.McCannEntropy

/-! A measurable, positive-definite Hessian field for the actual Brenier map,
with its genuine density Jacobian. This packages the rough convex regularity
needed by the conditional Gaussian matrix inequality. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem brenier_measurable_positive_jacobian (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hμca : volume ≪ (μ : Measure E))
    (hνac : (ν : Measure E) ≪ volume) :
    ∃ (s : Set E) (G : E → E →L[ℝ] E),
      MeasurableSet s ∧ volume sᶜ=0 ∧ Measurable G ∧ InjOn (brenierMap μ ν) s ∧
      (∀ᵐ x ∂(μ : Measure E),
        HasFDerivWithinAt (brenierMap μ ν) (G x) s x ∧
        (G x).toLinearMap.IsSymmetric ∧ ∀ v : E, v≠0 → 0<⟪v,G x v⟫) ∧
      (μ : Measure E).rnDeriv volume =ᵐ[volume] fun x =>
        ENNReal.ofReal |(G x).det| * (ν : Measure E).rnDeriv volume (brenierMap μ ν x) := by
  obtain ⟨φ,hφ,_,he⟩ := brenierMap_global_convex_gradient μ ν hμ hν hμac hμca
  obtain ⟨s,hs,hs0,hsD,hds⟩ :=
    convex_gradient_measurable_differentiability_domain (volume : Measure E) φ hφ
  obtain ⟨r,hr,hr0,hri⟩ := brenierMap_injectiveOn_full μ ν hμ hν hμac hνac
  let e : Set E := {x | brenierMap μ ν x=gradient φ x}
  have hem : MeasurableSet e :=
    measurableSet_eq_fun (measurable_brenierMap μ ν) (measurable_gradient φ)
  have hea : ∀ᵐ x ∂(volume : Measure E), x ∈ e := hμca.ae_le he
  let t := (s∩r)∩e
  have ht : t ⊆ s := fun _ hx => hx.1.1
  have htm : MeasurableSet t := (hs.inter hr).inter hem
  have ht0 : volume tᶜ=0 := by
    apply mem_ae_iff.mp
    filter_upwards [mem_ae_iff.mpr hs0,mem_ae_iff.mpr (hμca hr0),hea] with x hx hrx hex
    exact ⟨⟨hx,hrx⟩,hex⟩
  have hti : InjOn (brenierMap μ ν) t := hri.mono (fun _ hx => hx.1.2)
  have htd : DifferentiableOn ℝ (brenierMap μ ν) t := by
    intro x hx
    exact ((hds x (ht hx)).mono ht).congr (fun y hy => hy.2) hx.2
  let A := fderivWithin ℝ (brenierMap μ ν) t
  have hm : AEMeasurable A (volume : Measure E) := by
    have hh := aemeasurable_fderivWithin (volume : Measure E) htm
      (fun x hx => (htd x hx).hasFDerivWithinAt)
    have hr : (volume : Measure E).restrict t=volume :=
      Measure.restrict_eq_self_of_ae_mem (s:=t) (mem_ae_iff.mpr ht0)
    rw [hr] at hh
    exact hh
  let G := hm.mk A
  have hGeq : A =ᵐ[volume] G := hm.ae_eq_mk
  have hpos := convex_representative_fderiv_positive (volume : Measure E) φ hφ ht0
    (fun x hx => hsD x (ht hx)) (fun x hx => hx.2)
  have hmap := (brenierMap_spec μ ν hμ hν hμac).2.1
  have hJ := density_jacobian_ae volume μ ν hμac hνac (measurable_brenierMap μ ν)
    hmap htm ht0 hti (fun x hx => (htd x hx).hasFDerivWithinAt)
  have hdet := (log_jacobian_of_density_identity μ ν hμac hνac
    (measurable_brenierMap μ ν) hmap hJ).mono (fun _ h => h.1)
  refine ⟨t,G,htm,ht0,hm.measurable_mk,hti,?_,?_⟩
  · filter_upwards [hμac.ae_le hGeq,hμac.ae_le hpos,hdet,
      hμac.ae_le (mem_ae_iff.mpr ht0)] with x hx hp hdx hxt
    have hd : HasFDerivWithinAt (brenierMap μ ν) (A x) t x :=
      (htd x hxt).hasFDerivWithinAt
    rw [← hx]
    exact ⟨hd,hp.isSymmetric,fun v hv => positive_inner_pos_of_det_ne_zero (A x) hp hdx hv⟩
  · filter_upwards [hJ,hGeq] with x hx hgx
    change (μ : Measure E).rnDeriv volume x =
      ENNReal.ofReal |(G x).det| * (ν : Measure E).rnDeriv volume (brenierMap μ ν x)
    simpa only [← hgx] using hx

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenier_measurable_positive_jacobian
