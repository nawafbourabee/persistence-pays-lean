import PersistencePays.MonotoneDivergence

/-! Compact weighted divergence for the actual gradient of a finite convex
function, or any representative equal to it almost everywhere. -/
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace NNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem convex_gradient_locallyIntegrable {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ) :
    LocallyIntegrable (gradient φ) volume := by
  intro x
  obtain ⟨C,hC⟩ := convex_gradient_locally_bounded hφ x
  obtain ⟨u,hu,huo,hxu⟩ := mem_nhds_iff.mp hC
  obtain ⟨K,hK,hxK,hKu⟩ := exists_compact_subset huo hxu
  refine ⟨K,mem_interior_iff_mem_nhds.mp hxK,?_⟩
  have hi : IntegrableOn (fun _ : E => (C:ℝ)) K volume :=
    integrableOn_const hK.measure_ne_top
  apply hi.mono' (measurable_gradient φ).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
  exact hu (hKu hy)

theorem compact_convex_divergence
    {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {T : E → E} (he : T =ᵐ[volume] gradient φ)
    {G : E → E →L[ℝ] E} {s : Set E}
    (hs : volume sᶜ=0) (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,∀ v:E,0≤⟪v,G x v⟫)
    {w : E → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x,0≤w x) :
    Integrable (fun x => w x*(G x).toLinearMap.trace ℝ E) volume ∧
    (∫ x,w x*(G x).toLinearMap.trace ℝ E) ≤ -∫ x,(fderiv ℝ w x) (T x) := by
  let r : Set E := {x | x∈s ∧ DifferentiableAt ℝ φ x ∧ T x=gradient φ x}
  have hr : volume rᶜ=0 := by
    apply mem_ae_iff.mp
    filter_upwards [mem_ae_iff.mpr hs,convexOn_ae_differentiable volume hφ,he]
      with x hx hdx hex
    exact ⟨hx,(hdx (mem_univ x)).2,hex⟩
  have hmono : ∀ x∈r,∀ y∈r,0≤⟪T y-T x,y-x⟫ := by
    intro x hx y hy
    rw [hx.2.2,hy.2.2]
    exact supports_monotone (convex_gradient_supports hφ hy.2.1)
      (convex_gradient_supports hφ hx.2.1)
  exact compact_monotone_divergence
    ((convex_gradient_locallyIntegrable hφ).congr he.symm) hr hmono hG
    (hd.mono (fun x hx => hx.mono (fun y hy => hy.1))) hpos hw hwc hw0

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.compact_convex_divergence
