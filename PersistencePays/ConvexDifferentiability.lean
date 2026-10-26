import PersistencePays.Rockafellar
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.Compactness.Lindelof

/-! First-order regularity of the constructed convex transport potential. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology RealInnerProductSpace NNReal
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- Rademacher's theorem localized to an open set. -/
theorem locallyLipschitzOn_ae_differentiable {s : Set E} {f : E → ℝ}
    (hs : IsOpen s) (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x := by
  have hlocal : ∀ x : s, ∃ K : ℝ≥0, ∃ t : Set E,
      IsOpen t ∧ (x : E) ∈ t ∧ LipschitzOnWith K f t := by
    intro x
    obtain ⟨K, t, ht, hft⟩ := hf x.2
    rw [hs.nhdsWithin_eq x.2] at ht
    exact ⟨K, interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht,
      hft.mono interior_subset⟩
  choose K t hto hxt hlt using hlocal
  obtain ⟨r, hr, hcov⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    t hto (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩, hxt ⟨x,hx⟩⟩)
  have had : ∀ i ∈ r, ∀ᵐ x ∂μ, x ∈ t i → DifferentiableWithinAt ℝ f (t i) x :=
    fun i _ => (hlt i).ae_differentiableWithinAt_of_mem
  filter_upwards [(ae_ball_iff hr).mpr had] with x hx hxs
  obtain ⟨i, hir, hxi⟩ := mem_iUnion₂.mp (hcov hxs)
  exact (hx i hir hxi).differentiableAt ((hto i).mem_nhds hxi)

/-- A convex function is differentiable a.e. in its effective domain;
its potentially problematic boundary is Haar-null. -/
theorem convexOn_ae_differentiable {s : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ, x ∈ s → x ∈ interior s ∧ DifferentiableAt ℝ f x := by
  have hd := locallyLipschitzOn_ae_differentiable μ isOpen_interior
    hf.locallyLipschitzOn_interior
  have hb : ∀ᵐ x ∂μ, x ∉ frontier s := by
    exact ae_iff.mpr (by simpa using hf.1.addHaar_frontier μ)
  filter_upwards [hd, hb] with x hx hxb hxs
  have hxi : x ∈ interior s := by
    by_contra hn
    exact hxb ⟨subset_closure hxs, hn⟩
  exact ⟨hxi, hx hxi⟩

variable {μ}

/-- At an interior differentiability point a supporting linear functional
is exactly the derivative. -/
theorem supporting_vector_eq_gradient {s : Set E} {f : E → ℝ} {x v : E}
    (hx : x ∈ interior s) (hf : DifferentiableAt ℝ f x)
    (hv : ∀ z ∈ s, f x + ⟪v, z-x⟫ ≤ f z) :
    v = gradient f x := by
  let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E v
  have hmin : IsLocalMin (fun z => f z - l z) x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with z hz
    have hh := hv z hz
    change f x - ⟪v, x⟫ ≤ f z - ⟪v, z⟫
    rw [inner_sub_right] at hh
    linarith
  have hder : fderiv ℝ f x - l = 0 := by
    have hh := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hf l.differentiableAt, l.fderiv] at hh
    exact hh
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  exact (sub_eq_zero.mp hder).symm

/-- The Rockafellar relation is a graph above a.e. point of its convex domain. -/
theorem rockafellar_ae_graph {Γ : Set (E × E)} (hΓ : CyclicallyMonotone Γ)
    {a : E × E} (ha : a ∈ Γ) :
    ∀ᵐ x ∂μ, ∀ v, (x,v) ∈ Γ → v = gradient (rockafellarPotential Γ a) x := by
  filter_upwards [convexOn_ae_differentiable μ (rockafellarPotential_convex Γ a)] with x hx v hv
  have hxd := relation_in_potentialDomain hΓ ha hv
  obtain ⟨hxi, hd⟩ := hx hxd
  apply supporting_vector_eq_gradient hxi hd
  intro z hz
  exact rockafellar_subgradient hΓ ha hv hz

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.rockafellar_ae_graph
