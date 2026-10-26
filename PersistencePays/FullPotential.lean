import PersistencePays.Brenier
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The Brenier potential is globally finite when the source is equivalent
to Lebesgue (or any additive Haar) measure. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem potentialDomain_eq_univ (π : Measure (E×E)) [IsProbabilityMeasure π]
    (ρ : Measure E) [IsAddHaarMeasure ρ]
    (hac : π.fst ≪ ρ) (hca : ρ ≪ π.fst)
    {Γ : Set (E×E)} (hΓ : CyclicallyMonotone Γ)
    (hcarry : ∀ᵐ z ∂π, z ∈ Γ) {a : E×E} (ha : a ∈ Γ) :
    potentialDomain Γ a = univ := by
  let D := potentialDomain Γ a
  have hcv : Convex ℝ D := potentialDomain_convex Γ a
  have hD : ∀ᵐ z ∂π, z.1 ∈ D := hcarry.mono (fun z hz => relation_in_potentialDomain hΓ ha hz)
  have hcl : ∀ᵐ x ∂π.fst, x ∈ closure D := by
    apply (ae_map_iff measurable_fst.aemeasurable isClosed_closure.measurableSet).mpr
    exact hD.mono (fun _ hz => subset_closure hz)
  have hdense : Dense (closure D) := Measure.dense_of_ae (hca.ae_le hcl)
  have hclall : closure D = univ := by simpa only [closure_closure] using hdense.closure_eq
  have hb : ∀ᵐ x ∂ρ, x ∉ frontier D := by
    exact ae_iff.mpr (by simpa using hcv.addHaar_frontier ρ)
  have hbp := ae_of_ae_map measurable_fst.aemeasurable (hac.ae_le hb)
  have hi : ∀ᵐ z ∂π, z.1 ∈ interior D := by
    filter_upwards [hD,hbp] with z hz hzb
    by_contra hn
    exact hzb ⟨subset_closure hz,hn⟩
  obtain ⟨z,hz⟩ := hi.exists
  have hint : interior D = univ := by
    rw [← hcv.interior_closure_eq_interior_of_nonempty_interior ⟨z.1,hz⟩, hclall,
      interior_univ]
  exact eq_univ_of_univ_subset (by rw [← hint]; exact interior_subset)

theorem rockafellar_globally_convex (π : Measure (E×E)) [IsProbabilityMeasure π]
    (ρ : Measure E) [IsAddHaarMeasure ρ]
    (hac : π.fst ≪ ρ) (hca : ρ ≪ π.fst)
    {Γ : Set (E×E)} (hΓ : CyclicallyMonotone Γ)
    (hcarry : ∀ᵐ z ∂π, z ∈ Γ) {a : E×E} (ha : a ∈ Γ) :
    ConvexOn ℝ univ (rockafellarPotential Γ a) ∧
      LocallyLipschitz (rockafellarPotential Γ a) := by
  have hh := rockafellarPotential_convex Γ a
  rw [potentialDomain_eq_univ π ρ hac hca hΓ hcarry ha] at hh
  exact ⟨hh, hh.locallyLipschitz⟩

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.rockafellar_globally_convex
