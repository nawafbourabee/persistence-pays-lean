import PersistencePays.ConvexSecondRegularity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The density Jacobian identity from the area formula, on a measurable
full-measure differentiability and injectivity domain. All measures and
Radon--Nikodym derivatives are the actual mathlib objects. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem source_eq_jacobian_density
    (ρ μ ν : Measure E) [IsAddHaarMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ)
    {T : E → E} (hT : Measurable T) (hmap : μ.map T=ν)
    {s : Set E} (hs : MeasurableSet s) (hs0 : ρ sᶜ=0) (hinj : InjOn T s)
    {A : E → E →L[ℝ] E} (hd : ∀ x ∈ s, HasFDerivWithinAt T (A x) s x) :
    μ = ρ.withDensity (fun x => ENNReal.ofReal |(A x).det| * ν.rnDeriv ρ (T x)) := by
  have haeρ : ∀ᵐ x ∂ρ, x ∈ s := mem_ae_iff.mpr hs0
  have haeμ : ∀ᵐ x ∂μ, x ∈ s := hμ.ae_le haeρ
  apply Measure.ext
  intro a ha
  have has := ha.inter hs
  have hdas : ∀ x ∈ a∩s, HasFDerivWithinAt T (A x) (a∩s) x :=
    fun x hx => (hd x hx.2).mono inter_subset_right
  have him : MeasurableSet (T '' (a∩s)) :=
    measurable_image_of_fderivWithin has hdas (hinj.mono inter_subset_right)
  have he : T ⁻¹' (T '' (a∩s)) =ᵐ[μ] a := by
    filter_upwards [haeμ] with x hx
    apply propext
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact (hinj hy.2 hx hxy) ▸ hy.1
    · intro hxa
      exact ⟨x,⟨hxa,hx⟩,rfl⟩
  have heρ : (a∩s : Set E) =ᵐ[ρ] a := by
    filter_upwards [haeρ] with x hx
    exact propext ⟨fun h => h.1,fun h => ⟨h,hx⟩⟩
  calc
    μ a = μ (T ⁻¹' (T '' (a∩s))) := (measure_congr he).symm
    _ = ν (T '' (a∩s)) := by rw [← hmap,Measure.map_apply hT him]
    _ = ∫⁻ y in T '' (a∩s), ν.rnDeriv ρ y ∂ρ := by
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν ρ hν]
      exact withDensity_apply _ him
    _ = ∫⁻ x in a∩s, ENNReal.ofReal |(A x).det| * ν.rnDeriv ρ (T x) ∂ρ :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul ρ has hdas
        (hinj.mono inter_subset_right) _
    _ = ∫⁻ x in a, ENNReal.ofReal |(A x).det| * ν.rnDeriv ρ (T x) ∂ρ :=
      setLIntegral_congr heρ
    _ = (ρ.withDensity (fun x => ENNReal.ofReal |(A x).det| * ν.rnDeriv ρ (T x))) a :=
      (withDensity_apply _ ha).symm

theorem density_jacobian_ae
    (ρ μ ν : Measure E) [IsAddHaarMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ)
    {T : E → E} (hT : Measurable T) (hmap : μ.map T=ν)
    {s : Set E} (hs : MeasurableSet s) (hs0 : ρ sᶜ=0) (hinj : InjOn T s)
    {A : E → E →L[ℝ] E} (hd : ∀ x ∈ s, HasFDerivWithinAt T (A x) s x) :
    μ.rnDeriv ρ =ᵐ[ρ] fun x => ENNReal.ofReal |(A x).det| * ν.rnDeriv ρ (T x) := by
  have he := source_eq_jacobian_density ρ μ ν hμ hν hT hmap hs hs0 hinj hd
  have hm : AEMeasurable (fun x => ENNReal.ofReal |(A x).det|) ρ := by
    have hh := aemeasurable_ofReal_abs_det_fderivWithin ρ hs hd
    rwa [Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hs0)] at hh
  conv_lhs => rw [he]
  exact Measure.rnDeriv_withDensity₀ ρ
    (hm.mul ((Measure.measurable_rnDeriv ν ρ).comp hT).aemeasurable)

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.density_jacobian_ae
