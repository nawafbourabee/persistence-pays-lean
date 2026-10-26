import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Differentiation of a compactly indexed mixture. The uniform domination
needed for differentiation is derived from compactness and continuity. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set Filter Metric
open scoped Topology
variable {P Z V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem compact_parameter_integral_continuous (μ : Measure Z) [IsFiniteMeasure μ]
    {F : P → Z → V} (hF : Continuous F.uncurry) :
    Continuous (fun x => ∫ z, F x z ∂μ) := by
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ:=μ) hF isCompact_univ

theorem compact_parameter_integral_hasFDerivAt (μ : Measure Z) [IsFiniteMeasure μ]
    {F : P → Z → V} {F' : P → Z → P →L[ℝ] V}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ x z, HasFDerivAt (fun y => F y z) (F' x z) x) (x : P) :
    HasFDerivAt (fun y => ∫ z, F y z ∂μ) (∫ z, F' x z ∂μ) x := by
  have hK : IsCompact ((closedBall x 1) ×ˢ (univ : Set Z)) :=
    (isCompact_closedBall x 1).prod isCompact_univ
  obtain ⟨B,hB⟩ := (hK.image hF').isBounded.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=ball x 1) (bound:=fun _ => B) (ball_mem_nhds x (by norm_num))
  · filter_upwards with y
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with z
    intro y hy
    exact hB (F' y z) ⟨(y,z),⟨ball_subset_closedBall hy,mem_univ z⟩,rfl⟩
  · exact integrable_const B
  · filter_upwards with z
    intro y _
    exact hd y z

theorem compact_parameter_integral_contDiff_one (μ : Measure Z) [IsFiniteMeasure μ]
    {F : P → Z → V} {F' : P → Z → P →L[ℝ] V}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ x z, HasFDerivAt (fun y => F y z) (F' x z) x) :
    ContDiff ℝ 1 (fun y => ∫ z, F y z ∂μ) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨_, compact_parameter_integral_continuous μ hF',
    compact_parameter_integral_hasFDerivAt μ hF hF' hd⟩

end PersistencePays
#print axioms PersistencePays.compact_parameter_integral_contDiff_one
