import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi

/-! Support of a finite product measure. -/
open MeasureTheory Set
open scoped Topology
namespace PersistencePays
noncomputable section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, MetricSpace (E i)] [∀ i, MeasurableSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]

theorem mem_support_pi (x : ∀ i, E i) (hx : ∀ i, x i ∈ (μ i).support) :
    x ∈ (Measure.pi μ).support := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Measure.pi_ball μ x hε]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt ((Measure.mem_support_iff_forall _).mp (hx i)
    _ (Metric.ball_mem_nhds _ hε))

end
end PersistencePays
#print axioms PersistencePays.mem_support_pi
