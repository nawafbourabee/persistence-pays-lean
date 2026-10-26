import PersistencePays.FiniteAverageMap

/-! Exact marginal preservation under event-dependent finite coordinate rewiring. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory Set
open scoped ENNReal
variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace E]

def rewiredPair (A : Set (ι → E×E)) (e : Equiv.Perm ι) (i : ι) (p : ι → E×E) : E×E :=
  by classical exact if p ∈ A then ((p i).1,(p (e i)).2) else p i

theorem measurable_rewiredPair (A : Set (ι → E×E)) (hA : MeasurableSet A)
    (e : Equiv.Perm ι) (i : ι) : Measurable (rewiredPair A e i) := by
  classical
  exact Measurable.ite hA ((measurable_pi_apply i).fst.prodMk (measurable_pi_apply (e i)).snd)
    (measurable_pi_apply i)

def rewiredMeasure (π : Measure (E×E)) (A : Set (ι → E×E)) (e : Equiv.Perm ι) : Measure (E×E) :=
  averageMap (Measure.pi (fun _ : ι => π)) (rewiredPair A e)

theorem rewiredMeasure_probability (π : Measure (E×E)) [IsProbabilityMeasure π]
    (A : Set (ι → E×E)) (hA : MeasurableSet A) (e : Equiv.Perm ι) :
    IsProbabilityMeasure (rewiredMeasure π A e) :=
  averageMap_probability _ _ (measurable_rewiredPair A hA e)

theorem rewiredMeasure_fst (π : Measure (E×E)) [IsProbabilityMeasure π]
    (A : Set (ι → E×E)) (hA : MeasurableSet A) (e : Equiv.Perm ι) :
    (rewiredMeasure π A e).map Prod.fst = π.map Prod.fst := by
  classical
  rw [rewiredMeasure, averageMap_map _ _ (measurable_rewiredPair A hA e) _ measurable_fst]
  have he : (fun i => Prod.fst ∘ rewiredPair A e i) =
      (fun i => Prod.fst ∘ (Function.eval i : (ι → E×E) → E×E)) := by
    funext i p
    by_cases hp : p ∈ A <;> simp [rewiredPair, hp, Function.comp_def]
  rw [he, ← averageMap_map _ _ (fun i => measurable_pi_apply i) _ measurable_fst,
    averageMap_eq_of_measure_preserving _ π _ (fun i => measurePreserving_eval _ i)]

theorem rewiredMeasure_snd (π : Measure (E×E)) [IsProbabilityMeasure π]
    (A : Set (ι → E×E)) (hA : MeasurableSet A) (e : Equiv.Perm ι) :
    (rewiredMeasure π A e).map Prod.snd = π.map Prod.snd := by
  classical
  rw [rewiredMeasure, averageMap_map _ _ (measurable_rewiredPair A hA e) _ measurable_snd]
  calc
    _ = averageMap (Measure.pi (fun _ : ι => π))
        (fun i => Prod.snd ∘ (Function.eval i : (ι → E×E) → E×E)) := by
      apply averageMap_eq_of_sum _ _ _
        (fun i => measurable_snd.comp (measurable_rewiredPair A hA e i))
        (fun i => (measurable_pi_apply i).snd)
      intro φ p
      by_cases hp : p ∈ A
      · simp only [Function.comp_apply, rewiredPair, hp, if_true]
        exact Equiv.sum_comp e (fun i => φ (p i).2)
      · simp [Function.comp_def, rewiredPair, hp]
    _ = _ := by
      rw [← averageMap_map _ _ (fun i => measurable_pi_apply i) _ measurable_snd,
        averageMap_eq_of_measure_preserving _ π _ (fun i => measurePreserving_eval _ i)]

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.rewiredMeasure_snd
