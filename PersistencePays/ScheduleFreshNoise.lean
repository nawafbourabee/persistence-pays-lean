import PersistencePays.FiniteNoiseSchedule

/-! A state after an arbitrary deterministic schedule and its next independent draw. -/
noncomputable section
namespace PersistencePays.FiniteNoise
open MeasureTheory ProbabilityTheory
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

def scheduleBeforeLastStep (f : ℕ → S×B → S) (n : ℕ) (s : S) (b : Fin (n+1) → B) : S×B :=
  (scheduleTrajectory f n s (fun i => b i.castSucc), b (Fin.last n))

theorem measurable_scheduleBeforeLastStep (f : ℕ → S×B → S) (hf : ∀ j, Measurable (f j))
    (n : ℕ) (s : S) : Measurable (scheduleBeforeLastStep f n s) :=
  ((measurable_scheduleTrajectory_fixed f hf n s).comp
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc)).prodMk
      (measurable_pi_apply (Fin.last n))

theorem schedule_fresh_noise_law (μ : Measure B) [IsProbabilityMeasure μ]
    (f : ℕ → S×B → S) (hf : ∀ j, Measurable (f j)) (n : ℕ) (s : S) :
    (Measure.pi (fun _ : Fin (n+1) => μ)).map (scheduleBeforeLastStep f n s) =
      (scheduleKernel (fun j => noiseKernel μ (f j) (hf j)) n s).prod μ := by
  rw [← (snoc_preserving μ n).map_eq,
    Measure.map_map (measurable_scheduleBeforeLastStep f hf n s) (snoc_preserving μ n).measurable]
  have he : scheduleBeforeLastStep f n s ∘ (fun p : (Fin n → B)×B => Fin.snoc p.1 p.2) =
      Prod.map (scheduleTrajectory f n s) id := by
    funext p
    simp [scheduleBeforeLastStep, Function.comp_def, Prod.map]
  rw [he, ← Measure.map_prod_map _ _ (measurable_scheduleTrajectory_fixed f hf n s) measurable_id,
    Measure.map_id, scheduleTrajectory_law μ f hf n s]

end PersistencePays.FiniteNoise
#print axioms PersistencePays.FiniteNoise.schedule_fresh_noise_law
