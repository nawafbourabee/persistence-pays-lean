import PersistencePays.FiniteNoise
import PersistencePays.KernelEntropy

/-! Finite independent noise realizes arbitrary time-inhomogeneous kernels. -/
noncomputable section
namespace PersistencePays.FiniteNoise
open MeasureTheory ProbabilityTheory
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

def scheduleKernel (K : ℕ → Kernel S S) : ℕ → Kernel S S
  | 0 => Kernel.id
  | n+1 => K n ∘ₖ scheduleKernel K n

instance scheduleKernel_markov (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (scheduleKernel K n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih => change IsMarkovKernel (K n ∘ₖ scheduleKernel K n); infer_instance

theorem scheduleKernel_comp (K : ℕ → Kernel S S) [∀ n, IsMarkovKernel (K n)]
    (μ : Measure S) [SFinite μ] (n : ℕ) : scheduleKernel K n ∘ₘ μ = evolve K μ n := by
  induction n with
  | zero => simp [scheduleKernel, evolve]
  | succ n ih => rw [scheduleKernel, ← Measure.comp_assoc, ih, evolve_succ]

def scheduleTrajectory (f : ℕ → S×B → S) : (n : ℕ) → S → (Fin n → B) → S
  | 0, s, _ => s
  | n+1, s, b => f n (scheduleTrajectory f n s (fun i => b i.castSucc), b (Fin.last n))

theorem measurable_scheduleTrajectory (f : ℕ → S×B → S) (hf : ∀ j, Measurable (f j)) (n : ℕ) :
    Measurable (fun p : S × (Fin n → B) => scheduleTrajectory f n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact (hf n).comp ((ih.comp (measurable_fst.prodMk (measurable_pi_iff.mpr fun i =>
        (measurable_pi_apply i.castSucc).comp measurable_snd))).prodMk
          ((measurable_pi_apply (Fin.last n)).comp measurable_snd))

theorem measurable_scheduleTrajectory_fixed (f : ℕ → S×B → S) (hf : ∀ j, Measurable (f j))
    (n : ℕ) (s : S) : Measurable (scheduleTrajectory f n s) :=
  (measurable_scheduleTrajectory f hf n).comp (measurable_const.prodMk measurable_id)

omit [MeasurableSpace S] [MeasurableSpace B] in
theorem scheduleTrajectory_snoc (f : ℕ → S×B → S) (n : ℕ) (s : S) (b : Fin n → B) (last : B) :
    scheduleTrajectory f (n+1) s (Fin.snoc b last) = f n (scheduleTrajectory f n s b,last) := by
  simp [scheduleTrajectory]

theorem scheduleTrajectory_law (μ : Measure B) [IsProbabilityMeasure μ]
    (f : ℕ → S×B → S) (hf : ∀ j, Measurable (f j)) (n : ℕ) (s : S) :
    (Measure.pi (fun _ : Fin n => μ)).map (scheduleTrajectory f n s) =
      scheduleKernel (fun j => noiseKernel μ (f j) (hf j)) n s := by
  induction n with
  | zero => simp [scheduleTrajectory, scheduleKernel, Kernel.id_apply]
  | succ n ih =>
      rw [← (snoc_preserving μ n).map_eq,
        Measure.map_map (measurable_scheduleTrajectory_fixed f hf (n+1) s)
          (snoc_preserving μ n).measurable]
      simp only [Function.comp_def, scheduleTrajectory_snoc]
      ext t ht
      have hmap : Measurable (fun p : (Fin n → B) × B => f n (scheduleTrajectory f n s p.1,p.2)) :=
        (hf n).comp (((measurable_scheduleTrajectory_fixed f hf n s).comp measurable_fst).prodMk measurable_snd)
      rw [Measure.map_apply hmap ht, Measure.prod_apply (hmap ht),
        scheduleKernel, Kernel.comp_apply' _ _ _ ht, ← ih,
        lintegral_map (Kernel.measurable_coe _ ht) (measurable_scheduleTrajectory_fixed f hf n s)]
      apply lintegral_congr
      intro b
      have hb : Measurable (fun u : B => f n (scheduleTrajectory f n s b,u)) :=
        (hf n).comp (measurable_const.prodMk measurable_id)
      rw [noiseKernel_apply μ (f n) (hf n), Measure.map_apply hb ht]
      rfl

/-- Jointly sampling the initial state and all finite independent noises
produces exactly the inhomogeneous Markov evolution. -/
theorem scheduleTrajectory_random_start_law (μ : Measure B) [IsProbabilityMeasure μ]
    (ν : Measure S) [SFinite ν] (f : ℕ → S×B → S) (hf : ∀ j, Measurable (f j)) (n : ℕ) :
    (ν.prod (Measure.pi (fun _ : Fin n => μ))).map (fun p => scheduleTrajectory f n p.1 p.2) =
      evolve (fun j => noiseKernel μ (f j) (hf j)) ν n := by
  rw [← scheduleKernel_comp]
  ext A hA
  rw [Measure.map_apply (measurable_scheduleTrajectory f hf n) hA,
    Measure.prod_apply ((measurable_scheduleTrajectory f hf n) hA),
    Measure.bind_apply hA (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro s
  rw [← scheduleTrajectory_law μ f hf n s,
    Measure.map_apply (measurable_scheduleTrajectory_fixed f hf n s) hA]
  rfl

end PersistencePays.FiniteNoise
#print axioms PersistencePays.FiniteNoise.scheduleTrajectory_random_start_law
