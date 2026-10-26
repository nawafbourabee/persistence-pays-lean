import PersistencePays.EpochLaw
import PersistencePays.GradientCost

/-!
# The complete cached sampler: law and exact oracle count

A finite array contains one independent Gaussian block and one independent
exponential threshold per epoch. The implementation consumes this array,
carries a valid force cache across rejections and epoch boundaries, and has
exactly the iterated epoch-kernel law.
-/

noncomputable section
namespace PersistencePays.CachedOBABO

open MeasureTheory ProbabilityTheory OBABOPath

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem runEpochs_phase_trajectory
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n : ℕ)
    (noise : ℕ → NoiseBlock E n × ℝ) (s : State E) (hc : Consistent g s) (N : ℕ) :
    (runEpochs U g h r σ
      (fun j k => firstNoise n k (noise j).1)
      (fun j k => secondNoise n k (noise j).1)
      (fun j => (noise j).2) n s N).phase =
      FiniteNoise.trajectory (epochEndpoint U g h r σ n) N s.phase
        (fun i => noise i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      let current := runEpochs U g h r σ
        (fun j k => firstNoise n k (noise j).1)
        (fun j k => secondNoise n k (noise j).1)
        (fun j => (noise j).2) n s N
      have hcurrent : Consistent g current := runEpochs_consistent U g h r σ _ _ _ n s hc N
      have hp := congrArg Prod.fst (runSteps_projection U g h r σ
        (fun k => firstNoise n k (noise N).1) (fun k => secondNoise n k (noise N).1)
        (refreshThreshold current (noise N).2) hcurrent n)
      change (runSteps U g h r σ
        (fun k => firstNoise n k (noise N).1) (fun k => secondNoise n k (noise N).1)
        (refreshThreshold current (noise N).2) n).phase = _ at hp
      change (runSteps U g h r σ
        (fun k => firstNoise n k (noise N).1) (fun k => secondNoise n k (noise N).1)
        (refreshThreshold current (noise N).2) n).phase = _
      rw [hp]
      change epochEndpoint U g h r σ n (current.phase, noise N) = _
      rw [show current.phase = FiniteNoise.trajectory (epochEndpoint U g h r σ n)
        N s.phase (fun i => noise i) from ih]
      rfl

/-- The finite input array, padded only beyond its consumed indices. -/
def epochInput (n N k : ℕ) (b : Fin N → NoiseBlock E n × ℝ) : NoiseBlock E n × ℝ :=
  if hk : k < N then b ⟨k, hk⟩ else ((fun _ => 0, fun _ => 0), 0)

def simulate (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n N : ℕ)
    (z : E × E) (b : Fin N → NoiseBlock E n × ℝ) : State E :=
  runEpochs U g h r σ
    (fun j k => firstNoise n k (epochInput n N j b).1)
    (fun j k => secondNoise n k (epochInput n N j b).1)
    (fun j => (epochInput n N j b).2) n (initializeCache g z 0) N

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem simulate_phase_eq_trajectory
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n N : ℕ)
    (z : E × E) (b : Fin N → NoiseBlock E n × ℝ) :
    (simulate U g h r σ n N z b).phase =
      FiniteNoise.trajectory (epochEndpoint U g h r σ n) N z b := by
  have hp := runEpochs_phase_trajectory U g h r σ n
    (fun j => epochInput n N j b) (initializeCache g z 0) (initialize_consistent g z 0) N
  simpa [simulate, epochInput, initializeCache] using hp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Rejected proposals incur the same one-gradient cost as accepted ones;
threshold draws and epoch changes incur no additional gradient queries. -/
theorem simulate_queries_exact
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n N : ℕ)
    (z : E × E) (b : Fin N → NoiseBlock E n × ℝ) :
    (simulate U g h r σ n N z b).calls = N * n + 1 :=
  total_gradient_queries U g h r σ _ _ _ n N z

theorem simulate_law
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n N : ℕ) (z : E × E) :
    (Measure.pi (fun _ : Fin N => epochRandomness (E := E) n)).map
      (fun b => (simulate U g h r σ n N z b).phase) =
      iterateKernel (epochKernel U hU g hg h r σ n) N z := by
  have heq : (fun b => (simulate U g h r σ n N z b).phase) =
      FiniteNoise.trajectory (epochEndpoint U g h r σ n) N z := by
    funext b
    exact simulate_phase_eq_trajectory U g h r σ n N z b
  rw [heq]
  exact FiniteNoise.trajectory_law (epochRandomness n) (epochEndpoint U g h r σ n)
    (measurable_epochEndpoint U hU g hg h r σ n) N z

/-- The concrete cached sampler has the law of the invariant sequential
kernel, over an arbitrary number of epochs. -/
theorem simulate_law_sequential
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n N : ℕ) (z : E × E) :
    (Measure.pi (fun _ : Fin N => epochRandomness (E := E) n)).map
      (fun b => (simulate U g h r σ n N z b).phase) =
      iterateKernel (sequentialEpochKernel U hU g hg h r σ n) N z := by
  rw [simulate_law U hU g hg h r σ n N z, epochKernel_eq_sequentialEpochKernel]

end PersistencePays.CachedOBABO

#print axioms PersistencePays.CachedOBABO.simulate_queries_exact
#print axioms PersistencePays.CachedOBABO.simulate_law_sequential
