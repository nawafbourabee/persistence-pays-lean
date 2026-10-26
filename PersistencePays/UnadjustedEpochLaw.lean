import PersistencePays.EpochCoupling

/-! The finite Gaussian block law is exactly the n-fold unadjusted OBABO law. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unadjustedStepWithNoise (g : E → E) (h r σ : ℝ) (p : (E×E)×(E×E)) : E×E :=
  ou r σ p.2.2 (verlet g h (ou r σ p.2.1 p.1))

theorem measurable_unadjustedStepWithNoise (g : E → E) (hg : Measurable g) (h r σ : ℝ) :
    Measurable (unadjustedStepWithNoise g h r σ) := by
  unfold unadjustedStepWithNoise ou verlet kick drift
  fun_prop

def unadjustedStepKernel (g : E → E) (hg : Measurable g) (h r σ : ℝ) : Kernel (E×E) (E×E) :=
  FiniteNoise.noiseKernel ((stdGaussian E).prod (stdGaussian E))
    (unadjustedStepWithNoise g h r σ) (measurable_unadjustedStepWithNoise g hg h r σ)

instance unadjustedStepKernel_markov (g : E → E) (hg : Measurable g) (h r σ : ℝ) :
    IsMarkovKernel (unadjustedStepKernel g hg h r σ) := by
  unfold unadjustedStepKernel
  infer_instance

theorem trajectory_eq_unadjustedPath (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : E×E) (n : ℕ) :
    FiniteNoise.trajectory (unadjustedStepWithNoise g h r σ) n z (fun i => (ξ i,ξ' i)) =
      unadjustedPath g h r σ ξ ξ' z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change unadjustedStepWithNoise g h r σ
        (FiniteNoise.trajectory (unadjustedStepWithNoise g h r σ) n z (fun i => (ξ i,ξ' i)),(ξ n,ξ' n)) = _
      rw [ih]
      rfl

theorem unadjusted_block_trajectory_eq (g : E → E) (h r σ : ℝ) (n : ℕ)
    (z : E×E) (b : NoiseBlock E n) :
    FiniteNoise.trajectory (unadjustedStepWithNoise g h r σ) n z (zipNoise n b) =
      unadjustedEpochEndpoint g h r σ n (z,b) := by
  have hh := trajectory_eq_unadjustedPath g h r σ
    (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n
  unfold zipNoise
  simpa [firstNoise,secondNoise,unadjustedEpochEndpoint] using hh

theorem unadjustedEpochKernel_eq_iterate (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) :
    unadjustedEpochKernel g hg h r σ n = iterateKernel (unadjustedStepKernel g hg h r σ) n := by
  ext z : 1
  rw [unadjustedEpochKernel_apply]
  calc
    _ = (gaussianBlock n).map (FiniteNoise.trajectory (unadjustedStepWithNoise g h r σ) n z ∘ zipNoise n) := by
      congr 1
      funext b
      exact (unadjusted_block_trajectory_eq g h r σ n z b).symm
    _ = (Measure.pi (fun _ : Fin n => (stdGaussian E).prod (stdGaussian E))).map
        (FiniteNoise.trajectory (unadjustedStepWithNoise g h r σ) n z) := by
      rw [← Measure.map_map (FiniteNoise.measurable_trajectory_fixed _
        (measurable_unadjustedStepWithNoise g hg h r σ) n z)
        (zipNoise_preserving n).measurable, (zipNoise_preserving n).map_eq]
    _ = _ := FiniteNoise.trajectory_law _ _ (measurable_unadjustedStepWithNoise g hg h r σ) n z

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.unadjustedEpochKernel_eq_iterate
