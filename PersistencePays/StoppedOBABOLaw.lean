import PersistencePays.StoppedNoiseLaw
import PersistencePays.StoppedLyapunov

/-! Literal finite Gaussian paths and the stopped OBABO transition. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The manuscript's survival event: all preceding energies and first refreshes
stay within their thresholds. Both Gaussian arrays remain independent in the
underlying law; no conditioning is built into the update. -/
def stoppedBlockEvent (U : E → ℝ) (g : E → E) (h r σ vstar : ℝ)
    (n : ℕ) (z : E×E) : Set (NoiseBlock E n) :=
  {b | ∀ k<n,
    phaseEnergy U (unadjustedPath g h r σ
      (fun j => firstNoise n j b) (fun j => secondNoise n j b) z k) ≤ vstar^2/32 ∧
    ‖σ • firstNoise n k b‖ ≤ vstar/2}

theorem stoppedBlockEvent_eq (U : E → ℝ) (g : E → E) (h r σ vstar : ℝ)
    (n : ℕ) (z : E×E) :
    stoppedBlockEvent U g h r σ vstar n z = zipNoise n ⁻¹'
      FiniteNoise.goodBlock (unadjustedStepWithNoise g h r σ)
        (stoppedOBABOGood U σ vstar) n z := by
  ext b
  have he : zipNoise n b = (fun i : Fin n => (firstNoise n i b, secondNoise n i b)) := by
    funext i
    simp [zipNoise,firstNoise,secondNoise]
  rw [mem_preimage, he]
  rw [FiniteNoise.goodBlock_iff_all _ _
    (fun j => (firstNoise n j b, secondNoise n j b)) n z]
  simp only [stoppedBlockEvent, mem_setOf_eq, stoppedOBABOGood,
    trajectory_eq_unadjustedPath g h r σ (fun j => firstNoise n j b)
      (fun j => secondNoise n j b) z]

theorem stoppedBlockEvent_measurable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    MeasurableSet (stoppedBlockEvent U (gradient U) h r σ vstar n z) := by
  rw [stoppedBlockEvent_eq]
  exact (zipNoise_preserving n).measurable
    (FiniteNoise.measurable_goodBlock _ (unadjustedNoiseStep_measurable a h r σ)
      _ (stoppedOBABOGood_measurable a σ vstar) n z)

/-- Exact stopped endpoint law for the literal two-array Gaussian implementation. -/
theorem stoppedOBABO_block_law {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    ((gaussianBlock n).restrict (stoppedBlockEvent U (gradient U) h r σ vstar n z)).map
      (fun b => unadjustedEpochEndpoint (gradient U) h r σ n (z,b)) =
        iterateKernel (stoppedOBABOKernel a h r σ vstar) n z := by
  have hf : Measurable (unadjustedStepWithNoise (gradient U) h r σ) :=
    unadjustedNoiseStep_measurable a h r σ
  have hG := stoppedOBABOGood_measurable a σ vstar
  have hB := FiniteNoise.measurable_goodBlock _ hf _ hG n z
  rw [stoppedBlockEvent_eq]
  calc
    _ = ((gaussianBlock n).restrict (zipNoise n ⁻¹'
        FiniteNoise.goodBlock (unadjustedStepWithNoise (gradient U) h r σ)
          (stoppedOBABOGood U σ vstar) n z)).map
        (FiniteNoise.trajectory (unadjustedStepWithNoise (gradient U) h r σ) n z ∘ zipNoise n) := by
      congr 1
      funext b
      exact (unadjusted_block_trajectory_eq (gradient U) h r σ n z b).symm
    _ = ((Measure.pi (fun _ : Fin n => (stdGaussian E).prod (stdGaussian E))).restrict
        (FiniteNoise.goodBlock (unadjustedStepWithNoise (gradient U) h r σ)
          (stoppedOBABOGood U σ vstar) n z)).map
        (FiniteNoise.trajectory (unadjustedStepWithNoise (gradient U) h r σ) n z) := by
      rw [← Measure.map_map (FiniteNoise.measurable_trajectory_fixed _ hf n z)
        (zipNoise_preserving n).measurable,
        ← Measure.restrict_map (zipNoise_preserving n).measurable hB,
        (zipNoise_preserving n).map_eq]
    _ = _ := FiniteNoise.stopped_trajectory_law _ _ hf _ hG n z

/-- Integrating any nonnegative measurable observable against the actual stopped
path law is exactly integration against the killed-kernel iterate. -/
theorem stoppedOBABO_block_lintegral {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) (F : E×E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ b in stoppedBlockEvent U (gradient U) h r σ vstar n z,
      F (unadjustedEpochEndpoint (gradient U) h r σ n (z,b)) ∂gaussianBlock n) =
      ∫⁻ w, F w ∂iterateKernel (stoppedOBABOKernel a h r σ vstar) n z := by
  have he : Measurable (fun b : NoiseBlock E n =>
      unadjustedEpochEndpoint (gradient U) h r σ n (z,b)) :=
    (measurable_unadjustedEpochEndpoint (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ n).comp (f:=fun b : NoiseBlock E n => (z,b)) measurable_prodMk_left
  rw [← stoppedOBABO_block_law a h r σ vstar n z, lintegral_map hF he]

/-- The stopped kernel's missing mass is the actual finite-path exit probability. -/
theorem stoppedOBABO_block_mass {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    iterateKernel (stoppedOBABOKernel a h r σ vstar) n z univ =
      gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z) := by
  have he : Measurable (fun b : NoiseBlock E n =>
      unadjustedEpochEndpoint (gradient U) h r σ n (z,b)) :=
    (measurable_unadjustedEpochEndpoint (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ n).comp (f:=fun b : NoiseBlock E n => (z,b)) measurable_prodMk_left
  rw [← stoppedOBABO_block_law a h r σ vstar n z, Measure.map_apply he MeasurableSet.univ]
  simp

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stoppedOBABO_block_law
#print axioms PersistencePays.OBABOPath.stoppedOBABO_block_lintegral
