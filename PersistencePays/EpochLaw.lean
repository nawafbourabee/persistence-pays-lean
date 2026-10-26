import PersistencePays.FiniteNoise
import PersistencePays.StepLaw

/-!
# Equality of the finite Gaussian-block and sequential epoch laws

The first construction is the literal finite-array implementation. The second
is composition of the invariant OU and adjusted Verlet kernels. Identifying
them is necessary before transferring either invariance or warm-start bounds
to the implementation.
-/

noncomputable section
namespace PersistencePays.OBABOPath

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def zipNoise (n : ℕ) (b : NoiseBlock E n) : Fin n → E × E :=
  fun i => (b.1 i, b.2 i)

theorem zipNoise_preserving (n : ℕ) :
    MeasurePreserving (zipNoise (E := E) n) (gaussianBlock n)
      (Measure.pi (fun _ : Fin n => (stdGaussian E).prod (stdGaussian E))) := by
  exact (measurePreserving_arrowProdEquivProdArrow E E (Fin n)
    (fun _ => stdGaussian E) (fun _ => stdGaussian E)).symm

theorem measurable_stepWithNoise_uncurry
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g) (h r σ : ℝ) :
    Measurable (fun p : ((E × E) × ℝ) × (E × E) => stepWithNoise U g h r σ p.1 p.2) := by
  have hm := (verlet_adjusted_preserves_extendedGibbs U hU g hg h).measurable
  unfold stepWithNoise
  exact (extendedOU_measurable r σ).comp
    ((hm.comp ((extendedOU_measurable r σ).comp
      (measurable_fst.prodMk measurable_snd.fst))).prodMk measurable_snd.snd)

theorem step_noiseKernel_eq
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g) (h r σ : ℝ) :
    FiniteNoise.noiseKernel ((stdGaussian E).prod (stdGaussian E))
      (fun p => stepWithNoise U g h r σ p.1 p.2)
      (measurable_stepWithNoise_uncurry U hU g hg h r σ) =
      stepKernel U hU g hg h r σ := by
  ext z A hA
  rw [FiniteNoise.noiseKernel_apply, stepKernel_apply]

theorem trajectory_eq_actualPath
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (ξ ξ' : ℕ → E)
    (z : (E × E) × ℝ) (n : ℕ) :
    FiniteNoise.trajectory (fun p => stepWithNoise U g h r σ p.1 p.2)
      n z (fun i => (ξ i, ξ' i)) = actualPath U g h r σ ξ ξ' z.1 z.2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change stepWithNoise U g h r σ
        (FiniteNoise.trajectory (fun p => stepWithNoise U g h r σ p.1 p.2)
          n z (fun i => (ξ i, ξ' i))) (ξ n, ξ' n) = _
      rw [ih, stepWithNoise_eq_actualPath]
      rfl

theorem block_trajectory_eq
    (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n : ℕ)
    (z : (E × E) × ℝ) (b : NoiseBlock E n) :
    FiniteNoise.trajectory (fun p => stepWithNoise U g h r σ p.1 p.2)
      n z (zipNoise n b) =
      actualPath U g h r σ (fun k => firstNoise n k b)
        (fun k => secondNoise n k b) z.1 z.2 n := by
  have hh := trajectory_eq_actualPath U g h r σ
    (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n
  unfold zipNoise
  simpa [firstNoise, secondNoise] using hh

theorem block_path_law
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) (z : (E × E) × ℝ) :
    (gaussianBlock (E := E) n).map (fun b =>
      actualPath U g h r σ (fun k => firstNoise n k b)
        (fun k => secondNoise n k b) z.1 z.2 n) =
      iterateKernel (stepKernel U hU g hg h r σ) n z := by
  let f := fun p : ((E × E) × ℝ) × (E × E) => stepWithNoise U g h r σ p.1 p.2
  have hf : Measurable f := measurable_stepWithNoise_uncurry U hU g hg h r σ
  calc
    _ = (gaussianBlock n).map (FiniteNoise.trajectory f n z ∘ zipNoise n) := by
      congr 1
      funext b
      exact (block_trajectory_eq U g h r σ n z b).symm
    _ = (Measure.pi (fun _ : Fin n => (stdGaussian E).prod (stdGaussian E))).map
        (FiniteNoise.trajectory f n z) := by
      rw [← Measure.map_map (FiniteNoise.measurable_trajectory_fixed f hf n z)
        (zipNoise_preserving n).measurable, (zipNoise_preserving n).map_eq]
    _ = iterateKernel (FiniteNoise.noiseKernel
        ((stdGaussian E).prod (stdGaussian E)) f hf) n z :=
      FiniteNoise.trajectory_law _ f hf n z
    _ = _ := by rw [step_noiseKernel_eq U hU g hg h r σ]

/-- Drawing all Gaussian vectors at the start of an epoch is exactly the
same chain law as independently drawing them step by step. The single
exponential threshold is carried through the entire composition. -/
theorem epochKernel_eq_sequentialEpochKernel
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) :
    epochKernel U hU g hg h r σ n = sequentialEpochKernel U hU g hg h r σ n := by
  ext z A hA
  have hm := measurable_epochEndpoint U hU g hg h r σ n
  have hz : Measurable (fun p : NoiseBlock E n × ℝ => epochEndpoint U g h r σ n (z, p)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet (Prod.mk z ⁻¹' epochEndpoint U g h r σ n ⁻¹' A) :=
    (measurable_const.prodMk measurable_id) (hm hA)
  rw [epochKernel, Kernel.map_apply' _ hm _ hA,
    Kernel.id_prod_apply' _ _ (hm hA), Kernel.const_apply,
    sequentialEpochKernel, Kernel.map_apply' _ measurable_fst _ hA,
    Kernel.comp_apply' _ _ _ (measurable_fst hA),
    Kernel.lintegral_id_prod (Kernel.measurable_coe _ (measurable_fst hA)), Kernel.const_apply]
  rw [epochRandomness, Measure.prod_apply_symm hset]
  apply lintegral_congr
  intro ell
  rw [← block_path_law U hU g hg h r σ n (z, ell)]
  have hp : Measurable (fun b : NoiseBlock E n => actualPath U g h r σ
      (fun k => firstNoise n k b) (fun k => secondNoise n k b) z ell n) :=
    measurable_actualPath U hU g hg h r σ (firstNoise n) (secondNoise n)
      (measurable_firstNoise n) (measurable_secondNoise n) (fun _ => z)
      measurable_const (fun _ => ell) measurable_const n
  rw [Measure.map_apply hp (measurable_fst hA)]
  rfl

/-- Invariance of the literal finite-array implementation, not merely of an
abstract kernel assembled from its stages. -/
theorem epochKernel_invariant
    (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (hnorm : r ^ 2 + σ ^ 2 = 1) (n : ℕ) :
    epochKernel U hU g hg h r σ n ∘ₘ phaseGibbs U = phaseGibbs U := by
  rw [epochKernel_eq_sequentialEpochKernel]
  exact sequentialEpochKernel_invariant U hU hi g hg h r σ hnorm n

end PersistencePays.OBABOPath

namespace PersistencePays

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Lemma 2.3 for the finite-array implementation under the paper's actual
potential assumptions and actual OU coefficients. -/
theorem A1.finite_epoch_invariant {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) (n : ℕ) :
    OBABOPath.epochKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h
      (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) n ∘ₘ
      phaseGibbs U = phaseGibbs U := by
  rw [OBABOPath.epochKernel_eq_sequentialEpochKernel]
  exact a.epoch_invariant γ h hγ hh n

end PersistencePays

#print axioms PersistencePays.OBABOPath.block_path_law
#print axioms PersistencePays.OBABOPath.epochKernel_eq_sequentialEpochKernel
#print axioms PersistencePays.OBABOPath.epochKernel_invariant
#print axioms PersistencePays.A1.finite_epoch_invariant
