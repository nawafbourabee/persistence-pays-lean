import PersistencePays.EpochLaw
import PersistencePays.EpochRejectionBound
import PersistencePays.CouplingTV

/-!
# The actual adjusted/unadjusted epoch coupling

Both endpoints are explicit functions of the same finite Gaussian block and
the independent exponential threshold. Their marginal laws are proved equal
to the actual kernels before the coupling inequality is applied.
-/

noncomputable section
namespace PersistencePays.OBABOPath

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_unadjustedPath_initial
    {Ω : Type*} [MeasurableSpace Ω]
    (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (ξ ξ' : ℕ → Ω → E) (hξ : ∀ k, Measurable (ξ k)) (hξ' : ∀ k, Measurable (ξ' k))
    (z : Ω → E × E) (hz : Measurable z) (n : ℕ) :
    Measurable (fun ω => unadjustedPath g h r σ (fun k => ξ k ω) (fun k => ξ' k ω)
      (z ω) n) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
      change Measurable (fun ω => ou r σ (ξ' n ω)
        (verlet g h (ou r σ (ξ n ω)
          (unadjustedPath g h r σ (fun k => ξ k ω) (fun k => ξ' k ω) (z ω) n))))
      dsimp only [ou, verlet, kick, drift]
      fun_prop

def unadjustedEpochEndpoint (g : E → E) (h r σ : ℝ) (n : ℕ)
    (p : (E × E) × NoiseBlock E n) : E × E :=
  unadjustedPath g h r σ (fun k => firstNoise n k p.2)
    (fun k => secondNoise n k p.2) p.1 n

theorem measurable_unadjustedEpochEndpoint (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) : Measurable (unadjustedEpochEndpoint g h r σ n) := by
  exact measurable_unadjustedPath_initial (Ω := (E × E) × NoiseBlock E n) g hg h r σ
    (fun k p => firstNoise n k p.2) (fun k p => secondNoise n k p.2)
    (fun k => (measurable_firstNoise n k).comp measurable_snd)
    (fun k => (measurable_secondNoise n k).comp measurable_snd)
    Prod.fst measurable_fst n

def unadjustedEpochKernel (g : E → E) (_hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    Kernel (E × E) (E × E) :=
  (Kernel.id ×ₖ Kernel.const (E × E) (gaussianBlock (E := E) n)).map
    (unadjustedEpochEndpoint g h r σ n)

instance unadjustedEpochKernel_markov (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) : IsMarkovKernel (unadjustedEpochKernel g hg h r σ n) :=
  Kernel.IsMarkovKernel.map _ (measurable_unadjustedEpochEndpoint g hg h r σ n)

theorem unadjustedEpochKernel_apply (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) (z : E × E) :
    unadjustedEpochKernel g hg h r σ n z =
      (gaussianBlock (E := E) n).map (fun b => unadjustedEpochEndpoint g h r σ n (z, b)) :=
  FiniteNoise.noiseKernel_apply _ _ (measurable_unadjustedEpochEndpoint g hg h r σ n) z

theorem epochKernel_apply (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) (z : E × E) :
    epochKernel U hU g hg h r σ n z =
      (epochRandomness (E := E) n).map (fun p => epochEndpoint U g h r σ n (z, p)) :=
  FiniteNoise.noiseKernel_apply _ _ (measurable_epochEndpoint U hU g hg h r σ n) z

/-- Forgetting the unused exponential threshold gives exactly the
unadjusted OBABO law; no assertion of independence is left as a premise. -/
theorem unadjusted_law_with_threshold (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) (z : E × E) :
    (epochRandomness (E := E) n).map
      (fun p => unadjustedEpochEndpoint g h r σ n (z, p.1)) =
      unadjustedEpochKernel g hg h r σ n z := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hm : Measurable (fun b => unadjustedEpochEndpoint g h r σ n (z, b)) :=
    (measurable_unadjustedEpochEndpoint g hg h r σ n).comp (measurable_const.prodMk measurable_id)
  rw [unadjustedEpochKernel_apply]
  change (epochRandomness n).map ((fun b => unadjustedEpochEndpoint g h r σ n (z, b)) ∘ Prod.fst) = _
  rw [← Measure.map_map hm measurable_fst, epochRandomness, Measure.map_fst_prod,
    measure_univ, one_smul]

theorem adjusted_unadjusted_epoch_probabilityTV
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) (z : E × E) :
    probabilityTV (epochKernel U hU g hg h r σ n z)
      (unadjustedEpochKernel g hg h r σ n z) ≤
      epochRandomness (E := E) n
        {p | ¬ everyMoveAccepted U g h r σ
          (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n} := by
  rw [epochKernel_apply, ← unadjusted_law_with_threshold]
  apply coupling_probabilityTV_of_agree (epochRandomness n)
    (fun p => epochEndpoint U g h r σ n (z, p))
    (fun p => unadjustedEpochEndpoint g h r σ n (z, p.1))
    ((measurable_epochEndpoint U hU g hg h r σ n).comp (measurable_const.prodMk measurable_id))
    ((measurable_unadjustedEpochEndpoint g hg h r σ n).comp
      (measurable_const.prodMk measurable_fst))
    {p | everyMoveAccepted U g h r σ
      (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n}
  intro p hp
  exact congrArg Prod.fst (actualPath_eq_unadjusted_on_acceptance U g h r σ
    (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n hp)

/-- The clipped energy-error estimate controls the actual adjusted/unadjusted
endpoint discrepancy in total variation. -/
theorem adjusted_unadjusted_epoch_probabilityTV_bound {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (n : ℕ) (hn : 0 < n) (z : E × E) :
    probabilityTV
      (epochKernel U a.twice_contDiff.continuous.measurable (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ n z)
      (unadjustedEpochKernel (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ n z) ≤
      ENNReal.ofReal (∫ b, min 1 (rejectionBudget U (U a.minimizer) L (gradient U) h r σ
        (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n) ∂gaussianBlock n) := by
  apply (adjusted_unadjusted_epoch_probabilityTV U _ (gradient U) _ h r σ n z).trans
  calc
    _ = ENNReal.ofReal ((epochRandomness (E := E) n).real
        {p | ¬ everyMoveAccepted U (gradient U) h r σ
          (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n}) :=
      (ENNReal.ofReal_toReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (gaussian_epoch_rejection_bound a h r σ z n hn)

end PersistencePays.OBABOPath

#print axioms PersistencePays.OBABOPath.adjusted_unadjusted_epoch_probabilityTV
#print axioms PersistencePays.OBABOPath.adjusted_unadjusted_epoch_probabilityTV_bound
