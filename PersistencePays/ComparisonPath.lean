import PersistencePays.FiniteEntropyPropagation
import PersistencePays.FiniteNoiseSchedule
import PersistencePays.StoppedPathBounds

/-! Equation (5.2): the actual comparison chain, using precisely the same finite
Gaussian arrays as unadjusted OBABO. Its first step is unadjusted. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def comparisonStepWithNoise (g : E → E) (h r σ vstar : ℝ) (j : ℕ)
    (p : (E×E)×(E×E)) : E×E :=
  if j=0 then unadjustedStepWithNoise g h r σ p else
    ou r σ p.2.2 (comparisonVerlet g h vstar (ou r σ p.2.1 p.1))

theorem measurable_comparisonStepWithNoise (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (j : ℕ) : Measurable (comparisonStepWithNoise g h r σ vstar j) := by
  unfold comparisonStepWithNoise
  by_cases hj : j=0
  · simpa only [hj,ite_true] using measurable_unadjustedStepWithNoise g hg h r σ
  · simp only [hj,ite_false]
    have hD := (comparisonVerlet_measurePreserving g hg h vstar).measurable
    unfold ou
    fun_prop

def comparisonPath (g : E → E) (h r σ vstar : ℝ) (ξ ξ' : ℕ → E)
    (z : E×E) : ℕ → E×E
  | 0 => z
  | n+1 => comparisonStepWithNoise g h r σ vstar n
      (comparisonPath g h r σ vstar ξ ξ' z n,(ξ n,ξ' n))

theorem scheduleTrajectory_eq_comparisonPath (g : E → E) (h r σ vstar : ℝ)
    (ξ ξ' : ℕ → E) (z : E×E) (n : ℕ) :
    FiniteNoise.scheduleTrajectory (comparisonStepWithNoise g h r σ vstar) n z
      (fun i => (ξ i,ξ' i)) = comparisonPath g h r σ vstar ξ ξ' z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change comparisonStepWithNoise g h r σ vstar n
      (FiniteNoise.scheduleTrajectory (comparisonStepWithNoise g h r σ vstar) n z
        (fun i => (ξ i,ξ' i)),(ξ n,ξ' n)) = _
    rw [ih]
    rfl

def comparisonEndpoint (g : E → E) (h r σ vstar : ℝ) (n : ℕ)
    (p : (E×E)×NoiseBlock E n) : E×E :=
  comparisonPath g h r σ vstar (fun j => firstNoise n j p.2)
    (fun j => secondNoise n j p.2) p.1 n

theorem comparison_block_trajectory_eq (g : E → E) (h r σ vstar : ℝ) (n : ℕ)
    (z : E×E) (b : NoiseBlock E n) :
    FiniteNoise.scheduleTrajectory (comparisonStepWithNoise g h r σ vstar) n z (zipNoise n b) =
      comparisonEndpoint g h r σ vstar n (z,b) := by
  have hh := scheduleTrajectory_eq_comparisonPath g h r σ vstar
    (fun k => firstNoise n k b) (fun k => secondNoise n k b) z n
  unfold zipNoise
  simpa [firstNoise,secondNoise,comparisonEndpoint] using hh

theorem measurable_comparisonEndpoint (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (n : ℕ) : Measurable (comparisonEndpoint g h r σ vstar n) := by
  have hm := (FiniteNoise.measurable_scheduleTrajectory _
    (measurable_comparisonStepWithNoise g hg h r σ vstar) n).comp
      (measurable_fst.prodMk ((zipNoise_preserving n).measurable.comp measurable_snd))
  simpa only [Function.comp_def,comparison_block_trajectory_eq] using hm

theorem comparison_noiseKernel (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (j : ℕ) :
    FiniteNoise.noiseKernel ((stdGaussian E).prod (stdGaussian E))
      (comparisonStepWithNoise g h r σ vstar j)
      (measurable_comparisonStepWithNoise g hg h r σ vstar j) =
    if j=0 then unadjustedStepKernel g hg h r σ else
      gaussianSandwichKernel (comparisonVerlet g h vstar)
        (comparisonVerlet_measurePreserving g hg h vstar).measurable r σ := by
  ext z : 1
  rw [FiniteNoise.noiseKernel_apply]
  by_cases hj : j=0
  · simp only [hj,ite_true,comparisonStepWithNoise]
    rw [unadjustedStepKernel,FiniteNoise.noiseKernel_apply]
  · simp only [hj,ite_false,comparisonStepWithNoise]
    rw [gaussianSandwichKernel_apply]

theorem comparison_scheduleKernel (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (n : ℕ) :
    FiniteNoise.scheduleKernel (fun j => FiniteNoise.noiseKernel
      ((stdGaussian E).prod (stdGaussian E)) (comparisonStepWithNoise g h r σ vstar j)
      (measurable_comparisonStepWithNoise g hg h r σ vstar j)) (n+1) =
    iterateKernel (gaussianSandwichKernel (comparisonVerlet g h vstar)
      (comparisonVerlet_measurePreserving g hg h vstar).measurable r σ) n ∘ₖ
        unadjustedStepKernel g hg h r σ := by
  induction n with
  | zero =>
    rw [FiniteNoise.scheduleKernel,comparison_noiseKernel g hg h r σ vstar 0]
    simp [FiniteNoise.scheduleKernel,iterateKernel]
  | succ n ih =>
    rw [FiniteNoise.scheduleKernel,ih,comparison_noiseKernel g hg h r σ vstar (n+1)]
    simp only [Nat.succ_ne_zero,ite_false,iterateKernel]
    rw [Kernel.comp_assoc]

/-- Exact endpoint law: one ordinary step, followed by n comparison steps. -/
theorem comparison_endpoint_law (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    (gaussianBlock (n+1)).map (fun b => comparisonEndpoint g h r σ vstar (n+1) (z,b)) =
      (iterateKernel (gaussianSandwichKernel (comparisonVerlet g h vstar)
        (comparisonVerlet_measurePreserving g hg h vstar).measurable r σ) n ∘ₖ
          unadjustedStepKernel g hg h r σ) z := by
  calc
    _ = (gaussianBlock (n+1)).map
        (FiniteNoise.scheduleTrajectory (comparisonStepWithNoise g h r σ vstar) (n+1) z ∘
          zipNoise (n+1)) := by
      congr 1
      funext b
      exact (comparison_block_trajectory_eq g h r σ vstar (n+1) z b).symm
    _ = (Measure.pi (fun _ : Fin (n+1) => (stdGaussian E).prod (stdGaussian E))).map
        (FiniteNoise.scheduleTrajectory (comparisonStepWithNoise g h r σ vstar) (n+1) z) := by
      rw [← Measure.map_map (FiniteNoise.measurable_scheduleTrajectory_fixed _
        (measurable_comparisonStepWithNoise g hg h r σ vstar) (n+1) z)
        (zipNoise_preserving (n+1)).measurable,(zipNoise_preserving (n+1)).map_eq]
    _ = _ := by
      rw [FiniteNoise.scheduleTrajectory_law _ _
        (measurable_comparisonStepWithNoise g hg h r σ vstar),
        comparison_scheduleKernel g hg h r σ vstar]

/-- Deterministic agreement over every prefix as long as the ordinary flights
stay within the comparison radius. No probabilistic independence is assumed here. -/
theorem comparisonPath_agree (g : E → E) (h r σ vstar : ℝ)
    (ξ ξ' : ℕ → E) (z : E×E) (n : ℕ)
    (hfast : ∀ j<n, ‖flightVelocity g h (ou r σ (ξ j)
      (unadjustedPath g h r σ ξ ξ' z j))‖ ≤ vstar) :
    comparisonPath g h r σ vstar ξ ξ' z n = unadjustedPath g h r σ ξ ξ' z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun j hj => hfast j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    rw [comparisonPath,hi]
    have hf := hfast n (Nat.lt_succ_self n)
    change comparisonStepWithNoise g h r σ vstar n
      (unadjustedPath g h r σ ξ ξ' z n,(ξ n,ξ' n)) =
      unadjustedStepWithNoise g h r σ
        (unadjustedPath g h r σ ξ ξ' z n,(ξ n,ξ' n))
    by_cases hn : n=0 <;>
      simp only [comparisonStepWithNoise,hn,ite_true,ite_false,unadjustedStepWithNoise,comparisonVerlet,hf]

/-- The manuscript's actual stopping event forces agreement at every preceding
state, including the endpoint. -/
theorem comparison_agree_on_stoppedBlock {U : E → ℝ} {L h r σ vstar : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hv : 0 ≤ vstar)
    (n : ℕ) (z : E×E) (b : NoiseBlock E n)
    (hb : b ∈ stoppedBlockEvent U (gradient U) h r σ vstar n z)
    (k : ℕ) (hk : k ≤ n) :
    comparisonPath (gradient U) h r σ vstar (fun j => firstNoise n j b)
      (fun j => secondNoise n j b) z k =
      unadjustedPath (gradient U) h r σ (fun j => firstNoise n j b)
        (fun j => secondNoise n j b) z k := by
  apply comparisonPath_agree
  intro j hj
  have hb' := hb j (Nat.lt_of_lt_of_le hj hk)
  have hf := a.normalized_noisy_flight_radius hstar hzero hL hr hv _ hb'.1 _ hb'.2
  linarith

/-- Equation (5.2), for the literal Gaussian implementation and the actual
comparison kernel. The right side is the probability of the stated path exit. -/
theorem comparison_chain_TV_bound {U : E → ℝ} {L h r σ vstar : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hv : 0 ≤ vstar)
    (n : ℕ) (z : E×E) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    probabilityTV (unadjustedEpochKernel (gradient U) hg h r σ (n+1) z)
      ((iterateKernel (gaussianSandwichKernel (comparisonVerlet (gradient U) h vstar)
        (comparisonVerlet_measurePreserving (gradient U) hg h vstar).measurable r σ) n ∘ₖ
          unadjustedStepKernel (gradient U) hg h r σ) z) ≤
      gaussianBlock (n+1) (stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z)ᶜ := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  rw [unadjustedEpochKernel_apply,← comparison_endpoint_law (gradient U) hg]
  apply coupling_probabilityTV_of_agree
  · exact (measurable_unadjustedEpochEndpoint _ hg h r σ (n+1)).comp measurable_prodMk_left
  · exact (measurable_comparisonEndpoint _ hg h r σ vstar (n+1)).comp measurable_prodMk_left
  · intro b hb
    exact (comparison_agree_on_stoppedBlock a hstar hzero hL hr hv (n+1) z b hb
      (n+1) le_rfl).symm

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.comparison_endpoint_law
#print axioms PersistencePays.OBABOPath.comparison_chain_TV_bound
