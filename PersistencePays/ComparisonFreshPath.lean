import PersistencePays.ScheduleFreshNoise
import PersistencePays.ComparisonFlightBounds

/-! The actual pre-Hamiltonian comparison state on a finite Gaussian block. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def comparisonPreEndpoint (g : E → E) (h r σ vstar : ℝ) (n : ℕ)
    (z : E×E) (b : NoiseBlock E (n+2)) : E×E :=
  ou r σ (firstNoise (n+2) (n+1) b)
    (comparisonEndpoint g h r σ vstar (n+1) (z,prefixBlock (Nat.le_succ (n+1)) b))

theorem comparisonPreEndpoint_eq (g : E → E) (h r σ vstar : ℝ) (n : ℕ)
    (z : E×E) (b : NoiseBlock E (n+2)) :
    comparisonPreEndpoint g h r σ vstar n z b =
      ou r σ (FiniteNoise.scheduleBeforeLastStep (comparisonStepWithNoise g h r σ vstar)
        (n+1) z (zipNoise (n+2) b)).2.1
        (FiniteNoise.scheduleBeforeLastStep (comparisonStepWithNoise g h r σ vstar)
          (n+1) z (zipNoise (n+2) b)).1 := by
  unfold comparisonPreEndpoint
  rw [← comparison_block_trajectory_eq, zipNoise_prefixBlock]
  simp only [FiniteNoise.scheduleBeforeLastStep]
  congr 1
  · simp [firstNoise,zipNoise,Fin.last]

theorem measurable_comparisonPreEndpoint (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    Measurable (comparisonPreEndpoint g h r σ vstar n z) := by
  have he := (FiniteNoise.measurable_scheduleBeforeLastStep (comparisonStepWithNoise g h r σ vstar)
    (measurable_comparisonStepWithNoise g hg h r σ vstar) (n+1) z).comp
      (zipNoise_preserving (n+2)).measurable
  have ho : Measurable (fun p : (E×E)×(E×E) => ou r σ p.2.1 p.1) := by unfold ou; fun_prop
  convert ho.comp he using 1
  funext b
  exact comparisonPreEndpoint_eq g h r σ vstar n z b

theorem comparison_pre_endpoint_law (g : E → E) (hg : Measurable g)
    (h r σ vstar : ℝ) (n : ℕ) (z : E×E) :
    (gaussianBlock (n+2)).map (comparisonPreEndpoint g h r σ vstar n z) =
      phaseOUKernel r σ ∘ₘ comparisonChainLaw g hg h r σ vstar n z := by
  let μ := comparisonChainLaw g hg h r σ vstar n z
  let f := comparisonStepWithNoise g h r σ vstar
  let B := FiniteNoise.scheduleBeforeLastStep f (n+1) z
  let T : (E×E)×(E×E) → E×E := fun p => ou r σ p.2.1 p.1
  have hB : Measurable B := FiniteNoise.measurable_scheduleBeforeLastStep f
    (measurable_comparisonStepWithNoise g hg h r σ vstar) (n+1) z
  have hT : Measurable T := by unfold T ou; fun_prop
  have hfun : comparisonPreEndpoint g h r σ vstar n z = T ∘ B ∘ zipNoise (n+2) :=
    funext (comparisonPreEndpoint_eq g h r σ vstar n z)
  rw [hfun, ← Function.comp_assoc, ← Measure.map_map (hT.comp hB) (zipNoise_preserving (n+2)).measurable,
    (zipNoise_preserving (n+2)).map_eq, ← Measure.map_map hT hB,
    FiniteNoise.schedule_fresh_noise_law]
  have hK := comparison_scheduleKernel g hg h r σ vstar n
  change ((FiniteNoise.scheduleKernel (fun j => FiniteNoise.noiseKernel
    ((stdGaussian E).prod (stdGaussian E)) (f j)
      (measurable_comparisonStepWithNoise g hg h r σ vstar j)) (n+1) z).prod
      ((stdGaussian E).prod (stdGaussian E))).map T = _
  rw [hK]
  change (μ.prod ((stdGaussian E).prod (stdGaussian E))).map T = phaseOUKernel r σ ∘ₘ μ
  let project : ((E×E)×(E×E)) → (E×E)×E := fun p => (p.1,p.2.1)
  have hp : Measurable project := measurable_fst.prodMk measurable_snd.fst
  have hproject : (μ.prod ((stdGaussian E).prod (stdGaussian E))).map project = μ.prod (stdGaussian E) := by
    have he := Measure.map_prod_map μ ((stdGaussian E).prod (stdGaussian E)) measurable_id measurable_fst
    change (μ.map id).prod (((stdGaussian E).prod (stdGaussian E)).map Prod.fst) =
      (μ.prod ((stdGaussian E).prod (stdGaussian E))).map project at he
    simpa only [Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] using he.symm
  have houter : Measurable (fun p : (E×E)×E => ou r σ p.2 p.1) := by unfold ou; fun_prop
  change (μ.prod ((stdGaussian E).prod (stdGaussian E))).map
      ((fun p : (E×E)×E => ou r σ p.2 p.1) ∘ project) = _
  rw [← Measure.map_map houter hp, hproject, ← phaseOUKernel_comp_map]

theorem comparison_pre_flight_agree {U : E → ℝ} {L h r σ vstar : ℝ}
    (a : A1 U 1 L) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hr : r^2 ≤ 1) (hv : 0 ≤ vstar)
    (n : ℕ) (z : E×E) (b : NoiseBlock E (n+2))
    (hb : b ∈ stoppedBlockEvent U (gradient U) h r σ vstar (n+2) z) :
    flightVelocity (gradient U) h (comparisonPreEndpoint (gradient U) h r σ vstar n z b) =
      lastFlight (gradient U) h r σ (n+1) z b := by
  have hp := stoppedBlockEvent_prefix U (gradient U) h r σ vstar (Nat.le_succ (n+1)) z hb
  have hc := comparison_agree_on_stoppedBlock a hstar hzero hL hr hv (n+1) z
    (prefixBlock (Nat.le_succ (n+1)) b) hp (n+1) le_rfl
  unfold comparisonPreEndpoint comparisonEndpoint
  rw [hc, unadjustedPath_prefixBlock (gradient U) h r σ _ le_rfl]
  rfl

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.comparison_pre_endpoint_law
#print axioms PersistencePays.OBABOPath.comparison_pre_flight_agree
