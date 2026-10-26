import PersistencePays.StageKernels
import PersistencePays.EpochKernel

/-! Identification of sequential Markov stages with independent Gaussian draws. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem velocityOUKernel_apply (r σ : ℝ) (v : E) :
    velocityOUKernel r σ v = (stdGaussian E).map (fun ξ => r • v + σ • ξ) := by
  rw [velocityOUKernel, Kernel.map_apply _ (by unfold gaussianOU; fun_prop),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by unfold gaussianOU; fun_prop) (by fun_prop)]
  rfl

theorem phaseOUKernel_apply (r σ : ℝ) (z : E × E) :
    phaseOUKernel r σ z = (stdGaussian E).map (fun ξ => OBABOPath.ou r σ ξ z) := by
  rw [phaseOUKernel, Kernel.parallelComp_apply, Kernel.id_apply,
    velocityOUKernel_apply, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

def extendedOU (r σ : ℝ) (ξ : E) (z : (E × E) × ℝ) : (E × E) × ℝ :=
  (OBABOPath.ou r σ ξ z.1, z.2)

theorem extendedOU_measurable (r σ : ℝ) :
    Measurable (fun p : ((E × E) × ℝ) × E => extendedOU r σ p.2 p.1) := by
  unfold extendedOU OBABOPath.ou
  fun_prop

theorem extendedOUKernel_apply (r σ : ℝ) (z : (E × E) × ℝ) :
    extendedOUKernel r σ z = (stdGaussian E).map (fun ξ => extendedOU r σ ξ z) := by
  rw [extendedOUKernel, Kernel.parallelComp_apply, Kernel.id_apply,
    phaseOUKernel_apply, Measure.prod_dirac, Measure.map_map (by fun_prop)
      (by unfold OBABOPath.ou; fun_prop)]
  rfl

def stepWithNoise (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (z : (E × E) × ℝ) (ξ : E × E) : (E × E) × ℝ :=
  extendedOU r σ ξ.2
    (adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h) (extendedOU r σ ξ.1 z))

theorem stepWithNoise_measurable (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (z : (E × E) × ℝ) :
    Measurable (stepWithNoise U g h r σ z) := by
  have hm := (verlet_adjusted_preserves_extendedGibbs U hU g hg h).measurable
  unfold stepWithNoise
  exact (extendedOU_measurable r σ).comp
    ((hm.comp ((extendedOU_measurable r σ).comp
      (measurable_const.prodMk measurable_fst))).prodMk measurable_snd)

/-- The sequential stage composition is the actual joint law of two
independent Gaussian vectors applied to the carried-threshold update. -/
theorem stepKernel_apply (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (z : (E × E) × ℝ) :
    stepKernel U hU g hg h r σ z =
      ((stdGaussian E).prod (stdGaussian E)).map (stepWithNoise U g h r σ z) := by
  let D := adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h)
  have hD : Measurable D := (verlet_adjusted_preserves_extendedGibbs U hU g hg h).measurable
  rw [stepKernel, ← Kernel.comp_assoc, adjustedStageKernel,
    Kernel.comp_deterministic_eq_comap]
  ext A hA
  rw [Kernel.comp_apply' _ _ _ hA, extendedOUKernel_apply]
  simp only [Kernel.comap_apply]
  rw [lintegral_map
    (f := fun b => extendedOUKernel r σ (D b) A)
    (g := fun ξ => extendedOU r σ ξ z)
    (((extendedOUKernel r σ).measurable_coe hA).comp hD)
    (by unfold extendedOU OBABOPath.ou; fun_prop)]
  simp_rw [extendedOUKernel_apply]
  rw [Measure.map_apply (stepWithNoise_measurable U hU g hg h r σ z) hA,
    Measure.prod_apply ((stepWithNoise_measurable U hU g hg h r σ z) hA)]
  apply lintegral_congr
  intro ξ
  rw [Measure.map_apply (by unfold extendedOU OBABOPath.ou; fun_prop) hA]
  rfl

/-- Literal equality with the finite-path implementation at one step. -/
theorem stepWithNoise_eq_actualPath (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (z : (E × E) × ℝ) (ξ : E × E) :
    stepWithNoise U g h r σ z ξ =
      OBABOPath.actualPath U g h r σ (fun _ => ξ.1) (fun _ => ξ.2) z.1 z.2 1 := by
  unfold stepWithNoise extendedOU adjustedUpdate OBABOPath.actualPath
  simp only [EpochAcceptance.adjustedPath, OBABOPath.energyDefect, energyIncrement]
  split_ifs with ha <;> simp [ha, OBABOPath.acceptedUpdate, OBABOPath.rejectedUpdate]

end PersistencePays

#print axioms PersistencePays.stepKernel_apply
#print axioms PersistencePays.stepWithNoise_eq_actualPath
