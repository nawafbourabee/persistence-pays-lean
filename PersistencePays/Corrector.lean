import PersistencePays.BrenierMap
import PersistencePays.GibbsPositionMoment
import PersistencePays.KickEntropy

/-! Lu's actual optimal-transport corrector and its finite-moment bounds. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def positionBrenierMap (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) : E → E :=
  QuadraticTransport.brenierMap ⟨μ.fst,inferInstance⟩ ξ

def transportCorrector (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) : ℝ :=
  ∫ z, ⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ

theorem measurable_positionBrenierMap (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) : Measurable (positionBrenierMap μ ξ) :=
  QuadraticTransport.measurable_brenierMap _ _

theorem positionBrenierMap_congr (μ ν : Measure (E × E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : ProbabilityMeasure E)
    (h : μ.fst=ν.fst) : positionBrenierMap μ ξ = positionBrenierMap ν ξ := by
  unfold positionBrenierMap
  congr 1
  exact Subtype.ext h

theorem positionBrenierMap_memLp (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume) :
    MemLp (fun z : E × E => positionBrenierMap μ ξ z.1) 2 μ := by
  have hf : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have ht := QuadraticTransport.brenierMap_memLp ⟨μ.fst,inferInstance⟩ ξ hf hξ hac
  exact (memLp_map_measure_iff (measurable_positionBrenierMap μ ξ).aestronglyMeasurable
    measurable_fst.aemeasurable).mp ht

theorem integrable_inner_of_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x,g x⟫) μ := by
  have hb := (hf.integrable_norm_pow'.add hg.integrable_norm_pow').div_const 2
  apply hb.mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hn := norm_inner_le_norm (𝕜 := ℝ) (f x) (g x)
  change ‖⟪f x,g x⟫‖ ≤ (‖f x‖^2+‖g x‖^2)/2
  nlinarith [sq_nonneg (‖f x‖-‖g x‖)]

theorem transportCorrector_integrable (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume) :
    Integrable (fun z => ⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫) μ :=
  integrable_inner_of_memLp_two hμ.snd (hμ.fst.sub (positionBrenierMap_memLp μ ξ hμ hξ hac))

theorem abs_integral_inner_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, ⟪f x,g x⟫ ∂μ| ≤
      Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have hprod : Integrable (fun x => ‖f x‖*‖g x‖) μ := by
    have hp : MemLp (fun x => ‖f x‖*‖g x‖) 1 μ := hg.norm.mul hf.norm
    exact memLp_one_iff_integrable.mp hp
  have hn := norm_integral_le_integral_norm (f := fun x => ⟪f x,g x⟫) (μ := μ)
  have hb := integral_mono (integrable_inner_of_memLp_two hf hg).norm hprod
    (fun x => norm_inner_le_norm (𝕜 := ℝ) (f x) (g x))
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun x => norm_nonneg (g x)))
    (by simpa using hf.norm) (by simpa using hg.norm)
  rw [Real.norm_eq_abs] at hn
  simpa only [Real.rpow_two, one_div, Real.sqrt_eq_rpow] using hn.trans (hb.trans hc)

theorem transportCorrector_moment_bound (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume) :
    |transportCorrector μ ξ| ≤ Real.sqrt (∫ z : E × E, ‖z.2‖^2 ∂μ) *
      Real.sqrt ((QuadraticTransport.cost ⟨μ.fst,inferInstance⟩ ξ).toReal) := by
  have ht := positionBrenierMap_memLp μ ξ hμ hξ hac
  have hf : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have he := QuadraticTransport.brenierMap_displacement_cost ⟨μ.fst,inferInstance⟩ ξ hf hξ hac
  have hmap : (∫ x, ‖x-positionBrenierMap μ ξ x‖^2 ∂μ.fst) =
      ∫ z : E × E, ‖z.1-positionBrenierMap μ ξ z.1‖^2 ∂μ := by
    exact integral_map measurable_fst.aemeasurable
      ((measurable_id.sub (measurable_positionBrenierMap μ ξ)).norm.pow_const 2).aestronglyMeasurable
  change (∫ x, ‖x-positionBrenierMap μ ξ x‖^2 ∂μ.fst) = _ at he
  rw [← he, hmap]
  exact abs_integral_inner_le_sqrt hμ.snd (hμ.fst.sub ht)

end PersistencePays
#print axioms PersistencePays.transportCorrector_moment_bound
