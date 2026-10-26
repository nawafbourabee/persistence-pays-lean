import PersistencePays.ComparisonVerlet
import PersistencePays.CorrectorStages
import PersistencePays.CorrectorBounds
import PersistencePays.QuadraticDistance

/-! Actual speed reflection: Gaussian conditional entropy is unchanged, and
its corrector jump is controlled by the exceptional velocity energy. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def speedFlipEquiv (vstar : ℝ) : (E×E) ≃ᵐ (E×E) where
  toFun := speedFlip vstar
  invFun := speedFlip vstar
  left_inv := speedFlip_involutive vstar
  right_inv := speedFlip_involutive vstar
  measurable_toFun := (speedFlip_measurePreserving vstar).measurable
  measurable_invFun := (speedFlip_measurePreserving vstar).measurable

instance speedFlip_map_probability (μ : Measure (E×E)) [IsProbabilityMeasure μ] (vstar : ℝ) :
    IsProbabilityMeasure (μ.map (speedFlipEquiv vstar)) :=
  Measure.isProbabilityMeasure_map (speedFlipEquiv vstar).measurable.aemeasurable

theorem speedFlip_fst (vstar : ℝ) (z : E×E) : (speedFlip vstar z).1=z.1 := by
  simp only [speedFlip,velocityFlip]; split_ifs <;> rfl

theorem speedFlip_snd_norm (vstar : ℝ) (z : E×E) : ‖(speedFlip vstar z).2‖=‖z.2‖ := by
  simp only [speedFlip,velocityFlip]; split_ifs <;> simp

theorem speedFlip_norm (vstar : ℝ) (z : E×E) : ‖speedFlip vstar z‖=‖z‖ := by
  simp only [Prod.norm_def,speedFlip_fst,speedFlip_snd_norm]

theorem speedFlip_memLp {μ : Measure (E×E)} {p : ℝ≥0∞} (hμ : MemLp id p μ) (vstar : ℝ) :
    MemLp (speedFlipEquiv vstar) p μ :=
  hμ.congr_norm (speedFlipEquiv vstar).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z=>(speedFlip_norm vstar z).symm))

theorem speedFlip_gaussian_preserving (ν : Measure E) [IsProbabilityMeasure ν] (vstar : ℝ) :
    MeasurePreserving (speedFlipEquiv (E:=E) vstar) (ν.prod (stdGaussian E))
      (ν.prod (stdGaussian E)) := by
  have hneg : MeasurePreserving (fun x:E=>-x) (stdGaussian E) (stdGaussian E) :=
    ⟨by fun_prop,stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  have hflip : MeasurePreserving (velocityFlip (E:=E)) (ν.prod (stdGaussian E))
      (ν.prod (stdGaussian E)) := (MeasurePreserving.id ν).prod hneg
  have hs : MeasurableSet {z:E×E|vstar<‖z.2‖} := measurableSet_lt measurable_const measurable_snd.norm
  have he : velocityFlip ⁻¹' {z:E×E|vstar<‖z.2‖}={z:E×E|vstar<‖z.2‖} := by
    ext z; simp [velocityFlip]
  exact preserving_piecewise_id _ _ hflip _ hs he

theorem speedFlip_conditional_entropy (μ : Measure (E×E)) [IsProbabilityMeasure μ] (vstar : ℝ) :
    conditionalGaussianEntropy (μ.map (speedFlipEquiv vstar)) (stdGaussian E) 0 =
      conditionalGaussianEntropy μ (stdGaussian E) 0 := by
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
  rw [map_position_preserving_fst μ (speedFlipEquiv vstar) (speedFlip_fst vstar)]
  have he := klDiv_map_measurableEquiv (speedFlipEquiv vstar) μ (μ.fst.prod (stdGaussian E))
  rwa [(speedFlip_gaussian_preserving μ.fst vstar).map_eq] at he

theorem transportCorrector_speedFlip (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ) (hξ : MemLp id 2 (ξ:Measure E))
    (hac : μ.fst ≪ volume) (vstar : ℝ) :
    transportCorrector (μ.map (speedFlipEquiv vstar)) ξ-transportCorrector μ ξ =
      -2*(∫ z in {z:E×E|vstar<‖z.2‖},⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ) := by
  let A := {z:E×E|vstar<‖z.2‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_snd.norm
  have hp := map_position_preserving_fst μ (speedFlipEquiv vstar) (speedFlip_fst vstar)
  have hT := measurable_positionBrenierMap μ ξ
  have hi := transportCorrector_integrable μ ξ hμ hξ hac
  have hc : Measurable (fun z:E×E=>⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫) :=
    measurable_snd.inner (measurable_fst.sub (hT.comp measurable_fst))
  unfold transportCorrector
  rw [positionBrenierMap_congr _ μ ξ hp,integral_map
    (speedFlipEquiv vstar).measurable.aemeasurable hc.aestronglyMeasurable]
  have he : (fun z:E×E=>⟪(speedFlipEquiv vstar z).2,
      (speedFlipEquiv vstar z).1-positionBrenierMap μ ξ (speedFlipEquiv vstar z).1⟫) =
      fun z=>⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫-
        2*A.indicator (fun z=>⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫) z := by
    funext z
    change ⟪(speedFlip vstar z).2,(speedFlip vstar z).1-positionBrenierMap μ ξ (speedFlip vstar z).1⟫ = _
    rw [speedFlip_fst]
    by_cases hz:vstar<‖z.2‖
    · simp [speedFlip,hz,velocityFlip,A,inner_neg_left]; ring
    · simp [speedFlip,hz,A]
  rw [he,integral_sub hi ((hi.indicator hA).const_mul 2),integral_const_mul,
    integral_indicator hA]
  ring

theorem transportCorrector_speedFlip_bound (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ) (hξ : MemLp id 2 (ξ:Measure E))
    (hac : μ.fst ≪ volume) (vstar : ℝ) :
    |transportCorrector (μ.map (speedFlipEquiv vstar)) ξ-transportCorrector μ ξ| ≤
      2*Real.sqrt (∫ z in {z:E×E|vstar<‖z.2‖},‖z.2‖^2 ∂μ)*
        QuadraticTransport.wassersteinTwo ⟨μ.fst,inferInstance⟩ ξ := by
  let A := {z:E×E|vstar<‖z.2‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_snd.norm
  have hD := hμ.fst.sub (positionBrenierMap_memLp μ ξ hμ hξ hac)
  have hf := hμ.snd.indicator hA
  have hb := abs_integral_inner_le_sqrt hf hD
  have hi : (∫ z,⟪A.indicator Prod.snd z,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ)=
      ∫ z in A,⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ := by
    rw [←integral_indicator hA]
    apply integral_congr_ae; filter_upwards with z
    by_cases hz:z∈A <;> simp [hz]
  have hn : (∫ z,‖A.indicator Prod.snd z‖^2 ∂μ)=∫ z in A,‖z.2‖^2 ∂μ := by
    rw [←integral_indicator hA]
    apply integral_congr_ae; filter_upwards with z
    by_cases hz:z∈A <;> simp [hz]
  have hfst : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hd := QuadraticTransport.brenierMap_displacement_cost ⟨μ.fst,inferInstance⟩ ξ hfst hξ hac
  have hmap : (∫ x,‖x-positionBrenierMap μ ξ x‖^2 ∂μ.fst)=
      ∫ z,‖z.1-positionBrenierMap μ ξ z.1‖^2 ∂μ :=
    integral_map measurable_fst.aemeasurable
      ((measurable_id.sub (measurable_positionBrenierMap μ ξ)).norm.pow_const 2).aestronglyMeasurable
  change (∫ x,‖x-positionBrenierMap μ ξ x‖^2 ∂μ.fst)=_ at hd
  rw [hmap] at hd
  change |∫ z,⟪A.indicator Prod.snd z,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ| ≤
    Real.sqrt (∫ z,‖A.indicator Prod.snd z‖^2 ∂μ)*
      Real.sqrt (∫ z,‖z.1-positionBrenierMap μ ξ z.1‖^2 ∂μ) at hb
  rw [hi,hn,hd] at hb
  rw [transportCorrector_speedFlip μ ξ hμ hξ hac vstar,abs_mul]
  norm_num
  unfold QuadraticTransport.wassersteinTwo
  nlinarith

end PersistencePays
#print axioms PersistencePays.transportCorrector_speedFlip_bound
#print axioms PersistencePays.speedFlip_conditional_entropy
