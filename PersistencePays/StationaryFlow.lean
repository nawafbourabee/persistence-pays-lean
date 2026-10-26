import PersistencePays.Conductance
import PersistencePays.StepLaw
import PersistencePays.EpochProbability

/-! Exact stationary accepted-crossing probabilities for Definition 2.2. -/

namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def positionCylinder (A : Set E) : Set ((E × E) × ℝ) := {z | z.1.1 ∈ A}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem positionCylinder_measurable (A : Set E) (hA : MeasurableSet A) :
    MeasurableSet (positionCylinder A) :=
  (measurable_fst.comp measurable_fst) hA

theorem extendedOUKernel_position_set (r σ : ℝ) (z : (E × E) × ℝ)
    (A : Set E) (hA : MeasurableSet A) :
    extendedOUKernel r σ z (positionCylinder A) =
      (positionCylinder A).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  classical
  rw [extendedOUKernel_apply, Measure.map_apply
    (by unfold extendedOU OBABOPath.ou; fun_prop) (positionCylinder_measurable A hA)]
  by_cases hz : z.1.1 ∈ A <;> simp [positionCylinder, extendedOU, OBABOPath.ou, hz]

theorem extendedOU_comp_position_set (r σ : ℝ) (ν : Measure ((E × E) × ℝ))
    (A : Set E) (hA : MeasurableSet A) :
    (extendedOUKernel r σ ∘ₘ ν) (positionCylinder A) = ν (positionCylinder A) := by
  classical
  rw [Measure.bind_apply (positionCylinder_measurable A hA) (Kernel.aemeasurable _)]
  simp_rw [extendedOUKernel_position_set r σ _ A hA]
  change (∫⁻ z, (positionCylinder A).indicator (fun _ => (1 : ℝ≥0∞)) z ∂ν) = _
  rw [lintegral_indicator (positionCylinder_measurable A hA)]
  simp

theorem extendedOU_restricted_target (U : E → ℝ) (r σ : ℝ)
    (hnorm : r ^ 2 + σ ^ 2 = 1) (A : Set E) :
    extendedOUKernel r σ ∘ₘ (extendedTarget U).restrict (positionCylinder A) =
      (extendedTarget U).restrict (positionCylinder A) := by
  have he : positionCylinder A = (A ×ˢ (univ : Set E)) ×ˢ (univ : Set ℝ) := by
    ext z
    simp [positionCylinder]
  rw [he, extendedTarget, phaseGibbs, ← Measure.restrict_prod_eq_prod_univ,
    ← Measure.restrict_prod_eq_prod_univ]
  rw [extendedOUKernel, phaseOUKernel, ← Measure.prod_comp_left,
    ← Measure.prod_comp_right, velocityOUKernel_invariant r σ hnorm]

/-- Removing the OU bookends in the stationary crossing calculation is valid
because they preserve the position event and its restricted Gibbs measure. -/
theorem stationaryFlow_step_eq_adjustedStage (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1)
    (A : Set E) (hA : MeasurableSet A) :
    stationaryFlow (stepKernel U hU g hg h r σ) (extendedTarget U) (positionCylinder A) =
      stationaryFlow (adjustedStageKernel U hU g hg h) (extendedTarget U) (positionCylinder A) := by
  have hAc : (positionCylinder A)ᶜ = positionCylinder Aᶜ := rfl
  unfold stationaryFlow
  rw [← Measure.bind_apply (positionCylinder_measurable A hA).compl (Kernel.aemeasurable _),
    ← Measure.bind_apply (positionCylinder_measurable A hA).compl (Kernel.aemeasurable _)]
  rw [stepKernel, ← Measure.comp_assoc, ← Measure.comp_assoc, hAc,
    extendedOU_comp_position_set r σ _ Aᶜ hA.compl,
    extendedOU_restricted_target U r σ hnorm A]

theorem exponential_acceptance_probability (s : ℝ) :
    (expMeasure 1) (Ioi s) = ENNReal.ofReal (min 1 (Real.exp (-s))) := by
  have hr : (expMeasure 1).real (Ioi s) = Real.exp (-max s 0) := by
    have he : Ioi s = (Iic s)ᶜ := by ext x; simp
    rw [he, measureReal_compl measurableSet_Iic, EpochAcceptance.exponential_rejection_probability]
    simp
  have hm : Real.exp (-max s 0) = min 1 (Real.exp (-s)) := by
    by_cases hs : 0 ≤ s
    · rw [max_eq_left hs, min_eq_right (Real.exp_le_one_iff.mpr (by linarith))]
    · have hs' : s ≤ 0 := le_of_not_ge hs
      rw [max_eq_right hs', neg_zero, Real.exp_zero,
        min_eq_left (Real.one_le_exp_iff.mpr (by linarith))]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact congrArg ENNReal.ofReal (hr.trans hm)

def proposalCrossing (g : E → E) (h : ℝ) (A : Set E) : Set (E × E) :=
  {w | w.1 ∈ A ∧ (verlet g h w).1 ∉ A}

theorem proposalCrossing_measurable (g : E → E) (hg : Measurable g)
    (h : ℝ) (A : Set E) (hA : MeasurableSet A) :
    MeasurableSet (proposalCrossing g h A) :=
  (measurable_fst hA).inter
    ((measurable_fst.comp (verlet_measurePreserving g hg h).measurable) hA).compl

theorem stationaryFlow_adjustedStage (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) (A : Set E) (hA : MeasurableSet A) :
    stationaryFlow (adjustedStageKernel U hU g hg h) (extendedTarget U) (positionCylinder A) =
      ∫⁻ w, (proposalCrossing g h A).indicator
        (fun w => ENNReal.ofReal (min 1
          (Real.exp (-energyIncrement (phaseEnergy U) (verlet g h) w)))) w ∂phaseGibbs U := by
  classical
  let D := adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h)
  let C := proposalCrossing g h A
  let δ := energyIncrement (phaseEnergy U) (verlet g h)
  have hD : Measurable D := (verlet_adjusted_preserves_extendedGibbs U hU g hg h).measurable
  have hδ : Measurable δ :=
    ((phaseEnergy_measurable U hU).comp (verlet_measurePreserving g hg h).measurable).sub
      (phaseEnergy_measurable U hU)
  have hC : MeasurableSet C := proposalCrossing_measurable g hg h A hA
  have he : D ⁻¹' (positionCylinder A)ᶜ ∩ positionCylinder A =
      {z : (E × E) × ℝ | z.1 ∈ C ∧ δ z.1 < z.2} := by
    ext z
    by_cases hz : δ z.1 < z.2
    · simp [D, C, δ, positionCylinder, proposalCrossing, adjustedUpdate,
        hz, Set.mem_inter_iff, and_comm]
    · simp [D, C, δ, positionCylinder, proposalCrossing, adjustedUpdate,
        hz, velocityFlip]
  have hm : MeasurableSet {z : (E × E) × ℝ | z.1 ∈ C ∧ δ z.1 < z.2} :=
    (measurable_fst hC).inter (measurableSet_lt (hδ.comp measurable_fst) measurable_snd)
  unfold stationaryFlow
  rw [← Measure.bind_apply (positionCylinder_measurable A hA).compl (Kernel.aemeasurable _),
    adjustedStageKernel, Measure.deterministic_comp_eq_map,
    Measure.map_apply hD (positionCylinder_measurable A hA).compl,
    Measure.restrict_apply (hD (positionCylinder_measurable A hA).compl), he,
    extendedTarget, Measure.prod_apply hm]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ C
  · have hs : Prod.mk w ⁻¹' {z : (E × E) × ℝ | z.1 ∈ C ∧ δ z.1 < z.2} = Ioi (δ w) := by
      ext l
      simp [hw]
    rw [hs, exponential_acceptance_probability]
    symm
    exact Set.indicator_of_mem hw _
  · have hs : Prod.mk w ⁻¹' {z : (E × E) × ℝ | z.1 ∈ C ∧ δ z.1 < z.2} = ∅ := by
      ext l
      simp [hw]
    rw [hs, measure_empty]
    symm
    exact Set.indicator_of_notMem hw _

/-- The stationary crossing probability of the actual OBABO attempt equals
the Gibbs expectation of accepted Verlet crossings. No independence of the
carried threshold away from stationarity is claimed. -/
theorem stationaryFlow_step (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1)
    (A : Set E) (hA : MeasurableSet A) :
    stationaryFlow (stepKernel U hU g hg h r σ) (extendedTarget U) (positionCylinder A) =
      ∫⁻ w, (proposalCrossing g h A).indicator
        (fun w => ENNReal.ofReal (min 1
          (Real.exp (-energyIncrement (phaseEnergy U) (verlet g h) w)))) w ∂phaseGibbs U := by
  rw [stationaryFlow_step_eq_adjustedStage U hU g hg h r σ hnorm A hA,
    stationaryFlow_adjustedStage U hU g hg h A hA]

/-- Independently refresh the threshold and retain the full phase state. -/
def thresholdRefreshKernel : Kernel ((E × E) × ℝ) ((E × E) × ℝ) :=
  Kernel.id ∥ₖ Kernel.const ℝ (expMeasure 1)

instance thresholdRefreshKernel_markov : IsMarkovKernel (thresholdRefreshKernel (E := E)) := by
  unfold thresholdRefreshKernel
  infer_instance

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem thresholdRefreshKernel_product (ν : Measure (E × E)) [SFinite ν] :
    thresholdRefreshKernel ∘ₘ (ν.prod (expMeasure 1)) = ν.prod (expMeasure 1) := by
  rw [thresholdRefreshKernel, ← Measure.prod_comp_right, Measure.const_comp]
  simp

theorem thresholdRefreshKernel_invariant (U : E → ℝ) :
    thresholdRefreshKernel ∘ₘ extendedTarget U = extendedTarget U :=
  thresholdRefreshKernel_product (phaseGibbs U)

theorem thresholdRefreshKernel_restricted_target (U : E → ℝ) (A : Set E) :
    thresholdRefreshKernel ∘ₘ (extendedTarget U).restrict (positionCylinder A) =
      (extendedTarget U).restrict (positionCylinder A) := by
  have he : positionCylinder A = (A ×ˢ (univ : Set E)) ×ˢ (univ : Set ℝ) := by
    ext z
    simp [positionCylinder]
  rw [he, extendedTarget, ← Measure.restrict_prod_eq_prod_univ]
  exact thresholdRefreshKernel_product _

theorem stationaryFlow_refresh_then_step (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (A : Set E) (hA : MeasurableSet A) :
    stationaryFlow (stepKernel U hU g hg h r σ ∘ₖ thresholdRefreshKernel)
        (extendedTarget U) (positionCylinder A) =
      stationaryFlow (stepKernel U hU g hg h r σ) (extendedTarget U) (positionCylinder A) := by
  unfold stationaryFlow
  rw [← Measure.bind_apply (positionCylinder_measurable A hA).compl (Kernel.aemeasurable _),
    ← Measure.bind_apply (positionCylinder_measurable A hA).compl (Kernel.aemeasurable _),
    ← Measure.comp_assoc, thresholdRefreshKernel_restricted_target U A]

/-- A Boolean schedule refreshes before selected attempts. Constant true is
the fresh-threshold rule; epoch boundaries give the persistent-threshold rule. -/
def scheduledStepKernel (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (refresh : Bool) :
    Kernel ((E × E) × ℝ) ((E × E) × ℝ) :=
  if refresh then stepKernel U hU g hg h r σ ∘ₖ thresholdRefreshKernel
  else stepKernel U hU g hg h r σ

instance scheduledStepKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (refresh : Bool) :
    IsMarkovKernel (scheduledStepKernel U hU g hg h r σ refresh) := by
  cases refresh <;> simp only [scheduledStepKernel, Bool.false_eq_true, ↓reduceIte]
  all_goals infer_instance

theorem scheduledStepKernel_invariant (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) (refresh : Bool) :
    scheduledStepKernel U hU g hg h r σ refresh ∘ₘ extendedTarget U = extendedTarget U := by
  cases refresh <;> simp only [scheduledStepKernel, Bool.false_eq_true, ↓reduceIte]
  · exact stepKernel_invariant U hU hi g hg h r σ hnorm
  · rw [← Measure.comp_assoc, thresholdRefreshKernel_invariant]
    exact stepKernel_invariant U hU hi g hg h r σ hnorm

theorem stationaryFlow_scheduledStep (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1)
    (refresh : Bool) (A : Set E) (hA : MeasurableSet A) :
    stationaryFlow (scheduledStepKernel U hU g hg h r σ refresh)
        (extendedTarget U) (positionCylinder A) =
      ∫⁻ w, (proposalCrossing g h A).indicator
        (fun w => ENNReal.ofReal (min 1
          (Real.exp (-energyIncrement (phaseEnergy U) (verlet g h) w)))) w ∂phaseGibbs U := by
  cases refresh <;> simp only [scheduledStepKernel, Bool.false_eq_true, ↓reduceIte]
  · exact stationaryFlow_step U hU g hg h r σ hnorm A hA
  · rw [stationaryFlow_refresh_then_step U hU g hg h r σ A hA]
    exact stationaryFlow_step U hU g hg h r σ hnorm A hA

theorem extendedTarget_positionCylinder (U : E → ℝ) (A : Set E) :
    extendedTarget U (positionCylinder A) = positionGibbs U A := by
  have he : positionCylinder A = (A ×ˢ (univ : Set E)) ×ˢ (univ : Set ℝ) := by
    ext z
    simp [positionCylinder]
  simp [extendedTarget, phaseGibbs, he, Measure.prod_prod]

theorem extendedTarget_map_position (U : E → ℝ) :
    (extendedTarget U).map (fun z => z.1.1) = positionGibbs U := by
  ext A hA
  rw [Measure.map_apply
    (by fun_prop : Measurable (fun z : (E × E) × ℝ => z.1.1)) hA]
  exact extendedTarget_positionCylinder U A

/-- The full Appendix B stationary-crossing reduction for any deterministic
refresh schedule, with the actual implemented attempted-step kernels. -/
theorem scheduled_half_conditioned_TV_gt_quarter
    (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1)
    (refresh : ℕ → Bool) (A : Set E) (hA : MeasurableSet A)
    (hhalf : positionGibbs U A = (1 / 2 : ℝ≥0∞))
    (q : ℝ≥0∞)
    (hq : (∫⁻ w, (proposalCrossing g h A).indicator
        (fun w => ENNReal.ofReal (min 1
          (Real.exp (-energyIncrement (phaseEnergy U) (verlet g h) w)))) w ∂phaseGibbs U) ≤ q)
    (n : ℕ) (hn : (n : ℝ≥0∞) * 2 * q < 1 / 4) :
    (1 / 4 : ℝ≥0∞) < probabilityTV
      ((evolve (fun j => scheduledStepKernel U hU g hg h r σ (refresh j))
        ((2 : ℝ≥0∞) • (extendedTarget U).restrict (positionCylinder A)) n).map (fun z => z.1.1))
      (positionGibbs U) := by
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hi
  let : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  let : IsProbabilityMeasure (extendedTarget U) := by unfold extendedTarget; infer_instance
  rw [← extendedTarget_map_position U]
  apply half_conditioned_observation_TV_gt_quarter
    (fun j => scheduledStepKernel U hU g hg h r σ (refresh j)) (extendedTarget U)
    (fun j => scheduledStepKernel_invariant U hU hi g hg h r σ hnorm (refresh j))
    (fun z => z.1.1) (measurable_fst.comp measurable_fst) A hA
    (by change extendedTarget U (positionCylinder A) = _
        rw [extendedTarget_positionCylinder]
        exact hhalf) q
    (fun j => ?_) n hn
  change stationaryFlow _ _ (positionCylinder A) ≤ q
  rw [stationaryFlow_scheduledStep U hU g hg h r σ hnorm (refresh j) A hA]
  exact hq

end
end PersistencePays

#print axioms PersistencePays.stationaryFlow_step_eq_adjustedStage
#print axioms PersistencePays.exponential_acceptance_probability
#print axioms PersistencePays.stationaryFlow_step
#print axioms PersistencePays.stationaryFlow_scheduledStep
#print axioms PersistencePays.scheduled_half_conditioned_TV_gt_quarter
