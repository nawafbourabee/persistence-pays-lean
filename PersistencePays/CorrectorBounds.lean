import PersistencePays.GibbsCorrector

/-! Curvature and velocity-entropy bounds for the actual transport corrector. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.transportGap_ge_cost {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    m/2*(QuadraticTransport.cost ⟨μ.fst,inferInstance⟩ a.targetProbability).toReal ≤
      a.transportGap μ := by
  have hac := a.position_absolutelyContinuous μ hK
  have hf : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have ht := QuadraticTransport.brenierMap_memLp ⟨μ.fst,inferInstance⟩ a.targetProbability
    hf a.position_memLp_two hac
  have hi : Integrable (fun x => m/2*‖x-positionBrenierMap μ a.targetProbability x‖^2) μ.fst :=
    (hf.sub ht).integrable_norm_pow'.const_mul (m/2)
  have hc := QuadraticTransport.brenierMap_displacement_cost ⟨μ.fst,inferInstance⟩ a.targetProbability
    hf a.position_memLp_two hac
  change (∫ x, ‖x-positionBrenierMap μ a.targetProbability x‖^2 ∂μ.fst) = _ at hc
  rw [← hc, ← integral_const_mul]
  apply integral_mono hi (a.transportGap_identity μ hμ hK).1
  intro x
  have hb := a.strong_lower_bound x (positionBrenierMap μ a.targetProbability x)
  change m/2*‖x-positionBrenierMap μ a.targetProbability x‖^2 ≤
    U (positionBrenierMap μ a.targetProbability x)-U x+
      ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫
  rw [show x-positionBrenierMap μ a.targetProbability x =
    -(positionBrenierMap μ a.targetProbability x-x) by module, inner_neg_right, norm_neg]
  linarith

theorem A1.corrector_velocity_entropy_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    |a.corrector μ| ≤ Real.sqrt (2*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal) *
      Real.sqrt ((QuadraticTransport.cost ⟨μ.fst,inferInstance⟩ a.targetProbability).toReal) := by
  have hV := a.velocity_entropy_finite μ hK
  have hJ := conditional_mean_entropy μ (hμ.snd.integrable (by norm_num))
  have hJr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hV) hJ
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hJr
  apply (a.corrector_conditional_bound μ hμ hK).trans
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hJr) (Real.sqrt_nonneg _)

end PersistencePays
#print axioms PersistencePays.A1.transportGap_ge_cost
#print axioms PersistencePays.A1.corrector_velocity_entropy_bound
