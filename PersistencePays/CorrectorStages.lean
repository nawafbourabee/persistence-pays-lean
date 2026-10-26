import PersistencePays.Corrector
import PersistencePays.ConditionalOU

/-! Exact OU and force-kick identities for the actual Brenier corrector. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_inner_mean (b : E) : (∫ x : E, ⟪x,b⟫ ∂stdGaussian E) = 0 := by
  calc
    _ = ∫ x : E, ⟪b,x⟫ ∂stdGaussian E := integral_congr_ae
      (Filter.Eventually.of_forall (fun x => real_inner_comm b x))
    _ = 0 := by
      simpa only [innerSL_apply_apply] using integral_strongDual_stdGaussian (innerSL ℝ b)

theorem transportCorrector_ou (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume) (r σ : ℝ) :
    transportCorrector (phaseOUKernel r σ ∘ₘ μ) ξ = r*transportCorrector μ ξ := by
  have hT := measurable_positionBrenierMap μ ξ
  have hD := hμ.fst.sub (positionBrenierMap_memLp μ ξ hμ hξ hac)
  have hnoise : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hi : Integrable (fun p : (E × E) × E =>
      ⟪r•p.1.2+σ•p.2,p.1.1-positionBrenierMap μ ξ p.1.1⟫) (μ.prod (stdGaussian E)) :=
    integrable_inner_of_memLp_two
      (((hμ.snd.comp_fst (stdGaussian E)).const_smul r).add
        ((hnoise.comp_snd μ).const_smul σ)) (hD.comp_fst (stdGaussian E))
  have hc : Measurable (fun z : E × E => ⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫) :=
    measurable_snd.inner (measurable_fst.sub (hT.comp measurable_fst))
  unfold transportCorrector
  rw [positionBrenierMap_congr _ μ ξ (phaseOUKernel_fst r σ μ), phaseOUKernel_comp_map,
    integral_map (by unfold OBABOPath.ou; fun_prop)
      hc.aestronglyMeasurable]
  change (∫ p : (E × E) × E,
    ⟪r•p.1.2+σ•p.2,p.1.1-positionBrenierMap μ ξ p.1.1⟫ ∂μ.prod (stdGaussian E)) = _
  rw [integral_prod _ hi]
  have he (z : E × E) :
      (∫ η : E, ⟪r•z.2+σ•η,z.1-positionBrenierMap μ ξ z.1⟫ ∂stdGaussian E) =
      r*⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫ := by
    simp_rw [inner_add_left, real_inner_smul_left]
    have hη : Integrable (fun η : E => σ*⟪η,z.1-positionBrenierMap μ ξ z.1⟫) (stdGaussian E) :=
      (IsGaussian.integrable_id.inner_const _).const_mul σ
    rw [integral_add (integrable_const _) hη]
    simp only [integral_const_mul, stdGaussian_inner_mean, integral_const, probReal_univ, one_smul]
    ring
  simp_rw [he]
  rw [integral_const_mul]

instance kickEquiv_map_probability (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (g : E → E) (hg : Measurable g) (s : ℝ) :
    IsProbabilityMeasure (μ.map (kickEquiv g hg s)) :=
  Measure.isProbabilityMeasure_map (kickEquiv g hg s).measurable.aemeasurable

theorem transportCorrector_kick (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ)
    (hξ : MemLp id 2 (ξ : Measure E)) (hac : μ.fst ≪ volume)
    (g : E → E) (hg : Measurable g) (hg2 : MemLp (fun z : E × E => g z.1) 2 μ) (s : ℝ) :
    transportCorrector (μ.map (kickEquiv g hg s)) ξ = transportCorrector μ ξ -
      s*(∫ x, ⟪g x,x-positionBrenierMap μ ξ x⟫ ∂μ.fst) := by
  have hT := measurable_positionBrenierMap μ ξ
  have hD := hμ.fst.sub (positionBrenierMap_memLp μ ξ hμ hξ hac)
  have hgD : Integrable (fun z : E × E => ⟪g z.1,z.1-positionBrenierMap μ ξ z.1⟫) μ :=
    integrable_inner_of_memLp_two hg2 hD
  have hm : Measurable (fun x => ⟪g x,x-positionBrenierMap μ ξ x⟫) :=
    hg.inner (measurable_id.sub hT)
  have hp := map_position_preserving_fst μ (kickEquiv g hg s) (fun _ => rfl)
  have hc : Measurable (fun z : E × E => ⟪z.2,z.1-positionBrenierMap μ ξ z.1⟫) :=
    measurable_snd.inner (measurable_fst.sub (hT.comp measurable_fst))
  unfold transportCorrector
  rw [positionBrenierMap_congr _ μ ξ hp,
    integral_map (kickEquiv g hg s).measurable.aemeasurable
      hc.aestronglyMeasurable]
  change (∫ z, ⟪z.2-s•g z.1,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ) = _
  simp_rw [inner_sub_left, real_inner_smul_left]
  have he : (∫ x, ⟪g x,x-positionBrenierMap μ ξ x⟫ ∂μ.fst) =
      ∫ z : E × E, ⟪g z.1,z.1-positionBrenierMap μ ξ z.1⟫ ∂μ :=
    integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable
  rw [integral_sub (transportCorrector_integrable μ ξ hμ hξ hac) (hgD.const_mul s),
    integral_const_mul, he]

end PersistencePays
#print axioms PersistencePays.transportCorrector_ou
#print axioms PersistencePays.transportCorrector_kick
