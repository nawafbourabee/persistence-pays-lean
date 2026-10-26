import PersistencePays.CorrectorStages
import PersistencePays.CorrectorConditional
import PersistencePays.TransportEntropyBalance

/-! The actual Gibbs-target corrector, convexity gap, and Lemma 4.3. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def A1.targetProbability {U : E → ℝ} {m L : ℝ} (a : A1 U m L) : ProbabilityMeasure E :=
  ⟨positionGibbs U,a.gibbs_isProbabilityMeasure⟩

def A1.corrector {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] : ℝ :=
  transportCorrector μ a.targetProbability

def A1.transportGap {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] : ℝ :=
  ∫ x, U (positionBrenierMap μ a.targetProbability x)-U x+
    ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst

theorem A1.position_absolutelyContinuous {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) : μ.fst ≪ volume :=
  (klDiv_ne_top_iff.mp (a.position_entropy_finite μ hK)).1.trans
    (tilted_absolutelyContinuous volume (-U))

theorem A1.corrector_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    Integrable (fun z => ⟪z.2,z.1-positionBrenierMap μ a.targetProbability z.1⟫) μ :=
  transportCorrector_integrable μ a.targetProbability hμ a.position_memLp_two
    (a.position_absolutelyContinuous μ hK)

theorem A1.transportGap_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    Integrable (fun x => U (positionBrenierMap μ a.targetProbability x)-U x+
      ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫) μ.fst ∧
    0 ≤ a.transportGap μ ∧
    (∫ x, ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst) =
      a.transportGap μ+(klDiv μ.fst (positionGibbs U)).toReal-
        (boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hac := a.position_absolutelyContinuous μ hK
  have hf : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have ht := QuadraticTransport.brenierMap_memLp ⟨μ.fst,inferInstance⟩ a.targetProbability
    hf a.position_memLp_two hac
  have hs := QuadraticTransport.brenierMap_spec ⟨μ.fst,inferInstance⟩ a.targetProbability
    hf a.position_memLp_two hac
  have hU : Integrable U μ.fst := a.potential_integrable hf
  have hUT : Integrable (fun x => U (positionBrenierMap μ a.targetProbability x)) μ.fst :=
    a.potential_integrable ht
  have hinner : Integrable (fun x => ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫) μ.fst :=
    integrable_inner_of_memLp_two (a.gradient_memLp hf) (hf.sub ht)
  have hi := (hUT.sub hU).add hinner
  refine ⟨hi,?_,?_⟩
  · apply integral_nonneg
    intro x
    have hb := a.strong_lower_bound x (positionBrenierMap μ a.targetProbability x)
    have hn := mul_nonneg (div_nonneg a.m_pos.le (show 0 ≤ (2 : ℝ) by norm_num))
      (sq_nonneg ‖positionBrenierMap μ a.targetProbability x-x‖)
    change 0 ≤ U (positionBrenierMap μ a.targetProbability x)-U x+
      ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫
    rw [show x-positionBrenierMap μ a.targetProbability x =
      -(positionBrenierMap μ a.targetProbability x-x) by module, inner_neg_right]
    linarith
  · have hmap : (∫ x, U (positionBrenierMap μ a.targetProbability x) ∂μ.fst) =
        ∫ x, U x ∂positionGibbs U := by
      have hpush : μ.fst.map (positionBrenierMap μ a.targetProbability) = positionGibbs U := hs.2.1
      rw [← hpush]
      exact (integral_map (μ := μ.fst) (measurable_positionBrenierMap μ a.targetProbability).aemeasurable
        a.twice_contDiff.continuous.measurable.aestronglyMeasurable).symm
    have hUs : Integrable (fun x => U (positionBrenierMap μ a.targetProbability x)-U x) μ.fst :=
      hUT.sub hU
    have hgap : a.transportGap μ = (∫ x, U x ∂positionGibbs U)-
        (∫ x, U x ∂μ.fst)+(∫ x, ⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst) := by
      unfold A1.transportGap
      rw [integral_add hUs hinner, integral_sub hUT hU, hmap]
    have hsL := (gibbs_boltzmann_identity U a.gibbs_integrable μ.fst hU
      (a.position_entropy_finite μ hK)).2
    have htL := (gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
      (a.potential_integrable a.position_memLp_two) (by simp)).2
    simp only [klDiv_self, ENNReal.toReal_zero, zero_sub] at htL
    linarith

/-- The exact force-kick identity of Lemma 4.3, with all maps and functionals actual. -/
theorem A1.lemma_4_3 {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) (s : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    a.corrector (μ.map (kickEquiv (gradient U) hg s)) = a.corrector μ-
      s*(a.transportGap μ+(klDiv μ.fst (positionGibbs U)).toReal-
        (boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U))) := by
  dsimp only
  rw [A1.corrector, transportCorrector_kick μ a.targetProbability hμ a.position_memLp_two
    (a.position_absolutelyContinuous μ hK) (gradient U)
    (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    (a.gradient_memLp hμ.fst) s, (a.transportGap_identity μ hμ hK).2.2]
  rfl

/-- The corrector part of Lemma 4.2, with arbitrary OU coefficients. -/
theorem A1.corrector_ou {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) (r σ : ℝ) :
    a.corrector (phaseOUKernel r σ ∘ₘ μ) = r*a.corrector μ :=
  transportCorrector_ou μ a.targetProbability hμ a.position_memLp_two
    (a.position_absolutelyContinuous μ hK) r σ

/-- All assertions of Lemma 4.2 for the actual Gaussian OU transition. -/
theorem A1.lemma_4_2 {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hnorm : r^2+σ^2=1) :
    (phaseOUKernel r σ ∘ₘ μ).fst = μ.fst ∧
    klDiv (phaseOUKernel r σ ∘ₘ μ).fst (positionGibbs U) = klDiv μ.fst (positionGibbs U) ∧
    conditionalGaussianEntropy (phaseOUKernel r σ ∘ₘ μ) (stdGaussian E) 0 ≤
      ENNReal.ofReal (r^2)*conditionalGaussianEntropy μ (stdGaussian E) 0 ∧
    a.corrector (phaseOUKernel r σ ∘ₘ μ) = r*a.corrector μ := by
  refine ⟨phaseOUKernel_fst r σ μ,?_,?_,a.corrector_ou μ hμ hK r σ⟩
  · rw [phaseOUKernel_fst]
  · have hV := a.velocity_entropy_finite μ hK
    have hV' : klDiv μ (μ.fst.prod (stdGaussian E)) ≠ ∞ := by
      simpa only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero] using hV
    simpa only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero] using
      phaseOUKernel_conditional_entropy_contraction r σ hr hσ hnorm μ hV'

/-- The Cauchy–Schwarz assertion in Lemma 4.1(S3), with the genuine J and W₂ cost. -/
theorem A1.corrector_conditional_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    |a.corrector μ| ≤ Real.sqrt (conditionalMeanSquare μ).toReal *
      Real.sqrt ((QuadraticTransport.cost ⟨μ.fst,inferInstance⟩ a.targetProbability).toReal) :=
  transportCorrector_conditional_bound μ a.targetProbability hμ a.position_memLp_two
    (a.position_absolutelyContinuous μ hK) (a.velocity_entropy_finite μ hK)

end PersistencePays
#print axioms PersistencePays.A1.lemma_4_3
#print axioms PersistencePays.A1.corrector_ou

#print axioms PersistencePays.A1.lemma_4_2
#print axioms PersistencePays.A1.corrector_conditional_bound
