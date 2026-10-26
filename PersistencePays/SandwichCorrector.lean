import PersistencePays.SandwichEntropy

/-! Actual corrector dissipation and one-step entropy/corrector contraction
for a Gaussian/volume/Gaussian kernel, including the exact square-root curvature
normalization. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance equiv_map_probability (ν : Measure (E×E)) [IsProbabilityMeasure ν]
    (e : (E×E) ≃ᵐ (E×E)) : IsProbabilityMeasure (ν.map e) :=
  Measure.isProbabilityMeasure_map e.measurable.aemeasurable

theorem A1.sandwich_corrector_dissipation {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (e : (E×E) ≃ᵐ (E×E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (r σ h a1 a2 b : ℝ) (hμ : MemLp id 2 μ) (hμe : MemLp e 2 (phaseOUKernel r σ ∘ₘ μ))
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1) (hh : 0 ≤ h) (ha1 : 0 ≤ a1) (hb : 0 ≤ b)
    (hstage : a.corrector ((phaseOUKernel r σ ∘ₘ μ).map e)-a.corrector (phaseOUKernel r σ ∘ₘ μ) ≤
      h*(a1*((conditionalGaussianEntropy (phaseOUKernel r σ ∘ₘ μ) (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy ((phaseOUKernel r σ ∘ₘ μ).map e) (stdGaussian E) 0).toReal)-
        a2*(klDiv (phaseOUKernel r σ ∘ₘ μ).fst (positionGibbs U)).toReal)+h*b) :
    a.corrector (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ) ≤
      r^2*a.corrector μ+h*a1*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy ((phaseOUKernel r σ ∘ₘ μ).map e) (stdGaussian E) 0).toReal)-
        r*h*a2*(klDiv μ.fst (positionGibbs U)).toReal+h*b := by
  let ν := phaseOUKernel r σ ∘ₘ μ
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  have hKν : klDiv ν (phaseGibbs U) ≠ ∞ :=
    ne_top_of_le_ne_top hK (klDiv_step_le _ _ _ (phaseOUKernel_invariant U r σ hn))
  have hνe : MemLp id 2 (ν.map e) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable e.measurable.aemeasurable).mpr hμe
  have hKνe := a.volume_stage_entropy_finite ν e he hν hμe hKν
  have hci := a.corrector_ou μ hμ hK r σ
  have hco := a.corrector_ou (ν.map e) hνe hKνe r σ
  have hV := a.velocity_entropy_finite μ hK
  have hVB := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV)
    (a.lemma_4_2 μ hμ hK r σ hr hσ hn).2.2.1
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at hVB
  have hr1 : r ≤ 1 := by nlinarith [sq_nonneg σ]
  have hr2 : r^2 ≤ 1 := by nlinarith [sq_nonneg σ]
  have hVi : (conditionalGaussianEntropy ν (stdGaussian E) 0).toReal ≤
      (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal :=
    hVB.trans (mul_le_of_le_one_left ENNReal.toReal_nonneg hr2)
  rw [phaseOUKernel_fst,hci] at hstage
  have hstage' := mul_le_mul_of_nonneg_left hstage hr
  have hVn : 0 ≤ (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := ENNReal.toReal_nonneg
  have hWn : 0 ≤ (conditionalGaussianEntropy (ν.map e) (stdGaussian E) 0).toReal := ENNReal.toReal_nonneg
  have hA := mul_le_mul_of_nonneg_left hVi (show 0 ≤ r*h*a1 by positivity)
  have hB := mul_le_mul_of_nonneg_right hr1 (show 0 ≤ h*b by positivity)
  have hD := mul_le_mul_of_nonneg_right hr1
    (show 0 ≤ h*a1*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
      (conditionalGaussianEntropy (ν.map e) (stdGaussian E) 0).toReal) by positivity)
  simp only [gaussianSandwichKernel_comp]
  change a.corrector (phaseOUKernel r σ ∘ₘ ν.map e) ≤ _
  rw [hco]
  change a.corrector (ν.map e)-r*a.corrector μ ≤ _ at hstage
  nlinarith

/-- One-step conclusion of Proposition 4.12 for the actual kernel. The stage
corrector estimate is the only algorithm-specific premise; the OU and Gibbs
entropy/corrector estimates are proved from A1 and actual laws. -/
theorem A1.sandwich_entropy_corrector_step {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (e : (E×E) ≃ᵐ (E×E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (r σ h a1 a2 b θ : ℝ) (hμ : MemLp id 2 μ) (hμe : MemLp e 2 (phaseOUKernel r σ ∘ₘ μ))
    (hK : klDiv μ (phaseGibbs U) ≠ ∞)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1) (hh : 0 ≤ h)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb : 0 ≤ b) (hθ : 0 ≤ θ)
    (hc1 : θ*(Real.sqrt m*h)*a1 ≤ (1-r^2)/4)
    (hc2 : 2*θ*(1-r^2) ≤ r*(Real.sqrt m*h)*a2/2)
    (hc3 : θ*r*(Real.sqrt m*h)*a2/2 ≤ (1-r^2)/4)
    (hstage : a.corrector ((phaseOUKernel r σ ∘ₘ μ).map e)-a.corrector (phaseOUKernel r σ ∘ₘ μ) ≤
      h*(a1*((conditionalGaussianEntropy (phaseOUKernel r σ ∘ₘ μ) (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy ((phaseOUKernel r σ ∘ₘ μ).map e) (stdGaussian E) 0).toReal)-
        a2*(klDiv (phaseOUKernel r σ ∘ₘ μ).fst (positionGibbs U)).toReal)+h*b) :
    let μout := gaussianSandwichKernel e e.measurable r σ ∘ₘ μ
    (klDiv μout (phaseGibbs U)).toReal+θ*Real.sqrt m*a.corrector μout ≤
      (1-θ*r*a2*(Real.sqrt m*h)/(2*(1+θ)))*
        ((klDiv μ (phaseGibbs U)).toReal+θ*Real.sqrt m*a.corrector μ)+
      (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂phaseOUKernel r σ ∘ₘ μ)+θ*Real.sqrt m*h*b := by
  let μout := gaussianSandwichKernel e e.measurable r σ ∘ₘ μ
  have hEnt := a.sandwich_entropy_dissipation μ e he r σ hμ hμe hK hr hσ hn
  have hC := a.sandwich_corrector_dissipation μ e he r σ h a1 a2 b hμ hμe hK hr hσ hn hh ha1 hb hstage
  have hCm := mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg m)
  have hsum := a.phase_entropy_eq_sum μ hK
  have hCompare := (a.entropy_corrector_comparison μ hμ hK θ hθ).2
  have hbound := a.corrector_scaled_entropy_bound μ hμ hK
  have hd : 0 ≤ 1-r^2 := by nlinarith [sq_nonneg σ]
  have hCscaled : Real.sqrt m*a.corrector μout ≤
      r^2*(Real.sqrt m*a.corrector μ)+(Real.sqrt m*h)*a1*
        ((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
          (conditionalGaussianEntropy ((phaseOUKernel r σ ∘ₘ μ).map e) (stdGaussian E) 0).toReal)-
        r*(Real.sqrt m*h)*a2*(klDiv μ.fst (positionGibbs U)).toReal+(Real.sqrt m*h)*b := by
    nlinarith
  rw [hsum] at hEnt hCompare ⊢
  have hs := entropy_corrector_one_step ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hθ hd hr (show 0 ≤ Real.sqrt m*h by positivity) ha2 (by ring) hbound
    (by nlinarith [hCompare]) hEnt hCscaled hc1 hc2 hc3
  convert hs using 1 <;> ring

end PersistencePays
#print axioms PersistencePays.A1.sandwich_entropy_corrector_step
