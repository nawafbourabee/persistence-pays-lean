import PersistencePays.OUEntropyContraction
import PersistencePays.ConditionalEntropy
import PersistencePays.StageKernels

/-! The actual OU half-step contracts conditional velocity entropy, retaining
the position marginal, as required in Lemma 4.2. -/
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem velocityOUKernel_comp_eq (r σ : ℝ) (μ : Measure E) [IsProbabilityMeasure μ] :
    velocityOUKernel r σ ∘ₘ μ = gaussianUpdate r σ μ := by
  unfold velocityOUKernel
  rw [← Measure.map_comp _ _ (by unfold gaussianOU; fun_prop),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  rfl

theorem velocityOUKernel_entropy_contraction (r σ : ℝ)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    klDiv (velocityOUKernel r σ ∘ₘ μ) (stdGaussian E) ≤
      ENNReal.ofReal (r^2) * klDiv μ (stdGaussian E) := by
  have hq1 : r^2 ≤ 1 := by nlinarith [sq_nonneg σ]
  have hh := gaussianChannel_entropy_contraction (sq_nonneg r) hq1 μ
  have hs : sqrt (1-r^2)=σ := by
    rw [show 1-r^2=σ^2 by linarith, sqrt_sq_eq_abs, abs_of_nonneg hσ]
  simpa only [gaussianChannel, sqrt_sq_eq_abs, abs_of_nonneg hr, hs,
    velocityOUKernel_comp_eq] using hh

theorem phaseOUKernel_fst (r σ : ℝ) (μ : Measure (E × E)) [IsProbabilityMeasure μ] :
    (phaseOUKernel r σ ∘ₘ μ).fst = μ.fst := by
  calc
    _ = ((Kernel.id ∥ₖ velocityOUKernel r σ) ∘ₘ (μ.fst ⊗ₘ μ.condKernel)).fst := by
      rw [μ.disintegrate μ.condKernel]
      rfl
    _ = μ.fst := by rw [Measure.parallelComp_comp_compProd, Measure.fst_compProd]

theorem phaseOUKernel_conditional_entropy_contraction (r σ : ℝ)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hn : r^2+σ^2=1)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hD : klDiv μ (μ.fst.prod (stdGaussian E)) ≠ ∞) :
    klDiv (phaseOUKernel r σ ∘ₘ μ)
      ((phaseOUKernel r σ ∘ₘ μ).fst.prod (stdGaussian E)) ≤
        ENNReal.ofReal (r^2) * klDiv μ (μ.fst.prod (stdGaussian E)) := by
  let K := velocityOUKernel (E := E) r σ
  let κ := μ.condKernel
  let η := Kernel.const E (stdGaussian E)
  have hpre : μ.fst ⊗ₘ κ = μ := μ.disintegrate μ.condKernel
  have href : μ.fst ⊗ₘ η = μ.fst.prod (stdGaussian E) := Measure.compProd_const
  have hpost : μ.fst ⊗ₘ (K ∘ₖ κ) = phaseOUKernel r σ ∘ₘ μ := by
    rw [← Measure.parallelComp_comp_compProd, hpre]
    rfl
  have hac : μ ≪ μ.fst.prod (stdGaussian E) := (klDiv_ne_top_iff.mp hD).1
  have hpres : phaseOUKernel r σ ∘ₘ (μ.fst.prod (stdGaussian E)) =
      μ.fst.prod (stdGaussian E) := by
    unfold phaseOUKernel
    rw [← Measure.prod_comp_right, velocityOUKernel_invariant r σ hn]
  have hacPost : phaseOUKernel r σ ∘ₘ μ ≪ μ.fst.prod (stdGaussian E) := by
    rw [← hpres]
    exact hac.comp_right _
  have hiPre := klDiv_compProd_right_integral_of_ac μ.fst κ η (by rwa [hpre, href])
  have hiPost := klDiv_compProd_right_integral_of_ac μ.fst (K ∘ₖ κ) η (by rwa [hpost, href])
  rw [hpre, href] at hiPre
  rw [hpost, href] at hiPost
  rw [phaseOUKernel_fst, hiPre, hiPost]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (r^2) * klDiv (κ x) (η x) ∂μ.fst := by
      apply lintegral_mono
      intro x
      exact velocityOUKernel_entropy_contraction r σ hr hσ hn (κ x)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end
end PersistencePays
#print axioms PersistencePays.phaseOUKernel_conditional_entropy_contraction
