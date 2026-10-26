import PersistencePays.FiniteEntropyPropagation
import Mathlib.Probability.Moments.Variance

/-! Probability-law second-moment norms and their propagation through kernels. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal

def secondMomentNorm {S : Type*} [MeasurableSpace S] (μ : Measure S) (F : S → ℝ) : ℝ :=
  Real.sqrt (∫ x, (F x)^2 ∂μ)

section General
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
  (F : S → ℝ)

theorem secondMomentNorm_nonneg : 0 ≤ secondMomentNorm μ F := Real.sqrt_nonneg _

theorem integral_le_secondMomentNorm (hF : MemLp F 2 μ) :
    (∫ x, F x ∂μ) ≤ secondMomentNorm μ F := by
  have hv := variance_nonneg F μ
  rw [variance_eq_sub hF] at hv
  simp only [Pi.pow_apply] at hv
  have hs := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (F x)) (μ := μ))
  have hn := secondMomentNorm_nonneg μ F
  unfold secondMomentNorm at hn ⊢
  nlinarith

theorem secondMomentNorm_add_const (hF : MemLp F 2 μ) (b : ℝ) (hb : 0 ≤ b) :
    secondMomentNorm μ (fun x => F x+b) ≤ secondMomentNorm μ F+b := by
  have hi := hF.integrable (by norm_num)
  have he : (fun x => (F x+b)^2) = fun x => (F x)^2+2*b*F x+b^2 := by
    funext x
    ring
  have hlin := hi.const_mul (2*b)
  have hs := hF.integrable_sq
  have hfirst : Integrable (fun x => (F x)^2+2*b*F x) μ := hs.add hlin
  have hm := integral_le_secondMomentNorm μ F hF
  have hsq := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (F x)) (μ := μ))
  have hnonneg := secondMomentNorm_nonneg μ F
  unfold secondMomentNorm at hsq hm hnonneg ⊢
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [he, integral_add hfirst (integrable_const _), integral_add hs hlin,
      integral_const_mul, integral_const, probReal_univ, one_smul]
    nlinarith [mul_le_mul_of_nonneg_left hm hb]

theorem secondMomentNorm_kernel (K : Kernel S S) [IsMarkovKernel K]
    (b : ℝ) (hb : 0 ≤ b) (hF : MemLp F 2 μ) (hout : MemLp F 2 (K ∘ₘ μ))
    (hstep : ∀ x, (∫ y, (F y)^2 ∂K x) ≤ (F x+b)^2) :
    secondMomentNorm (K ∘ₘ μ) F ≤ secondMomentNorm μ F+b := by
  apply le_trans _ (secondMomentNorm_add_const μ F hF b hb)
  unfold secondMomentNorm
  apply Real.sqrt_le_sqrt
  have ho := hout.integrable_sq
  rw [Measure.comp_eq_comp_const_apply] at ho ⊢
  rw [Kernel.integral_comp ho]
  exact integral_mono ho.integral_comp (hF.add (memLp_const b)).integrable_sq hstep

theorem secondMomentNorm_map_le {D : S → S} (hD : Measurable D) (c : ℝ)
    (hc : 0 ≤ c) (hF : MemLp F 2 μ) (hout : MemLp F 2 (μ.map D))
    (hFpos : ∀ x, 0 ≤ F x) (hbound : ∀ x, F (D x) ≤ c*F x) :
    secondMomentNorm (μ.map D) F ≤ c*secondMomentNorm μ F := by
  have ho := hout.integrable_sq
  have hmap := integral_map hD.aemeasurable ho.aestronglyMeasurable
  have hs := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (F x)) (μ := μ))
  unfold secondMomentNorm
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [hmap]
    have hi : Integrable (fun x => (F (D x))^2) μ :=
      (integrable_map_measure ho.aestronglyMeasurable hD.aemeasurable).mp ho
    have hb : (∫ x, (F (D x))^2 ∂μ) ≤ c^2*(∫ x, (F x)^2 ∂μ) := by
      rw [← integral_const_mul]
      apply integral_mono hi (hF.integrable_sq.const_mul (c^2))
      intro x
      simpa only [mul_pow] using pow_le_pow_left₀ (hFpos _) (hbound x) 2
    nlinarith [sq_nonneg c]

end General
end PersistencePays
#print axioms PersistencePays.secondMomentNorm_kernel
#print axioms PersistencePays.secondMomentNorm_map_le
