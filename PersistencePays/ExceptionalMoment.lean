import PersistencePays.SecondMomentKernel

/-! Small-event second-moment estimates used for the actual comparison path. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped ENNReal

theorem setIntegral_le_secondMomentNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : MemLp F 2 μ)
    (hF0 : ∀ x, 0 ≤ F x) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ x in A, F x ∂μ) ≤ secondMomentNorm μ F * Real.sqrt (μ.real A) := by
  let I : Ω → ℝ := A.indicator (fun _ => 1)
  have hI : MemLp I 2 μ := (memLp_const (1:ℝ)).indicator hA
  have hI0 : ∀ x, 0 ≤ I x := by intro x; exact indicator_nonneg (fun _ _ => by norm_num) x
  have hprod := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hI0)
      (by simpa using hF) (by simpa using hI)
  have he : (fun x => F x*I x) = A.indicator F := by
    funext x
    by_cases hx : x ∈ A <;> simp [I,hx]
  have he₂ : (fun x => I x ^ (2:ℝ)) = I := by
    funext x
    by_cases hx : x ∈ A <;> simp [I,hx]
  rw [he, integral_indicator hA, he₂] at hprod
  have hIi : (∫ x, I x ∂μ) = μ.real A := by
    dsimp only [I]
    rw [integral_indicator hA, setIntegral_const]
    simp
  rw [hIi] at hprod
  simpa only [secondMomentNorm, Real.rpow_two, one_div, Real.sqrt_eq_rpow] using hprod

theorem exceptional_event_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G R : Ω → ℝ)
    (hF : Measurable F) (hG : MemLp G 2 μ) (hF0 : ∀ x, 0 ≤ F x)
    (hG0 : ∀ x, 0 ≤ G x) (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ x, F x ≤ c*G x)
    (A : Set Ω) (hA : MeasurableSet A) (hagree : ∀ x ∈ A, F x=R x) :
    (∫ x, F x ∂μ) ≤ (∫ x in A, R x ∂μ) +
      c * secondMomentNorm μ G * Real.sqrt (μ.real Aᶜ) := by
  have hFi : Integrable F μ := ((hG.integrable (by norm_num)).const_mul c).mono'
    hF.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x)] using hbound x)
  rw [← integral_add_compl hA hFi]
  apply add_le_add
  · exact le_of_eq (setIntegral_congr_fun hA hagree)
  · calc
      _ ≤ ∫ x in Aᶜ, c*G x ∂μ := integral_mono hFi.integrableOn
        ((hG.integrable (by norm_num)).const_mul c).integrableOn hbound
      _ = c * ∫ x in Aᶜ, G x ∂μ := integral_const_mul c G
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left (setIntegral_le_secondMomentNorm μ G hG hG0 Aᶜ hA.compl) hc
        simpa only [mul_assoc] using hb

end PersistencePays
#print axioms PersistencePays.exceptional_event_expectation
