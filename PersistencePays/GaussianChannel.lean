import PersistencePays.GaussianUpdateSemigroup

/-! Parametrize the OU channel by its squared correlation, which makes the
entropy contraction coefficient and semigroup multiplication explicit. -/
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianChannel (q : ℝ) (μ : Measure E) : Measure E :=
  gaussianUpdate (sqrt q) (sqrt (1-q)) μ

instance gaussianChannel_probability (q : ℝ) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaussianChannel q μ) := gaussianUpdate_probability _ _ _

lemma gaussianChannel_normalized {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (sqrt q)^2+(sqrt (1-q))^2=1 := by rw [sq_sqrt hq, sq_sqrt (by linarith)]; ring

lemma gaussianChannel_one (μ : Measure E) [IsProbabilityMeasure μ] : gaussianChannel 1 μ = μ := by
  apply Measure.ext_of_charFun
  funext t
  rw [gaussianChannel, charFun_gaussianUpdate]
  simp

lemma gaussianChannel_zero (μ : Measure E) [IsProbabilityMeasure μ] :
    gaussianChannel 0 μ = stdGaussian E := by
  apply Measure.ext_of_charFun
  funext t
  rw [gaussianChannel, charFun_gaussianUpdate, charFun_stdGaussian]
  simp

theorem gaussianChannel_comp {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (μ : Measure E) [IsProbabilityMeasure μ] :
    gaussianChannel q (gaussianChannel p μ) = gaussianChannel (q*p) μ := by
  unfold gaussianChannel
  rw [sqrt_mul hq p]
  apply gaussianUpdate_comp
  have hqp : 0 ≤ 1-q*p := by nlinarith [mul_nonneg hp hq]
  rw [sq_sqrt hqp, sq_sqrt hq, sq_sqrt (by linarith : 0 ≤ 1-p),
    sq_sqrt (by linarith : 0 ≤ 1-q)]
  ring

theorem gaussianChannel_entropy_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    klDiv (gaussianChannel q μ) (stdGaussian E) ≤ klDiv μ (stdGaussian E) :=
  gaussianUpdate_entropy_le _ _ (gaussianChannel_normalized hq hq1) μ

theorem gaussianChannel_entropy_mono {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p)
    (hp1 : p ≤ 1) (μ : Measure E) [IsProbabilityMeasure μ] :
    klDiv (gaussianChannel q μ) (stdGaussian E) ≤
      klDiv (gaussianChannel p μ) (stdGaussian E) := by
  by_cases hp : p=0
  · have : q=0 := by linarith
    subst p; subst q; rfl
  have hp0 : 0 < p := lt_of_le_of_ne (by linarith) (Ne.symm hp)
  have hc0 : 0 ≤ q/p := div_nonneg hq hp0.le
  have hc1 : q/p ≤ 1 := (div_le_one hp0).2 hqp
  have hc := gaussianChannel_comp hp0.le hp1 hc0 hc1 μ
  rw [div_mul_cancel₀ _ hp] at hc
  rw [← hc]
  exact gaussianChannel_entropy_le hc0 hc1 _

end
end PersistencePays
#print axioms PersistencePays.gaussianChannel_comp
#print axioms PersistencePays.gaussianChannel_entropy_mono
