import PersistencePays.CorrectorBounds
import PersistencePays.Talagrand

/-! The exact entropy comparison for the genuine transport corrector, using
the proved Talagrand theorem and conditional Gaussian mean bound. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.corrector_scaled_entropy_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    |Real.sqrt m*a.corrector μ| ≤ 2*Real.sqrt
      ((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal*(klDiv μ.fst (positionGibbs U)).toReal) := by
  let X := (klDiv μ.fst (positionGibbs U)).toReal
  let V := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hc := a.corrector_velocity_entropy_bound μ hμ hK
  have ht := a.talagrand_cost (⟨μ.fst,inferInstance⟩ : ProbabilityMeasure E) (a.position_entropy_finite μ hK)
  change (QuadraticTransport.cost ⟨μ.fst,inferInstance⟩ a.targetProbability).toReal ≤ 2/m*X at ht
  have hc' : |a.corrector μ| ≤ Real.sqrt (2*V)*Real.sqrt (2/m*X) :=
    hc.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht) (Real.sqrt_nonneg _))
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hc'
  rw [sq_abs,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity [a.m_pos])] at hs
  have hm := mul_le_mul_of_nonneg_left hs a.m_pos.le
  have he : m*((2*V)*(2/m*X)) = 4*V*X := by field_simp [a.m_pos.ne']; ring
  rw [he] at hm
  have hsq : (Real.sqrt m)^2=m := Real.sq_sqrt a.m_pos.le
  have hprod := Real.sq_sqrt (mul_nonneg hV hX)
  change |Real.sqrt m*a.corrector μ| ≤ 2*Real.sqrt (V*X)
  have hb : |Real.sqrt m*a.corrector μ|^2 ≤ (2*Real.sqrt (V*X))^2 := by
    rw [sq_abs,mul_pow,hsq]
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hb

theorem A1.corrector_scaled_total_entropy_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    |Real.sqrt m*a.corrector μ| ≤ (klDiv μ (phaseGibbs U)).toReal := by
  have hc := a.corrector_scaled_entropy_bound μ hμ hK
  have he := a.phase_entropy_eq_sum μ hK
  have hX : 0 ≤ (klDiv μ.fst (positionGibbs U)).toReal := ENNReal.toReal_nonneg
  have hV : 0 ≤ (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := ENNReal.toReal_nonneg
  have hs := Real.sq_sqrt (mul_nonneg hV hX)
  have hn := sq_nonneg ((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
    (klDiv μ.fst (positionGibbs U)).toReal)
  have hb : 2*Real.sqrt ((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal*
      (klDiv μ.fst (positionGibbs U)).toReal) ≤
      (klDiv μ.fst (positionGibbs U)).toReal+(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := by
    nlinarith [Real.sqrt_nonneg ((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal*
      (klDiv μ.fst (positionGibbs U)).toReal)]
  linarith

theorem A1.entropy_corrector_comparison {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) (θ : ℝ) (hθ : 0 ≤ θ) :
    (1-θ)*(klDiv μ (phaseGibbs U)).toReal ≤
      (klDiv μ (phaseGibbs U)).toReal+θ*Real.sqrt m*a.corrector μ ∧
    (klDiv μ (phaseGibbs U)).toReal+θ*Real.sqrt m*a.corrector μ ≤
      (1+θ)*(klDiv μ (phaseGibbs U)).toReal := by
  have hb := a.corrector_scaled_total_entropy_bound μ hμ hK
  have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hb).1 hθ
  have h₂ := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 hθ
  constructor <;> nlinarith

end PersistencePays
#print axioms PersistencePays.A1.corrector_scaled_total_entropy_bound
#print axioms PersistencePays.A1.entropy_corrector_comparison
