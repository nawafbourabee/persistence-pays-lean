import PersistencePays.ComparisonChainBounds
import PersistencePays.DensityCapPropagation
import PersistencePays.OUScalarBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A genuine measurable density cap and its explicit logarithm for the actual
comparison law. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def comparisonDensityCap (d N:ℕ) (h σ:ℝ) : ℝ :=
  ((2*Real.pi*h*σ^2)^d)⁻¹*Real.exp (2*(d:ℝ)*((N:ℝ)*h))

theorem comparisonDensityCap_pos {h σ:ℝ} (hh:0<h) (hσ:0<σ) (d N:ℕ) :
    0<comparisonDensityCap d N h σ := by unfold comparisonDensityCap; positivity

theorem comparisonDensityCap_log {h σ:ℝ} (hh:0<h) (hσ:0<σ) (d N:ℕ) :
    Real.log (comparisonDensityCap d N h σ)+(d:ℝ)*Real.log (2*Real.pi) =
      (d:ℝ)*Real.log (1/(h*σ^2))+2*(d:ℝ)*((N:ℝ)*h) := by
  have ha:0<2*Real.pi*h*σ^2 := by positivity
  have hb:0<h*σ^2 := by positivity
  unfold comparisonDensityCap
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_inv,Real.log_pow,Real.log_exp]
  have he:2*Real.pi*h*σ^2=(2*Real.pi)*(h*σ^2) := by ring
  rw [he,Real.log_mul (by positivity) hb.ne',Real.log_div one_ne_zero hb.ne',Real.log_one]
  ring

theorem comparisonDensityCap_logPlus_bound {h:ℝ} (hh:0<h) (hmax:h≤1/8) (d N:ℕ) :
    let σ := Real.sqrt (1-Real.exp (-2*h))
    max (Real.log (comparisonDensityCap d N h σ)) 0+(d:ℝ)*Real.log (2*Real.pi) ≤
      (d:ℝ)*Real.log (1/h^2)+2*(d:ℝ)*((N:ℝ)*h) := by
  dsimp only
  let σ := Real.sqrt (1-Real.exp (-2*h))
  have hslo := (normalized_ou_coefficients h hh.le).2.2.2.2.2.2.1
  change 2*h*(1-h)≤σ^2 at hslo
  have hsq: h≤σ^2 := by nlinarith
  have hσ:0<σ := by
    have hn:0≤σ := Real.sqrt_nonneg _
    nlinarith
  have hσh:h^2≤h*σ^2 := by nlinarith
  have hbpos:0<h*σ^2 := by positivity
  have hlo : Real.log (1/(h*σ^2))≤Real.log (1/h^2) := by
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le (by positivity) hσh
  have hpi : 2*Real.pi≤1/h^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    have hp:=Real.pi_lt_four
    have hhsq:h^2≤1/64 := by nlinarith
    nlinarith [Real.pi_pos]
  have hlpi:=Real.log_le_log (by positivity :0<2*Real.pi) hpi
  have hd:0≤(d:ℝ) := by positivity
  rw [←max_add_add_right]
  apply max_le
  · rw [comparisonDensityCap_log hh hσ]
    exact add_le_add (mul_le_mul_of_nonneg_left hlo hd) le_rfl
  · simp only [zero_add]
    have ht:=mul_le_mul_of_nonneg_left hlpi hd
    have hn:0≤2*(d:ℝ)*((N:ℝ)*h) := by positivity
    linarith

/-- The log-cap inequality and an everywhere bounded measurable density for
precisely the actual law used by Section 6. -/
theorem comparison_pre_density_with_log (g:E→E) (hg:Measurable g)
    (h vstar:ℝ) (hh:0<h) (hmax:h≤1/8) (z:E×E) (n N:ℕ) (hn:n+1≤N) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let μ := phaseOUKernel r σ ∘ₘ OBABOPath.comparisonChainLaw g hg h r σ vstar n z
    let C := comparisonDensityCap (Module.finrank ℝ E) N h σ
    0<C ∧ (∃f:E×E→ℝ≥0∞, Measurable f ∧ μ=((volume:Measure E).prod volume).withDensity f ∧
      ∀w,f w≤ENNReal.ofReal C) ∧
    max (Real.log C) 0+(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi) ≤
      (Module.finrank ℝ E:ℝ)*Real.log (1/h^2)+2*(Module.finrank ℝ E:ℝ)*((N:ℝ)*h) := by
  dsimp only
  have hslo := (normalized_ou_coefficients h hh.le).2.2.2.2.2.2.1
  have hσ:0<Real.sqrt (1-Real.exp (-2*h)) := by
    have hn:=Real.sqrt_nonneg (1-Real.exp (-2*h))
    nlinarith
  refine ⟨comparisonDensityCap_pos hh hσ _ _,?_,comparisonDensityCap_logPlus_bound hh hmax _ _⟩
  exact lemma_5_11_density g hg h _ vstar hh hσ z n N hn

end PersistencePays
#print axioms PersistencePays.comparison_pre_density_with_log
