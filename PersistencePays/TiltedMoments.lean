import PersistencePays.LatentBayes
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Bounded-above exponential tilting preserves all existing Lp moments. -/
open MeasureTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {Z F:Type*} [MeasurableSpace Z] [NormedAddCommGroup F]

theorem memLp_tilted_of_upper (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:Z→ℝ} (hi:Integrable (fun z => Real.exp (ψ z)) μ)
    {B:ℝ} (hb:∀ z,ψ z≤B) {f:Z→F} {p:ℝ≥0∞} (hf:MemLp f p μ) :
    MemLp f p (μ.tilted ψ) := by
  have hZ:0<∫ z,Real.exp (ψ z) ∂μ := integral_exp_pos hi
  apply MemLp.of_measure_le_smul (c:=ENNReal.ofReal (Real.exp B/(∫ z,Real.exp (ψ z) ∂μ)))
    ENNReal.ofReal_ne_top _ hf
  rw [Measure.tilted,← withDensity_const]
  apply withDensity_mono
  filter_upwards with z
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (hb z)) hZ.le)

end
end PersistencePays
#print axioms PersistencePays.memLp_tilted_of_upper
