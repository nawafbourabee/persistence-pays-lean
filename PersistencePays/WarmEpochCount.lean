import PersistencePays.WarmTailParameters

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal

def samplingEpochs (ε:ℝ) : ℕ := ⌈Real.log (2/ε)/Real.log 4⌉₊

theorem samplingEpochs_pos {ε:ℝ} (hε:0<ε) (hε1:ε≤1) : 0<samplingEpochs ε := by
  apply Nat.ceil_pos.mpr
  apply div_pos _ (Real.log_pos (by norm_num))
  exact Real.log_pos ((one_lt_div hε).mpr (by linarith))

theorem samplingEpochs_quarter_power {ε:ℝ} (hε:0<ε) (hε1:ε≤1) :
    (1/4:ℝ≥0∞)^samplingEpochs ε≤ENNReal.ofReal (ε/2) := by
  have hlog:0<Real.log 4 := Real.log_pos (by norm_num)
  have hceil:Real.log (2/ε)≤(samplingEpochs ε:ℝ)*Real.log 4 :=
    (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have hreal:(1/4:ℝ)^samplingEpochs ε≤ε/2 := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
    have hl:Real.log (1/4:ℝ) = -Real.log 4 := by rw [one_div,Real.log_inv]
    rw [hl]
    have ht:=Real.exp_le_exp.mpr (show -Real.log 4*(samplingEpochs ε:ℝ)≤ -Real.log (2/ε) by nlinarith)
    rw [Real.exp_neg,Real.exp_log (by positivity)] at ht
    have he:(2/ε)⁻¹=ε/2 := by field_simp
    rwa [he] at ht
  rw [show (1/4:ℝ≥0∞)=ENNReal.ofReal (1/4:ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,←ENNReal.ofReal_pow (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem samplingEpochs_bound {ε:ℝ} (hε:0<ε) (hε1:ε≤1) :
    (samplingEpochs ε:ℝ)≤3*Real.log (2/ε)/Real.log 4 := by
  have hlog:0<Real.log 4 := Real.log_pos (by norm_num)
  have harg:2≤2/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hl:Real.log 2≤Real.log (2/ε) := Real.log_le_log (by norm_num) harg
  have hlogid:Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hpos:0≤Real.log (2/ε)/Real.log 4 := by positivity [Real.log_pos (by linarith :1<2/ε)]
  have hc := (Nat.ceil_lt_add_one hpos).le
  change (samplingEpochs ε:ℝ)≤Real.log (2/ε)/Real.log 4+1 at hc
  apply hc.trans
  apply (le_div_iff₀ hlog).mpr
  have he:(Real.log (2/ε)/Real.log 4+1)*Real.log 4=Real.log (2/ε)+Real.log 4 := by field_simp
  rw [he,hlogid]
  nlinarith

end PersistencePays
#print axioms PersistencePays.samplingEpochs_quarter_power
#print axioms PersistencePays.samplingEpochs_bound
