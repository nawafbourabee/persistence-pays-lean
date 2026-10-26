import PersistencePays.Proposition53
import PersistencePays.GibbsTail

/-! Warm-start radius and epoch count: exact scalar conversion of the proved
localized coupling estimate to a sampling guarantee. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {S:Type*} [MeasurableSpace S]

theorem one_le_warmL2 (ν π:Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    (hac:ν≪π) : 1 ≤ warmL2 ν π := by
  simpa using LocalizedCoupling.warmL2_function_bound ν π hac (fun _=>1) measurable_const (fun _=>le_rfl)

def samplingRadius (d N:ℕ) (M ε:ℝ) : ℝ :=
  3*(d:ℝ)*Real.log 2+2*Real.log (16*(N:ℝ)*M^2/ε^2)

theorem samplingRadius_nonnegative (d:ℕ) {N:ℕ} (hN:0<N) {M ε:ℝ}
    (hM:1 ≤ M) (hε:0<ε) (hε1:ε ≤ 1) : 0 ≤ samplingRadius d N M ε := by
  have hNr:1 ≤ (N:ℝ) := by exact_mod_cast hN
  have harg:1 ≤ 16*(N:ℝ)*M^2/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hm:1 ≤ M^2 := by nlinarith
    have he:ε^2 ≤ 1 := by nlinarith
    nlinarith
  unfold samplingRadius
  positivity [Real.log_nonneg harg,Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

theorem samplingRadius_tail_identity (d:ℕ) {N:ℕ} (hN:0<N) {M ε:ℝ}
    (hM:0<M) (hε:0<ε) :
    (2:ℝ)^(3*(d:ℝ)/2)*Real.exp (-samplingRadius d N M ε/2)=ε^2/(16*(N:ℝ)*M^2) := by
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  have harg:0<16*(N:ℝ)*M^2/ε^2 := by positivity
  rw [Real.rpow_def_of_pos (by norm_num),←Real.exp_add]
  have he:Real.log 2*(3*(d:ℝ)/2)+ -samplingRadius d N M ε/2=
      -Real.log (16*(N:ℝ)*M^2/ε^2) := by unfold samplingRadius; ring
  rw [he,Real.exp_neg,Real.exp_log harg]
  field_simp

variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.samplingRadius_tail {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) {N:ℕ} (hN:0<N) {M ε:ℝ}
    (hM:0<M) (hε:0<ε) :
    (N:ℝ≥0∞)*phaseGibbs U {z|phaseEnergy U z ≤ samplingRadius (Module.finrank ℝ E) N M ε}ᶜ ≤ 
      ENNReal.ofReal (ε^2/(16*M^2)) := by
  have ht:=lemma_5_4 a (samplingRadius (Module.finrank ℝ E) N M ε)
  simp only [hstar,hzero,sub_zero] at ht
  rw [samplingRadius_tail_identity (Module.finrank ℝ E) hN hM hε] at ht
  have he:{z:E×E|phaseEnergy U z ≤ samplingRadius (Module.finrank ℝ E) N M ε}ᶜ=
      {z|samplingRadius (Module.finrank ℝ E) N M ε<phaseEnergy U z} := by ext z; simp
  rw [he]
  apply (mul_le_mul' (le_refl (N:ℝ≥0∞)) ht).trans
  rw [show (N:ℝ≥0∞)=ENNReal.ofReal (N:ℝ) by simp,←ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  apply ENNReal.ofReal_le_ofReal
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  have heq:(N:ℝ)*(ε^2/(16*(N:ℝ)*M^2))=ε^2/(16*M^2) := by field_simp
  exact heq.le

 theorem localized_error_numeric {M ε:ℝ} (hM:1 ≤ M) (hε:0<ε) (hε1:ε ≤ 1)
    {q b W:ℝ≥0∞} (hq:q ≤ ENNReal.ofReal (ε/2))
    (hb:b ≤ ENNReal.ofReal (ε^2/(16*M^2))) (hW:W ≤ ENNReal.ofReal M) :
    q+b+W*b^(1/2:ℝ) ≤ ENNReal.ofReal ε := by
  have hMp:0<M := by linarith
  have hbsmall:ε^2/(16*M^2) ≤ ε/16 := by
    apply (div_le_iff₀ (by positivity :0<16*M^2)).mpr
    have he:ε^2 ≤ ε := by nlinarith
    have hm:1 ≤ M^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hm hε.le]
  have hroot:Real.sqrt (ε^2/(16*M^2))=ε/(4*M) := by
    rw [Real.sqrt_div (sq_nonneg ε),Real.sqrt_sq hε.le]
    have he:16*M^2=(4*M)^2 := by ring
    rw [he,Real.sqrt_sq (by positivity :0≤4*M)]
  have hrpow:ENNReal.ofReal (ε^2/(16*M^2))^(1/2:ℝ)=ENNReal.ofReal (ε/(4*M)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),←Real.sqrt_eq_rpow,hroot]
  calc
    _  ≤  ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/16)+
        ENNReal.ofReal M*(ENNReal.ofReal (ε^2/(16*M^2)))^(1/2:ℝ) := by
      gcongr
      exact hb.trans (ENNReal.ofReal_le_ofReal hbsmall)
    _ = ENNReal.ofReal (ε/2+ε/16+ε/4) := by
      rw [hrpow,←ENNReal.ofReal_mul hMp.le]
      have he:M*(ε/(4*M))=ε/4 := by field_simp
      rw [he,←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
    _  ≤  ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

end PersistencePays
#print axioms PersistencePays.A1.samplingRadius_tail
#print axioms PersistencePays.localized_error_numeric
