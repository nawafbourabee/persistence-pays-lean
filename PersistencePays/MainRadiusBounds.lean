import PersistencePays.WarmEpochCount
import PersistencePays.EpochParameters

/-! Scalar radius bounds used by the explicit main-theorem parameter choice. -/
noncomputable section
namespace PersistencePays
open scoped ENNReal

lemma main_log_four_bounds : (1:ℝ)≤Real.log 4 ∧ Real.log 2≤1 ∧ Real.log 16≤4 := by
  have hl:=Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hu:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have h4:Real.log (4:ℝ)=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have h16:Real.log (16:ℝ)=4*Real.log 2 := by rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]; norm_num
  norm_num at hl hu
  exact ⟨by linarith,hu,by linarith⟩

theorem samplingEpochs_le_two_div {ε:ℝ} (hε:0<ε) (hε1:ε≤1) :
    (samplingEpochs ε:ℝ)≤2/ε := by
  have hx:1≤2/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hlog:0≤Real.log (2/ε) := Real.log_nonneg hx
  have hfour:=main_log_four_bounds.1
  have hdiv:Real.log (2/ε)/Real.log 4≤Real.log (2/ε) :=
    div_le_self hlog hfour
  have hc: (samplingEpochs ε:ℝ)≤Real.log (2/ε)/Real.log 4+1 :=
    (Nat.ceil_lt_add_one (div_nonneg hlog (by linarith))).le
  have hu:=Real.log_le_sub_one_of_pos (by positivity :0<2/ε)
  linarith

/-- The exact warm radius satisfies R≤16D and Q≤100D. No asymptotic notation
or unspecified logarithm constants occur in this estimate. -/
theorem main_radius_bounds (d:ℕ) (hd:1≤d) {M ε:ℝ}
    (hM:1≤M) (hε:0<ε) (hε1:ε≤1) :
    let D:=(d:ℝ)+Real.log (M/ε)
    let R:=samplingRadius d (samplingEpochs ε) M ε
    1≤D ∧ (d:ℝ)≤D ∧ 0≤R ∧ R≤16*D ∧ OBABOPath.comparisonQ R d≤100*D := by
  let D:=(d:ℝ)+Real.log (M/ε)
  let N:=samplingEpochs ε
  let R:=samplingRadius d N M ε
  have hMp:0<M := by linarith
  have hN:0<N := samplingEpochs_pos hε hε1
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  have hd':1≤(d:ℝ) := by exact_mod_cast hd
  have hlM:0≤Real.log M := Real.log_nonneg hM
  have hlε:Real.log ε≤0 := Real.log_nonpos hε.le hε1
  have hlid:Real.log (M/ε)=Real.log M-Real.log ε := Real.log_div hMp.ne' hε.ne'
  have hD1:1≤D := by dsimp [D]; rw [hlid]; linarith
  have hdD:(d:ℝ)≤D := by dsimp [D]; rw [hlid]; linarith
  have hR:0≤R := samplingRadius_nonnegative d hN hM hε hε1
  have hln:Real.log (N:ℝ)≤Real.log 2-Real.log ε := by
    have ht:=Real.log_le_log hNr (samplingEpochs_le_two_div hε hε1)
    rwa [Real.log_div (by norm_num : (2:ℝ)≠0) hε.ne'] at ht
  have hRexp:R=3*(d:ℝ)*Real.log 2+
      2*(Real.log 16+Real.log (N:ℝ)+2*Real.log M-2*Real.log ε) := by
    unfold R samplingRadius
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) hNr.ne',
      Real.log_pow,Real.log_pow]
    norm_num
  have hl2:=main_log_four_bounds.2.1
  have hl16:=main_log_four_bounds.2.2
  have hdlog:=mul_le_mul_of_nonneg_left hl2 (show 0≤3*(d:ℝ) by positivity)
  have hRbound:R≤16*D := by
    rw [hRexp]
    dsimp [D]
    rw [hlid]
    nlinarith
  have hQ:OBABOPath.comparisonQ R d≤100*D := by
    unfold OBABOPath.comparisonQ
    nlinarith
  exact ⟨hD1,hdD,hR,hRbound,hQ⟩

end PersistencePays
#print axioms PersistencePays.main_radius_bounds
