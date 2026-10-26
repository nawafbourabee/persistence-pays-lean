import PersistencePays.NormalizedEpochConditions
import PersistencePays.SectionSixConstants

/-! Explicit universal parameter choices for Theorem 1. The deliberately
conservative numerical constants are absolute and do not affect exponents. -/
noncomputable section
namespace PersistencePays.OBABOPath

def mainComplexityScale (L LH D : ℝ) : ℝ := L*D+LH*D^(3/2:ℝ)
def mainLogScale (L LH D : ℝ) : ℝ := Real.log (2+L+LH+D)
def mainStep (L LH D : ℝ) : ℝ :=
  1/((10:ℝ)^20*Real.sqrt (mainLogScale L LH D)*Real.sqrt (mainComplexityScale L LH D))
def mainEpochPredecessor (L LH D : ℝ) : ℕ :=
  ⌈(10:ℝ)^7*mainLogScale L LH D/mainStep L LH D⌉₊
def mainCutoff (L LH D : ℝ) : ℝ :=
  (10:ℝ)^38*D^(3/2:ℝ)*mainLogScale L LH D

lemma log_ten_le_nine : Real.log (10:ℝ) ≤ 9 := by
  have h:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)
  linarith

lemma log_four_ge_one : (1:ℝ) ≤ Real.log 4 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have he : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  norm_num at h
  linarith

lemma main_log_bounds {L LH D:ℝ} (hL:1 ≤ L) (hLH:0 ≤ LH) (hD:1 ≤ D) :
    1 ≤ mainLogScale L LH D ∧ Real.log D ≤ mainLogScale L LH D ∧
      1 ≤ mainComplexityScale L LH D ∧
      Real.log (mainComplexityScale L LH D) ≤ 1+3*mainLogScale L LH D := by
  let K:=2+L+LH+D
  have hK:4 ≤ K := by dsimp [K]; linarith
  have hDp:0<D := by linarith
  have hSp:0< mainComplexityScale L LH D := by unfold mainComplexityScale; positivity
  have hS:1 ≤ mainComplexityScale L LH D := by
    have hp:=mul_le_mul hL hD (by norm_num) (by linarith :0 ≤ L)
    have hn:0 ≤ LH*D^(3/2:ℝ) := by positivity
    unfold mainComplexityScale
    linarith
  have hpow:D^(3/2:ℝ) ≤ D^2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (3/2:ℝ) ≤ 2)
  have hLK:L ≤ K := by dsimp [K]; linarith
  have hHK:LH ≤ K := by dsimp [K]; linarith
  have hDK:D ≤ K := by dsimp [K]; linarith
  have hSupper:mainComplexityScale L LH D ≤ 2*K^3 := by
    have hLD:L*D ≤ K^2 := by nlinarith [mul_le_mul hLK hDK (by linarith :0 ≤ D) (by linarith :0 ≤ K)]
    have hHD:LH*D^(3/2:ℝ) ≤ K^3 := by
      calc
        _  ≤  K*D^2 := mul_le_mul hHK hpow (by positivity) (by linarith)
        _  ≤  K*K^2 := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
        _ = K^3 := by ring
    unfold mainComplexityScale
    nlinarith [sq_nonneg K]
  have hlog := Real.log_le_log hSp hSupper
  have hl2:Real.log (2:ℝ) ≤ 1 := by
    have ht:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  refine ⟨?_,?_,hS,?_⟩
  · exact log_four_ge_one.trans (Real.log_le_log (by norm_num) hK)
  · exact Real.log_le_log hDp hDK
  · dsimp [mainLogScale]
    change Real.log (mainComplexityScale L LH D) ≤ 1+3*Real.log K
    norm_num at hlog
    linarith

theorem main_step_bounds {L LH D:ℝ} (hL:1 ≤ L) (hLH:0 ≤ LH) (hD:1 ≤ D) :
    let h:=mainStep L LH D
    let Λ:=mainLogScale L LH D
    let S:=mainComplexityScale L LH D
    0<h ∧ h ≤ 1/(10:ℝ)^20 ∧
    h^2*S*Λ=1/(10:ℝ)^40 ∧
    h^2*L*D*Λ ≤ 1/(10:ℝ)^40 ∧
    h^2*LH*D^(3/2:ℝ)*Λ ≤ 1/(10:ℝ)^40 ∧
    0 ≤ Real.log (1/h^2) ∧ Real.log (1/h^2) ≤ 500*Λ := by
  dsimp only
  obtain ⟨hΛ,hlogD,hS,hlogS⟩:=main_log_bounds hL hLH hD
  have hΛp:0< mainLogScale L LH D := by linarith
  have hSp:0< mainComplexityScale L LH D := by linarith
  have hrootΛ:1 ≤ Real.sqrt (mainLogScale L LH D) := by simpa using Real.sqrt_le_sqrt hΛ
  have hrootS:1 ≤ Real.sqrt (mainComplexityScale L LH D) := by simpa using Real.sqrt_le_sqrt hS
  have hh:0< mainStep L LH D := by unfold mainStep; positivity
  have hhmax:mainStep L LH D ≤ 1/(10:ℝ)^20 := by
    unfold mainStep
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [mul_le_mul hrootΛ hrootS (by norm_num) (by positivity :0 ≤ Real.sqrt (mainLogScale L LH D))]
  have hsquare:mainStep L LH D^2*mainComplexityScale L LH D*mainLogScale L LH D=1/(10:ℝ)^40 := by
    unfold mainStep
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hΛp.le,Real.sq_sqrt hSp.le]
    field_simp
    <;> ring
  have hfirst:mainStep L LH D^2*L*D*mainLogScale L LH D ≤ 1/(10:ℝ)^40 := by
    rw [←hsquare]
    have hle:L*D ≤ mainComplexityScale L LH D := by
      unfold mainComplexityScale
      have hp:0≤LH*D^(3/2:ℝ) := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hle (by positivity :0 ≤ mainStep L LH D^2*mainLogScale L LH D)]
  have hsecond:mainStep L LH D^2*LH*D^(3/2:ℝ)*mainLogScale L LH D ≤ 1/(10:ℝ)^40 := by
    rw [←hsquare]
    have hle:LH*D^(3/2:ℝ) ≤ mainComplexityScale L LH D := by
      unfold mainComplexityScale
      have hp:0≤L*D := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hle (by positivity :0 ≤ mainStep L LH D^2*mainLogScale L LH D)]
  have hlogid:Real.log (1/mainStep L LH D^2)=
      40*Real.log 10+Real.log (mainLogScale L LH D)+Real.log (mainComplexityScale L LH D) := by
    have hid:1/mainStep L LH D^2=(10:ℝ)^40*mainLogScale L LH D*mainComplexityScale L LH D := by
      unfold mainStep
      rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hΛp.le,Real.sq_sqrt hSp.le]
      field_simp
      <;> ring
    rw [hid,Real.log_mul (by positivity) hSp.ne',Real.log_mul (by positivity) hΛp.ne',Real.log_pow]
    norm_num
  have hlog0:0 ≤ Real.log (1/mainStep L LH D^2) := by
    apply Real.log_nonneg
    apply (one_le_div (sq_pos_of_pos hh)).mpr
    nlinarith
  refine ⟨hh,hhmax,hsquare,hfirst,hsecond,hlog0,?_⟩
  rw [hlogid]
  have ht:=log_ten_le_nine
  have hl:=Real.log_le_sub_one_of_pos hΛp
  nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.main_step_bounds
