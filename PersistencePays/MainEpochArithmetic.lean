import PersistencePays.MainStepBounds
import PersistencePays.TheoremTwoLiteral

noncomputable section
namespace PersistencePays.OBABOPath

lemma main_epoch_arithmetic {h Λ:ℝ} (hh:0<h) (hh1:h≤1) (hΛ:1≤Λ)
    (hlog:Real.log (1/h^2)≤500*Λ) :
    let n:ℕ:=⌈(10:ℝ)^7*Λ/h⌉₊
    (10:ℝ)^7*Λ≤(n:ℝ)*h ∧
    ((n+1:ℕ):ℝ)*h≤10000002*Λ ∧
    Real.log ((n+1:ℕ):ℝ)≤(10:ℝ)^8*Λ ∧
    Real.log (100*((n+1:ℕ)+1:ℝ))≤(10:ℝ)^9*Λ := by
  dsimp only
  let n:ℕ:=⌈(10:ℝ)^7*Λ/h⌉₊
  have hx:0≤(10:ℝ)^7*Λ/h := by positivity
  have hnlo:(10:ℝ)^7*Λ/h≤(n:ℝ) := Nat.le_ceil _
  have hnhi:(n:ℝ)≤(10:ℝ)^7*Λ/h+1 := (Nat.ceil_lt_add_one hx).le
  have hlow:(10:ℝ)^7*Λ≤(n:ℝ)*h := (div_le_iff₀ hh).mp hnlo
  have hhigh:(n:ℝ)*h≤(10:ℝ)^7*Λ+h := by
    have ht:=mul_le_mul_of_nonneg_right hnhi hh.le
    have he:((10:ℝ)^7*Λ/h+1)*h=(10:ℝ)^7*Λ+h := by field_simp
    rwa [he] at ht
  have htime:((n+1:ℕ):ℝ)*h≤10000002*Λ := by push_cast; norm_num at hhigh ⊢; nlinarith
  have hlogh: -Real.log h≤250*Λ := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow] at hlog
    norm_num at hlog
    linarith
  have hΛp:0<Λ := by linarith
  have hlogΛ:Real.log Λ≤Λ-1 := Real.log_le_sub_one_of_pos hΛp
  have hlarge:0<(10000003:ℝ)*Λ/h := by positivity
  have hsize:((n+1:ℕ)+1:ℝ)≤10000003*Λ/h := by
    apply (le_div_iff₀ hh).mpr
    push_cast
    norm_num at hhigh
    nlinarith
  have hlogsize:Real.log ((n+1:ℕ)+1:ℝ)≤(10:ℝ)^8*Λ := by
    have hl:=Real.log_le_log (by positivity :0<((n+1:ℕ)+1:ℝ)) hsize
    rw [Real.log_div (by positivity) hh.ne',Real.log_mul (by norm_num) hΛp.ne'] at hl
    have hc:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10000003)
    norm_num only at hc
    norm_num only [Nat.cast_add,Nat.cast_one] at hl ⊢
    norm_num only [show (10:ℝ)^8=100000000 by norm_num]
    linarith
  refine ⟨hlow,htime,?_,?_⟩
  · exact (Real.log_le_log (by positivity :0<((n+1:ℕ):ℝ)) (by push_cast; linarith)).trans hlogsize
  · rw [Real.log_mul (by norm_num) (by positivity)]
    have hc:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
    norm_num only at hc
    change Real.log 100+Real.log ((n+1:ℕ)+1:ℝ)≤(10:ℝ)^9*Λ
    norm_num only [show (10:ℝ)^8=100000000 by norm_num] at hlogsize
    norm_num only [show (10:ℝ)^9=1000000000 by norm_num]
    linarith

lemma main_entropy_log_bound {R D Λ h:ℝ} {d:ℕ}
    (hR:0≤R) (hRD:R≤100*D) (hD:1≤D) (hd:(d:ℝ)≤D) (hΛ:1≤Λ)
    (hlogD:Real.log D≤Λ) (hh:0<h)
    (hlog0:0≤Real.log (1/h^2)) (hlog:Real.log (1/h^2)≤500*Λ) :
    Real.log (227*((1.02:ℝ)*R+(d:ℝ)*Real.log (1/h^2)))≤100*Λ := by
  let Z:=227*((1.02:ℝ)*R+(d:ℝ)*Real.log (1/h^2))
  have hZ:0≤Z := by dsimp [Z]; positivity
  by_cases hp:0<Z
  · have hDΛ:D≤D*Λ := le_mul_of_one_le_right (by linarith) hΛ
    have hb:Z≤(10:ℝ)^6*D*Λ := by
      have hdlog:=mul_le_mul hd hlog hlog0 (by linarith :0≤D)
      dsimp [Z]
      norm_num only [show (10:ℝ)^6=1000000 by norm_num]
      nlinarith
    have hl:=Real.log_le_log hp hb
    rw [Real.log_mul (by positivity) (by linarith :Λ≠0),
      Real.log_mul (by norm_num) (by linarith :D≠0),Real.log_pow] at hl
    have hlogΛ:=Real.log_le_sub_one_of_pos (by linarith :0<Λ)
    have ht:=log_ten_le_nine
    change Real.log Z≤100*Λ
    norm_num at hl
    linarith
  · have hz:Z=0 := le_antisymm (le_of_not_gt hp) hZ
    change Real.log Z≤100*Λ
    rw [hz,Real.log_zero]
    positivity

lemma main_epoch_condition_c {L LH D R:ℝ} {d:ℕ}
    (hL:1≤L) (hLH:0≤LH) (hD:1≤D) (hR:0≤R)
    (hRD:R≤100*D) (hd:(d:ℝ)≤D) :
    let h:=mainStep L LH D
    let n:=mainEpochPredecessor L LH D
    (Real.exp (-h))^2/(4*(16+Real.exp (-h)))*h*(n:ℝ)≥
      Real.log (227*((1.02:ℝ)*R+(d:ℝ)*Real.log (1/h^2))) := by
  dsimp only
  obtain ⟨hh,hhmax,hsq,hfirst,hsecond,hlog0,hlog⟩:=main_step_bounds hL hLH hD
  obtain ⟨hΛ,hlogD,hS,hlogS⟩:=main_log_bounds hL hLH hD
  have hh1:mainStep L LH D≤1 := hhmax.trans (by norm_num)
  have hb:=main_epoch_arithmetic hh hh1 hΛ hlog
  change (10:ℝ)^7*mainLogScale L LH D≤(mainEpochPredecessor L LH D:ℝ)*mainStep L LH D ∧ _ at hb
  have hr:=normalized_entropy_rate_ge hh.le (hhmax.trans (by norm_num))
  have hn:0≤(mainEpochPredecessor L LH D:ℝ)*mainStep L LH D := by positivity
  have ht:=mul_le_mul_of_nonneg_right hr hn
  have hl:=main_entropy_log_bound hR hRD hD hd hΛ hlogD hh hlog0 hlog
  norm_num at hb
  nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.main_epoch_arithmetic
#print axioms PersistencePays.OBABOPath.main_epoch_condition_c
