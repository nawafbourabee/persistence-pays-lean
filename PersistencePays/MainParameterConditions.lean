import PersistencePays.MainEpochArithmetic
import PersistencePays.MainHessianParameters
import PersistencePays.MainPsiLogBound
import PersistencePays.MainRadiusBounds

/-! Every scalar condition in Proposition 6.1 is satisfied by explicit
parameters depending only on the displayed data of Theorem 1. -/
noncomputable section
namespace PersistencePays.OBABOPath

lemma main_condition_a {L h Q D Λ:ℝ} (hL:0≤L) (hD:1≤D) (hΛ:1≤Λ)
    (hQ:Q≤100*D) (hs:h^2*L*D*Λ≤1/(10:ℝ)^40) (n:ℕ)
    (hlog:Real.log (100*((n+1:ℕ)+1:ℝ))≤(10:ℝ)^9*Λ) :
    h^2*L*(Q+20*Real.log (100*((n+1:ℕ)+1:ℝ)))≤1/5000 := by
  have hDΛ:D≤D*Λ := le_mul_of_one_le_right (by linarith) hΛ
  have hΛD:Λ≤D*Λ := le_mul_of_one_le_left (by linarith) hD
  have hb:Q+20*Real.log (100*((n+1:ℕ)+1:ℝ))≤(10:ℝ)^11*(D*Λ) := by
    norm_num only [show (10:ℝ)^9=1000000000 by norm_num] at hlog
    norm_num only [show (10:ℝ)^11=100000000000 by norm_num]
    linarith
  calc
    _ ≤ h^2*L*((10:ℝ)^11*(D*Λ)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (10:ℝ)^11*(h^2*L*D*Λ) := by ring
    _ ≤ (10:ℝ)^11*(1/(10:ℝ)^40) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 1/5000 := by norm_num

lemma main_condition_d {Q D Λ Ψ h:ℝ} (hD:1≤D) (hΛ:1≤Λ)
    (hQ:Q≤100*D) (n:ℕ)
    (hlogE:Real.log ((n+1:ℕ):ℝ)≤(10:ℝ)^8*Λ)
    (hlogPsi:Real.log (Ψ/h)≤(10:ℝ)^10*Λ) :
    41*(Q+20*Real.log (2*((n+1:ℕ):ℝ))+80*Real.log (Ψ/h)+922)≤
      ((10:ℝ)^38*D^(3/2:ℝ)*Λ)^2 := by
  have hDΛ:D≤D*Λ := le_mul_of_one_le_right (by linarith) hΛ
  have hΛD:Λ≤D*Λ := le_mul_of_one_le_left (by linarith) hD
  have hDΛ1:1≤D*Λ := one_le_mul_of_one_le_of_one_le hD hΛ
  have hl2:Real.log (2:ℝ)≤1 := by
    have hp:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hclock:Real.log (2*((n+1:ℕ):ℝ))≤2*(10:ℝ)^8*Λ := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    norm_num only [show (10:ℝ)^8=100000000 by norm_num] at hlogE ⊢
    linarith
  have hleft:41*(Q+20*Real.log (2*((n+1:ℕ):ℝ))+80*Real.log (Ψ/h)+922)≤
      (10:ℝ)^14*(D*Λ) := by
    norm_num only [show (10:ℝ)^8=100000000 by norm_num] at hclock
    norm_num only [show (10:ℝ)^10=10000000000 by norm_num] at hlogPsi
    norm_num only [show (10:ℝ)^14=100000000000000 by norm_num]
    linarith
  have hDp:D≤D^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (1:ℝ)≤3/2)
  have hv:(10:ℝ)^38*(D*Λ)≤(10:ℝ)^38*D^(3/2:ℝ)*Λ := by
    have ht:=mul_le_mul_of_nonneg_right hDp (by positivity :0≤(10:ℝ)^38*Λ)
    nlinarith only [ht]
  have hv0:0≤(10:ℝ)^38*D^(3/2:ℝ)*Λ := by positivity
  have hv1:(10:ℝ)^38≤(10:ℝ)^38*D^(3/2:ℝ)*Λ := by
    have ht:=mul_le_mul_of_nonneg_left hDΛ1 (by positivity :0≤(10:ℝ)^38)
    nlinarith only [hv,ht]
  have hv2:=mul_le_mul hv hv1 (by positivity :0≤(10:ℝ)^38) hv0
  calc
    _ ≤ (10:ℝ)^14*(D*Λ) := hleft
    _ ≤ ((10:ℝ)^38*(D*Λ))*(10:ℝ)^38 := by
      have hc:(10:ℝ)^14≤(10:ℝ)^38*(10:ℝ)^38 := by norm_num
      nlinarith only [mul_le_mul_of_nonneg_right hc (by positivity :0≤D*Λ)]
    _ ≤ ((10:ℝ)^38*D^(3/2:ℝ)*Λ)^2 := by nlinarith only [hv2]

/-- A universal choice satisfying every condition, also when LH=0. -/
theorem main_normalized_conditions {L LH D R:ℝ} {d:ℕ}
    (hL:1≤L) (hLH:0≤LH) (hD:1≤D) (hR:0≤R)
    (hRD:R≤100*D) (hd:(d:ℝ)≤D) (hQ:comparisonQ R d≤100*D) :
    NormalizedEpochConditions L LH (mainStep L LH D) (mainCutoff L LH D) R d
      (mainEpochPredecessor L LH D) := by
  obtain ⟨hh,hhmax,hsq,hfirst,hsecond,hlog0,hlog⟩:=main_step_bounds hL hLH hD
  obtain ⟨hΛ,hlogD,hS,hlogS⟩:=main_log_bounds hL hLH hD
  have hh1:mainStep L LH D≤1 := hhmax.trans (by norm_num)
  have hb:=main_epoch_arithmetic hh hh1 hΛ hlog
  change (10:ℝ)^7*mainLogScale L LH D≤(mainEpochPredecessor L LH D:ℝ)*mainStep L LH D ∧
    ((mainEpochPredecessor L LH D+1:ℕ):ℝ)*mainStep L LH D≤10000002*mainLogScale L LH D ∧
    Real.log ((mainEpochPredecessor L LH D+1:ℕ):ℝ)≤(10:ℝ)^8*mainLogScale L LH D ∧
    Real.log (100*((mainEpochPredecessor L LH D+1:ℕ)+1:ℝ))≤(10:ℝ)^9*mainLogScale L LH D at hb
  have hQ0:0≤comparisonQ R d := (by norm_num : (0:ℝ)≤50).trans (comparisonQ_ge_fifty hR d)
  have hsecond':mainStep L LH D^2*LH*D^(3/2:ℝ)*mainLogScale L LH D≤(10:ℝ)^(-40:ℤ) := by
    convert hsecond using 1 <;> norm_num
  have hH:=main_hessian_parameters hD hΛ hLH hh hQ0 hQ hsecond'
    (mainEpochPredecessor L LH D) hb.2.1
  have hPsi:=comparisonPsi_log_bound d (mainEpochPredecessor L LH D+1) hR hRD hd hQ hD hΛ hlogD
    hh hh1 hlog hb.2.1
  refine ⟨hh,hR,hH.2.2,hLH,hH.2.1,?_,hH.1,?_,?_⟩
  · exact main_condition_a (by linarith) hD hΛ hQ hfirst _ hb.2.2.2
  · exact main_epoch_condition_c hL hLH hD hR hRD hd
  · exact main_condition_d hD hΛ hQ _ hb.2.2.1 hPsi

/-- The actual warm-start radius introduces no extra restriction. -/
theorem main_warm_parameters (d:ℕ) (hd:1≤d) {L LH M ε:ℝ}
    (hL:1≤L) (hLH:0≤LH) (hM:1≤M) (hε:0<ε) (hε1:ε≤1) :
    let D:=(d:ℝ)+Real.log (M/ε)
    NormalizedEpochConditions L LH (mainStep L LH D) (mainCutoff L LH D)
      (samplingRadius d (samplingEpochs ε) M ε) d (mainEpochPredecessor L LH D) := by
  obtain ⟨hD,hdD,hR,hRD,hQ⟩:=main_radius_bounds d hd hM hε hε1
  exact main_normalized_conditions hL hLH hD hR (by nlinarith) hdD hQ

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.main_normalized_conditions
#print axioms PersistencePays.OBABOPath.main_warm_parameters
