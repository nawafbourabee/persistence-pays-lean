import PersistencePays.EpochParameters
import PersistencePays.MainOneLogBounds

/-! A uniform explicit logarithmic bound for the comparison-chain envelope. -/
noncomputable section
namespace PersistencePays.OBABOPath

theorem comparisonPsi_log_bound {R D Λ h:ℝ} (d N:ℕ)
    (hR:0≤R) (hRD:R≤100*D) (hd:(d:ℝ)≤D)
    (hQ:comparisonQ R d≤100*D) (hD:1≤D) (hΛ:1≤Λ)
    (hlogD:Real.log D≤Λ) (hh:0<h) (hh1:h≤1)
    (hlog:Real.log (1/h^2)≤500*Λ)
    (ht:(N:ℝ)*h≤10000002*Λ) :
    Real.log (comparisonPsi R d h N/h)≤(10:ℝ)^10*Λ := by
  let t:ℝ:=(N:ℝ)*h
  let e:ℝ:=Real.exp ((0.081:ℝ)*t)
  have hD0:0<D:=by linarith
  have hΛ0:0<Λ:=by linarith
  have ht0:0≤t:=by dsimp [t];positivity
  have he:1≤e:=Real.one_le_exp_iff.mpr (by dsimp [t];positivity)
  have he0:0<e:=Real.exp_pos _
  have hDL:D≤D*Λ:=by nlinarith
  have hDL0:0≤D*Λ:=by positivity
  have hDLe:D*Λ≤D*Λ*e:=by nlinarith
  have htp:t+1≤10000003*Λ:=by dsimp [t];linarith
  have hd2:(d:ℝ)+2≤3*D:=by linarith
  have hbr:R+2*((d:ℝ)+2)*(t+1)≤60000118*(D*Λ):=by
    have hm:=mul_le_mul hd2 htp (by positivity :0≤t+1) (by positivity :0≤3*D)
    nlinarith
  have hXi:comparisonXi R d h N≤200000000*(D*Λ*e):=by
    have hm:=mul_le_mul_of_nonneg_left hbr (by positivity :0≤(1.01:ℝ)*e)
    unfold comparisonXi
    change (1.01:ℝ)*e*(R+2*((d:ℝ)+2)*(t+1))≤_
    nlinarith [mul_nonneg hDL0 he0.le]
  have hQ':comparisonQ R d≤100*(D*Λ*e):=by nlinarith
  have hlog':(d:ℝ)*Real.log (1/h^2)≤500*(D*Λ*e):=by
    have hm:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d)
    have hm2:=mul_le_mul_of_nonneg_right hd (by positivity :0≤500*Λ)
    nlinarith
  have ht':2*(d:ℝ)*(N:ℝ)*h≤20000004*(D*Λ*e):=by
    have hm:=mul_le_mul hd ht (by positivity :0≤(N:ℝ)*h) hD0.le
    nlinarith
  have hΨ:comparisonPsi R d h N≤(10:ℝ)^9*D*Λ*e:=by
    unfold comparisonPsi
    nlinarith
  have hΨ0:0<comparisonPsi R d h N:=by
    have hp:=(comparisonPsi_lower hR hh hh1 d N).2
    linarith
  have hl:=Real.log_le_log hΨ0 hΨ
  rw [Real.log_mul (by positivity) he0.ne',Real.log_mul (by positivity) hΛ0.ne',
    Real.log_mul (by positivity) hD0.ne',Real.log_exp] at hl
  have hC:Real.log ((10:ℝ)^9)≤(10:ℝ)^9:=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by norm_num)
  have hlogΛ:Real.log Λ≤Λ:=
    (Real.log_le_sub_one_of_pos hΛ0).trans (by linarith)
  have hlogh: -Real.log h≤250*Λ:=by
    rw [Real.log_div one_ne_zero (by positivity),Real.log_one,Real.log_pow] at hlog
    norm_num at hlog
    linarith
  rw [Real.log_div hΨ0.ne' hh.ne']
  dsimp [e,t] at hl
  norm_num at hC hl ⊢
  nlinarith only [hl,hC,hlogD,hlogΛ,hlogh,ht,hΛ]

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.comparisonPsi_log_bound
