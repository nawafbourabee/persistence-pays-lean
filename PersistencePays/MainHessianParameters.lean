import PersistencePays.EpochParameters

/-! Explicit Hessian-error and cutoff-scale checks for the main step schedule,
including LH=0. These are purely scalar consequences of the chosen step. -/
namespace PersistencePays

lemma main_hessian_power_bound {Q D:ℝ} (hQ:0≤Q) (hD:1≤D) (hQD:Q≤100*D) :
    ((6.6:ℝ)*Q)^(3/2:ℝ)≤(10:ℝ)^6*D^(3/2:ℝ) := by
  have hDp:0≤D := by linarith
  have hb:(6.6:ℝ)*Q≤1000*D := by nlinarith
  have hp:=Real.rpow_le_rpow (by positivity :0≤(6.6:ℝ)*Q) hb (by norm_num :0≤(3/2:ℝ))
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1000) hDp] at hp
  have hc: (1000:ℝ)^(3/2:ℝ)≤(10:ℝ)^6 := by
    calc
      _ ≤ (1000:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by rw [Real.rpow_two]; norm_num
  exact hp.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hDp _))

theorem main_hessian_parameters {D Λ LH h Q:ℝ} (hD:1≤D) (hΛ:1≤Λ)
    (hLH:0≤LH) (hh:0<h) (hQ:0≤Q) (hQD:Q≤100*D)
    (hs: h^2*LH*D^(3/2:ℝ)*Λ≤(10:ℝ)^(-40:ℤ)) (n:ℕ)
    (htime:((n+1:ℕ):ℝ)*h≤10000002*Λ) :
    LH*h^2*((6.6:ℝ)*Q)^(3/2:ℝ)*(1+((n+1:ℕ):ℝ)*h)≤1/1000 ∧
    LH*h^3/12*((10:ℝ)^38*D^(3/2:ℝ)*Λ)≤(0.02:ℝ)*h ∧
    0≤(10:ℝ)^38*D^(3/2:ℝ)*Λ := by
  have hDp:0≤D := by linarith
  have hΛp:0≤Λ := by linarith
  have hpow:0≤D^(3/2:ℝ) := Real.rpow_nonneg hDp _
  have hB:0≤LH*h^2 := by positivity
  have htime':1+((n+1:ℕ):ℝ)*h≤10000003*Λ := by linarith
  have hclock:0≤1+((n+1:ℕ):ℝ)*h := by positivity
  have hp:=main_hessian_power_bound hQ hD hQD
  refine ⟨?_,?_,by positivity⟩
  · have ht:=mul_le_mul (mul_le_mul_of_nonneg_left hp hB) htime' hclock (by positivity)
    have hs': LH*h^2*D^(3/2:ℝ)*Λ≤(10:ℝ)^(-40:ℤ) := by nlinarith [hs]
    have hb:=mul_le_mul_of_nonneg_left hs' (by positivity :0≤(10:ℝ)^6*10000003)
    calc
      _ ≤ (LH*h^2)*((10:ℝ)^6*D^(3/2:ℝ))*(10000003*Λ) := ht
      _ = ((10:ℝ)^6*10000003)*(LH*h^2*D^(3/2:ℝ)*Λ) := by ring
      _ ≤ ((10:ℝ)^6*10000003)*(10:ℝ)^(-40:ℤ) := hb
      _ ≤ 1/1000 := by norm_num
  · have ht:=mul_le_mul_of_nonneg_left hs (show 0≤h*(10:ℝ)^38/12 by positivity)
    have he: LH*h^3/12*((10:ℝ)^38*D^(3/2:ℝ)*Λ)=
      (h*(10:ℝ)^38/12)*(h^2*LH*D^(3/2:ℝ)*Λ) := by ring
    rw [he]
    apply ht.trans
    norm_num
    nlinarith

end PersistencePays
#print axioms PersistencePays.main_hessian_parameters
