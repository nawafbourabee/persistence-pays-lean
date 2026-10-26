import PersistencePays.EntropyParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Checked numerical constants in the final normalized entropy estimate. -/
namespace PersistencePays

lemma exp_neg_eighth_lower : (0.8824:ℝ)≤Real.exp (-(1/8:ℝ)) := by
  have ht:=Real.exp_bound (x:=-(1/8:ℝ)) (by norm_num) (n:=4) (by norm_num)
  norm_num [Finset.sum_range_succ] at ht
  have hlow := (abs_le.mp ht).1
  linarith

theorem comparison_entropy_rate_constants {h:ℝ} (hh:0<h) (hmax:h≤1/8) :
    let r:=Real.exp (-h)
    let rate:=r^2/(4*(16+r))
    0<rate ∧ 1/(rate*h)≤(86.8:ℝ)/h ∧ (16+r)/(4*r)≤(4.79:ℝ) := by
  dsimp only
  let r:=Real.exp (-h)
  have hr:0<r := Real.exp_pos _
  have hrlo:(0.8824:ℝ)≤r := exp_neg_eighth_lower.trans (Real.exp_le_exp.mpr (by linarith))
  have hrate:0<r^2/(4*(16+r)) := by positivity
  change 0<r^2/(4*(16+r)) ∧ _
  refine ⟨hrate,?_,?_⟩
  · have hinv:1/(r^2/(4*(16+r)))≤(86.8:ℝ) := by
      rw [one_div_div]
      apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      nlinarith [sq_nonneg (r-(0.8824:ℝ))]
    calc
      1/((r^2/(4*(16+r)))*h)=(1/(r^2/(4*(16+r))))/h := by ring
      _ ≤ (86.8:ℝ)/h := div_le_div_of_nonneg_right hinv hh.le
  · apply (div_le_iff₀ (by positivity :0<4*r)).mpr
    linarith

lemma comparison_entropy_remainder_constants {Q h L LH M u v b t rate:ℝ}
    (hQ:0≤Q) (hh:0<h) (hL:0≤L) (hLH:0≤LH) (hM:0≤M) (hr:0<rate)
    (hinv:1/(rate*h)≤(86.8:ℝ)/h)
    (hu:u≤(1.27:ℝ)*Q) (hv:v≤(2.61:ℝ)*Q)
    (hb:b≤(13/4:ℝ)*(h^2*L)*v+6*(10:ℝ)^(-5:ℤ))
    (ht0:0≤t) (ht:t≤(LH*h^3/12)*M+(10:ℝ)^(-11:ℤ)*h) :
    (h^2*L/4)*u+(1/(rate*h))*t+(4.79:ℝ)*b ≤
      (40.95:ℝ)*(h^2*L)*Q+(7.234:ℝ)*LH*h^2*M+3*(10:ℝ)^(-4:ℤ) := by
  have hut:=mul_le_mul_of_nonneg_left hu (by positivity :0≤h^2*L/4)
  have hvb:=mul_le_mul_of_nonneg_left hv (by positivity :0≤(13/4:ℝ)*(h^2*L))
  have hb':b≤(13/4:ℝ)*(h^2*L)*((2.61:ℝ)*Q)+6*(10:ℝ)^(-5:ℤ) := by linarith
  have hbt:=mul_le_mul_of_nonneg_left hb' (by norm_num : (0:ℝ)≤4.79)
  have htt:=mul_le_mul hinv ht ht0 (by positivity :0≤(86.8:ℝ)/h)
  have he:((86.8:ℝ)/h)*((LH*h^3/12)*M+(10:ℝ)^(-11:ℤ)*h)=
      ((86.8:ℝ)/12)*LH*h^2*M+(86.8:ℝ)*(10:ℝ)^(-11:ℤ) := by field_simp
  rw [he] at htt
  have hp:0≤h^2*L*Q := by positivity
  have hd:0≤LH*h^2*M := by positivity
  norm_num at hut hbt htt ⊢
  nlinarith


lemma comparison_entropy_numeric {B A T X Y rate:ℝ}
    (hA:0≤A)
    (hdecay:rate*T≥Real.log (227*A))
    (ha:X≤1/5000) (hb:Y≤1/1000)
    (hbound:B≤(17/15:ℝ)*Real.exp (-rate*T)*A+
      (16/15:ℝ)*((40.95:ℝ)*X+(7.234:ℝ)*Y+3*(10:ℝ)^(-4:ℤ))) :
    B≤(0.0218:ℝ) := by
  have hlead:Real.exp (-rate*T)*A≤1/227 := by
    by_cases hAz:A=0
    · simp [hAz]
    have hAp:0<A := lt_of_le_of_ne hA (Ne.symm hAz)
    have he:=Real.exp_le_exp.mpr (show -rate*T≤-Real.log (227*A) by linarith)
    rw [Real.exp_neg,Real.exp_log (by positivity)] at he
    have ht:=mul_le_mul_of_nonneg_right he hA
    have hid:(227*A)⁻¹*A=(1/227:ℝ) := by field_simp
    rwa [hid] at ht
  simp only [neg_mul] at hlead hbound
  norm_num at hbound ⊢
  nlinarith

end PersistencePays
#print axioms PersistencePays.comparison_entropy_rate_constants
#print axioms PersistencePays.comparison_entropy_numeric
