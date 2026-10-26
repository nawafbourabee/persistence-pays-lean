import PersistencePays.PrefixExit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Explicit scalar estimates for the actual comparison remainder. The inputs
are tail probabilities and moments, which are instantiated with the sampler in
ComparisonRemainder. -/
namespace PersistencePays
open Real

lemma mul_log_inv_le_sqrt {x:ℝ} (hx:0≤x) : x*Real.log (1/x)≤Real.sqrt x := by
  by_cases hz:x=0
  · simp [hz]
  have hp:0<x := lt_of_le_of_ne hx (Ne.symm hz)
  have hs:0<Real.sqrt x := Real.sqrt_pos.mpr hp
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0<1/(2*Real.sqrt x))
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  rw [Real.log_div (by norm_num) (by positivity),Real.log_one,
    Real.log_mul (by norm_num) hs.ne',Real.log_sqrt hx] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hx
  have hid : x/(2*Real.sqrt x) = Real.sqrt x/2 := by
    have hsq:=Real.sq_sqrt hx
    field_simp
    nlinarith
  simp only [mul_sub,mul_one,mul_zero,mul_one_div] at hm
  rw [hid] at hm
  rw [Real.log_div one_ne_zero hz,Real.log_one]
  have hm2 := mul_le_mul_of_nonneg_left hl2 hx
  nlinarith

lemma small_exit_sqrt_scaled {p h Ψ:ℝ} (hp:0≤p) (hh:0<h) (hΨ:1≤Ψ)
    (hb:p≤(10:ℝ)^(-20:ℤ)*(h/Ψ)^4) :
    Real.sqrt p*Ψ^2≤(10:ℝ)^(-10:ℤ)*h^2 := by
  have hΨp:0<Ψ := by linarith
  have hs : Real.sqrt p≤(10:ℝ)^(-10:ℤ)*(h/Ψ)^2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    calc
      _ ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := hb
      _ = ((10:ℝ)^(-10:ℤ)*(h/Ψ)^2)^2 := by norm_num; ring
  have ht:=mul_le_mul_of_nonneg_right hs (sq_nonneg Ψ)
  calc
    _ ≤ ((10:ℝ)^(-10:ℤ)*(h/Ψ)^2)*Ψ^2 := ht
    _ = _ := by field_simp

lemma comparison_cross_remainder {p h Ψ Q Ξ t W:ℝ}
    (hp:0≤p) (hh:0<h) (hΨ:1≤Ψ) (hQ:0≤Q) (hΞ:0≤Ξ) (hQΞ:Q+Ξ≤Ψ)
    (hb:p≤(10:ℝ)^(-20:ℤ)*(h/Ψ)^4)
    (ht0:0≤t) (ht:t≤(4.02:ℝ)*Ξ*Real.sqrt p)
    (hW0:0≤W) (hW:W≤(2.5:ℝ)*Real.sqrt Q) :
    (2/h)*Real.sqrt t*W ≤ (5.1:ℝ)*(10:ℝ)^(-5:ℤ) := by
  have hΨp:0<Ψ := by linarith
  have hs := small_exit_sqrt_scaled hp hh hΨ hb
  have ham:4*Q*Ξ≤Ψ^2 := by nlinarith [sq_nonneg (Q-Ξ)]
  have htQ := mul_le_mul_of_nonneg_right ht hQ
  have htΨ := mul_le_mul_of_nonneg_right htQ (sq_nonneg Ψ)
  have hsQ := mul_le_mul_of_nonneg_left hs (by positivity :0≤(4.02:ℝ)*Ξ*Q)
  have hamh := mul_le_mul_of_nonneg_right ham (by positivity :0≤(1.005:ℝ)*(10:ℝ)^(-10:ℤ)*h^2)
  have hcancel : (t*Q)*Ψ^2 ≤ ((1.005:ℝ)*(10:ℝ)^(-10:ℤ)*h^2)*Ψ^2 := by
    norm_num at hsQ hamh ⊢
    nlinarith
  have htQ' : t*Q≤(1.005:ℝ)*(10:ℝ)^(-10:ℤ)*h^2 :=
    (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hΨp)).mp hcancel
  have hprod : Real.sqrt t*Real.sqrt Q≤(1.02:ℝ)*(10:ℝ)^(-5:ℤ)*h := by
    have he1:=Real.sq_sqrt ht0
    have he2:=Real.sq_sqrt hQ
    have he:(Real.sqrt t*Real.sqrt Q)^2=t*Q := by rw [mul_pow,he1,he2]
    have hn:0≤Real.sqrt t*Real.sqrt Q := by positivity
    have hr:0≤(1.02:ℝ)*(10:ℝ)^(-5:ℤ)*h := by positivity
    norm_num at htQ' ⊢
    nlinarith
  calc
    _ ≤ (2/h)*Real.sqrt t*((2.5:ℝ)*Real.sqrt Q) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (5/h)*(Real.sqrt t*Real.sqrt Q) := by ring
    _ ≤ (5/h)*((1.02:ℝ)*(10:ℝ)^(-5:ℤ)*h) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by field_simp; norm_num

lemma comparison_entropy_bracket {p h Ψ Ξ K e:ℝ}
    (hp:0≤p) (hh:0<h) (hhmax:h≤1/8) (hΨ:1≤Ψ) (hΞ:0≤Ξ) (hΞΨ:Ξ≤Ψ)
    (hb:p≤(10:ℝ)^(-20:ℤ)*(h/Ψ)^4) (hK:K≤Ψ)
    (he:e≤(6.1:ℝ)*Ξ*Real.sqrt p) :
    3*p*Real.log (1/p)+2*p+p*K+e≤(10:ℝ)^(-9:ℤ) := by
  have hs := small_exit_sqrt_scaled hp hh hΨ hb
  have hw := OBABOPath.small_exit_weighted_sqrt hp hh hΨ hΞ hΞΨ hb
  have hΨp:0<Ψ := by linarith
  have hs0:=Real.sqrt_nonneg p
  have hs2:=Real.sq_sqrt hp
  have hΨ2:1≤Ψ^2 := by nlinarith
  have hsbase:Real.sqrt p≤(10:ℝ)^(-10:ℤ)*h^2 := by
    have ht:=mul_le_mul_of_nonneg_left hΨ2 hs0
    norm_num at hs ⊢
    nlinarith
  have hsmax:Real.sqrt p≤(10:ℝ)^(-10:ℤ)/64 := by
    have hh2:h^2≤1/64 := by nlinarith
    norm_num at hsbase ⊢
    nlinarith
  have hpmax:p≤Real.sqrt p := by norm_num at hsmax; nlinarith
  have hΨs:Ψ*Real.sqrt p≤(10:ℝ)^(-10:ℤ)*h^2 := by
    have ht:=mul_le_mul_of_nonneg_left (show Ψ≤Ψ^2 by nlinarith) hs0
    nlinarith
  have hΨpbound:p*Ψ≤(10:ℝ)^(-20:ℤ)/4096 := by
    have h1:Ψ*Real.sqrt p≤(10:ℝ)^(-10:ℤ)/64 := by
      have hh2:h^2≤1/64 := by nlinarith
      norm_num at hΨs ⊢
      nlinarith
    have ht:=mul_le_mul h1 hsmax hs0 (by positivity :0≤(10:ℝ)^(-10:ℤ)/64)
    norm_num at ht ⊢
    nlinarith
  have hemax:e≤(6.1:ℝ)*(10:ℝ)^(-10:ℤ)/64 := by
    have hh2:h^2≤1/64 := by nlinarith
    norm_num at hw ⊢
    nlinarith
  have hlog:=mul_log_inv_le_sqrt hp
  have hpk:=mul_le_mul_of_nonneg_left hK hp
  simp only [one_div,Real.log_inv] at hlog ⊢
  norm_num at hsmax hΨpbound hemax ⊢
  nlinarith

lemma comparison_remainder_arithmetic {p h Ψ Q Ξ t W K e A:ℝ}
    (hp:0≤p) (hh:0<h) (hhmax:h≤1/8) (hΨ:1≤Ψ)
    (hQ:0≤Q) (hΞ:0≤Ξ) (hQΞ:Q+Ξ≤Ψ)
    (hb:p≤(10:ℝ)^(-20:ℤ)*(h/Ψ)^4)
    (ht0:0≤t) (ht:t≤(4.02:ℝ)*Ξ*Real.sqrt p)
    (hW0:0≤W) (hW:W≤(2.5:ℝ)*Real.sqrt Q) (hK:K≤Ψ)
    (he:e≤(6.1:ℝ)*Ξ*Real.sqrt p) :
    A+(13/2:ℝ)*t+(2/h)*Real.sqrt t*W+
      7*(3*p*Real.log (1/p)+2*p+p*K+e) ≤ A+6*(10:ℝ)^(-5:ℤ) := by
  have hc := comparison_cross_remainder hp hh hΨ hQ hΞ hQΞ hb ht0 ht hW0 hW
  have hΞΨ:Ξ≤Ψ := by linarith
  have hbkt := comparison_entropy_bracket hp hh hhmax hΨ hΞ hΞΨ hb hK he
  have hw := OBABOPath.small_exit_weighted_sqrt hp hh hΨ hΞ hΞΨ hb
  have htmax:t≤(4.1:ℝ)*(10:ℝ)^(-10:ℤ) := by
    have hh2:h^2≤1 := by nlinarith
    norm_num at hw ⊢
    nlinarith
  norm_num at hc hbkt htmax ⊢
  linarith

lemma small_exit_le_exp_neg_one {p h Ψ:ℝ} (hp:0≤p) (hh:0<h)
    (hhmax:h≤1/8) (hΨ:1≤Ψ) (hb:p≤(10:ℝ)^(-20:ℤ)*(h/Ψ)^4) :
    p≤Real.exp (-1) := by
  have hs := small_exit_sqrt_scaled hp hh hΨ hb
  have hsq:=Real.sq_sqrt hp
  have hs0:=Real.sqrt_nonneg p
  have hΨ2:1≤Ψ^2 := by nlinarith
  have hsbase:=mul_le_mul_of_nonneg_left hΨ2 hs0
  have hpmax:p≤1/3 := by
    have hh2:h^2≤1 := by nlinarith
    norm_num at hs
    nlinarith
  apply hpmax.trans
  rw [Real.exp_neg]
  simpa only [one_div] using (one_div_le_one_div_of_le (Real.exp_pos 1) Real.exp_one_lt_three.le)


end PersistencePays
#print axioms PersistencePays.comparison_cross_remainder
#print axioms PersistencePays.comparison_entropy_bracket
