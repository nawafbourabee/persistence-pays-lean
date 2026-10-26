import PersistencePays.PropositionFiveTen
import PersistencePays.ComparisonDefectUniform
import PersistencePays.StartingEntropySectionSix
import PersistencePays.ComparisonTVClosure

/-! Actual relative-entropy closure of Proposition 6.1. All density, moment,
exceptional-event and numerical error premises of Proposition 5.10 are proved
for the literal cold-start comparison chain. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 800000

theorem proposition_6_1_comparison_entropy
    {U:E→ℝ} {L LH h vstar R Ψ:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hsm:GaussianSmoothedFreeTransportBound a)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0<h) (hL:h^2*L≤1/1000)
    (hv:0≤vstar) (hLH:0≤LH) (hscale:LH*h^3/12*vstar≤(0.02:ℝ)*h)
    (hR:0≤R) (n:ℕ)
    (hΨsum:comparisonXi R (Module.finrank ℝ E) h (n+1)+
      ((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50)≤Ψ)
    (hΨlog:(Module.finrank ℝ E:ℝ)*Real.log (1/h^2)+
      2*(Module.finrank ℝ E:ℝ)*((n+1:ℕ):ℝ)*h≤Ψ)
    (hd:41*((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50+20*Real.log (2*((n+1:ℕ):ℝ))+
      80*Real.log (Ψ/h)+922)≤vstar^2)
    (ha:h^2*L*((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50)≤1/5000)
    (hb:LH*h^2*((6.6:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50))^(3/2:ℝ)≤1/1000)
    (hc:(Real.exp (-h))^2/(4*(16+Real.exp (-h)))*h*(n:ℝ)≥
      Real.log (227*((1.02:ℝ)*R+(Module.finrank ℝ E:ℝ)*Real.log (1/h^2))))
    (z:E×E) (hz:phaseEnergy U z≤R) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    (klDiv (comparisonChainLaw (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar n z) (phaseGibbs U)).toReal≤(0.0218:ℝ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r:=Real.exp (-h)
  let σ:=Real.sqrt (1-Real.exp (-2*h))
  let rate:=r^2/(4*(16+r))
  let Q:=(1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50
  let M:=((6.6:ℝ)*Q)^(3/2:ℝ)
  let D:=comparisonDensityCap (Module.finrank ℝ E) (n+1) h σ
  let T:=LH*h^3/12*M+(10:ℝ)^(-11:ℤ)*h
  let B:=(13/4:ℝ)*(h^2*L)*((2.61:ℝ)*Q)+6*(10:ℝ)^(-5:ℤ)
  let p:=fun k=>comparisonChainLaw (gradient U) hg h r σ vstar k z
  let q:=fun k=>phaseOUKernel r σ ∘ₘ p k
  let A:=(1.02:ℝ)*R+(Module.finrank ℝ E:ℝ)*Real.log (1/h^2)
  have hQ:0≤Q := by dsimp [Q]; positivity
  have hM:0≤M := Real.rpow_nonneg (by positivity) _
  have hT:0≤T := by dsimp [T]; positivity
  have hB:0≤B := by dsimp [B]; positivity [a.L_pos]
  have hL':h^2*L≤1/64 := by linarith
  have hhsq:=mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
  have hmax:h≤1/8 := by nlinarith
  have hσ:0<σ := Real.sqrt_pos.mpr (by
    have he:=Real.exp_lt_one_iff.mpr (show -2*h<0 by linarith)
    linarith)
  have hD:0<D := comparisonDensityCap_pos hh hσ _ _
  have hΞ:=comparisonXi_nonneg hR hh.le (Module.finrank ℝ E) (n+1)
  have hQ50:50≤Q := by dsimp [Q]; nlinarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0:ℝ)≤Module.finrank ℝ E)]
  have hΨ:1≤Ψ := by change comparisonXi R (Module.finrank ℝ E) h (n+1)+Q≤Ψ at hΨsum; linarith
  have hΞΨ:comparisonXi R (Module.finrank ℝ E) h (n+1)≤Ψ := by linarith
  have herr (k:ℕ) (hk:k<n) := proposition_6_1_remainder a a2 hstar hzero hh hL hv hLH hscale
    hR (n+1) (by omega) hΨsum (by simpa only [mul_assoc] using hΨlog) hd z hz k (by omega)
  have hcap (k:ℕ) (hk:k<n) : q k≤ENNReal.ofReal D • ((volume:Measure E).prod volume) := by
    obtain ⟨f,hf,he,hfbound⟩ := (herr k hk).1
    change q k=((volume:Measure E).prod volume).withDensity f at he
    rw [he,←withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall hfbound)
  have hα (k:ℕ) (hk:k<n) : ((q k) {w|vstar<‖flightVelocity (gradient U) h w‖}).toReal<1 :=
    ((herr k hk).2.1).trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have hTb (k:ℕ) (hk:k<n) : (∫w,max (comparisonDefect U (gradient U) h vstar w) 0∂q k)≤T :=
    proposition_6_1_comparison_defect a a2 hstar hzero hh hL' hv hLH hscale hR hΨ
      (n+1) (by omega) hΞΨ hd z hz k (by omega)
  have hBb (k:ℕ) (hk:k<n) : a.comparisonRemainder h vstar D (q k)≤B := by
    have hrm: a.comparisonRemainder h vstar D (q k)≤
      (13/4:ℝ)*(h^2*L)*(∫w,‖flightVelocity (gradient U) h w‖^2∂q k)+6*(10:ℝ)^(-5:ℤ) :=
      (herr k hk).2.2
    have hflight := (proposition_6_1_comparison_flight a a2 hstar hzero hh hL' hv hLH hscale hR hΨ
      (n+1) (by omega) hΞΨ hd z hz k (by omega)).1
    apply hrm.trans
    change (13/4:ℝ)*(h^2*L)*(∫w,‖flightVelocity (gradient U) h w‖^2∂q k)+6*(10:ℝ)^(-5:ℤ)≤B
    exact add_le_add_left (mul_le_mul_of_nonneg_left hflight (show 0≤(13/4:ℝ)*(h^2*L) by positivity [a.L_pos])) _
  have hdecay:=a.proposition_5_10 hsm hstar hzero hh hmax (by nlinarith) z D vstar T B hD hT hB n
    hcap hα hTb hBb
  have he:=proposition_6_1_comparison_energy a a2 hstar hzero hh hL' hv hLH hscale hR hΨ
    (n+1) (by omega) hΞΨ hd z hz n (by omega)
  have hp2:MemLp id 2 (p n) := comparisonChainLaw_finite_moments a h r σ vstar n z 2 (by norm_num)
  have hu:(∫w,U w.1∂p n)≤(1.27:ℝ)*Q := by
    apply (integral_mono (a.potential_integrable hp2.fst) (a.phaseEnergy_integrable hp2)
      (fun w=>by rw [phaseEnergy_eq_norm]; exact le_add_of_nonneg_right (by positivity))).trans he
  obtain ⟨hrate,hinv,_⟩ := comparison_entropy_rate_constants hh hmax
  have hrem:=comparison_entropy_remainder_constants hQ hh a.L_pos.le hLH hM hrate hinv hu
    (show (2.61:ℝ)*Q≤(2.61:ℝ)*Q from le_rfl) (show B≤B from le_rfl) hT (show T≤T from le_rfl)
  have hinit: (klDiv (unadjustedStepKernel (gradient U) hg h r σ z) (phaseGibbs U)).toReal≤A :=
    (a.proposition_6_1_start_entropy hstar hzero hh hL' z hz).2
  have hlog:0≤Real.log (1/h^2) := Real.log_nonneg ((one_le_div (sq_pos_of_pos hh)).mpr (by nlinarith))
  have hA:0≤A := by dsimp [A]; positivity
  have hinitmul:=mul_le_mul_of_nonneg_left hinit
    (show 0≤(17/15:ℝ)*Real.exp (-rate*h*(n:ℝ)) by positivity)
  apply comparison_entropy_numeric (A:=A) (T:=h*(n:ℝ)) (X:=h^2*L*Q) (Y:=LH*h^2*M) (rate:=rate)
    hA (by change rate*h*(n:ℝ)≥Real.log (227*A) at hc; nlinarith) ha hb
  change (klDiv (p n) (phaseGibbs U)).toReal≤_
  change (klDiv (p n) (phaseGibbs U)).toReal≤
    (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*
      (klDiv (unadjustedStepKernel (gradient U) hg h r σ z) (phaseGibbs U)).toReal+
      (16/15:ℝ)*(h^2*L/4*(∫w,U w.1∂p n)+T/(rate*h)+(4.79:ℝ)*B) at hdecay
  change h^2*L/4*(∫w,U w.1∂p n)+(1/(rate*h))*T+(4.79:ℝ)*B≤
    (40.95:ℝ)*(h^2*L)*Q+(7.234:ℝ)*LH*h^2*M+3*(10:ℝ)^(-4:ℤ) at hrem
  have hexp : -rate*(h*(n:ℝ)) = -rate*h*(n:ℝ) := by ring
  rw [hexp]
  rw [div_eq_mul_inv T] at hdecay
  rw [one_div] at hrem
  nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_comparison_entropy
