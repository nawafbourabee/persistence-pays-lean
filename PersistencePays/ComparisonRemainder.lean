import PersistencePays.ComparisonMidpoint
import PersistencePays.ComparisonTailMoments
import PersistencePays.ComparisonDensityLog
import PersistencePays.ComparisonErrorArithmetic

/-! The literal remainder of Proposition 5.9, with an actual everywhere density
cap, and its Section 6 bound for the actual finite comparison chain. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 800000

def A1.comparisonRemainder {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (h vstar C:ℝ) (μ:Measure (E×E)) [IsProbabilityMeasure μ] : ℝ :=
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let F := {w:E×E | vstar<‖flightVelocity (gradient U) h w‖}
  let α := μ.real F
  (13/4:ℝ)*(h^2*L)*(∫ w,‖flightVelocity (gradient U) h w‖^2 ∂μ)+
    (13/2:ℝ)*(∫ w in F,‖flightVelocity (gradient U) h w‖^2 ∂μ)+
    (2/h)*Real.sqrt (∫ w in F,‖flightVelocity (gradient U) h w‖^2 ∂μ)*
      QuadraticTransport.wassersteinTwo (midpointProbability (gradient U) hg h μ) a.gibbsProbability+
    7*(3*α*Real.log (1/α)+2*α+α*max (Real.log C) 0+
      α*(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)+
      (∫ w in F,2*U w.1+‖flightVelocity (gradient U) h w‖^2 ∂μ))

namespace OBABOPath

theorem proposition_6_1_remainder
    {U:E→ℝ} {L LH h vstar R Ψ:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hstar:a.minimizer=0) (hzero:U 0=0)
    (hh:0<h) (hL:h^2*L≤1/1000)
    (hv:0≤vstar) (hLH:0≤LH) (hscale:LH*h^3/12*vstar≤(0.02:ℝ)*h)
    (hR:0≤R) (N:ℕ) (hN:0<N)
    (hΨsum:comparisonXi R (Module.finrank ℝ E) h N+
      ((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50)≤Ψ)
    (hΨlog:(Module.finrank ℝ E:ℝ)*Real.log (1/h^2)+
      2*(Module.finrank ℝ E:ℝ)*((N:ℝ)*h)≤Ψ)
    (hd:41*((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50+20*Real.log (2*(N:ℝ))+
      80*Real.log (Ψ/h)+922)≤vstar^2)
    (z:E×E) (hz:phaseEnergy U z≤R) (n:ℕ) (hn:n+2≤N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
    let ν := phaseOUKernel r σ ∘ₘ μ
    let C := comparisonDensityCap (Module.finrank ℝ E) N h σ
    let F := {w:E×E | vstar<‖flightVelocity (gradient U) h w‖}
    (∃f:E×E→ℝ≥0∞,Measurable f ∧ ν=((volume:Measure E).prod volume).withDensity f ∧
      ∀w,f w≤ENNReal.ofReal C) ∧ ν.real F≤Real.exp (-1) ∧
      a.comparisonRemainder h vstar C ν ≤
        (13/4:ℝ)*(h^2*L)*(∫ w,‖flightVelocity (gradient U) h w‖^2 ∂ν)+6*(10:ℝ)^(-5:ℤ) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
  let ν := phaseOUKernel r σ ∘ₘ μ
  let C := comparisonDensityCap (Module.finrank ℝ E) N h σ
  let F := {w:E×E | vstar<‖flightVelocity (gradient U) h w‖}
  let α := ν.real F
  let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50
  let Ξ := comparisonXi R (Module.finrank ℝ E) h N
  let W := QuadraticTransport.wassersteinTwo (midpointProbability (gradient U) hg h ν) a.gibbsProbability
  let t := ∫ w in F,‖flightVelocity (gradient U) h w‖^2 ∂ν
  let e := ∫ w in F,2*U w.1+‖flightVelocity (gradient U) h w‖^2 ∂ν
  have hL':h^2*L≤1/64 := by linarith
  have hhsq:h^2≤1/1000 := by
    have ht:=mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  have hmax:h≤1/8 := by nlinarith
  have hΞ:0≤Ξ := comparisonXi_nonneg hR hh.le _ _
  have hd0:0≤(Module.finrank ℝ E:ℝ) := by positivity
  have hQ:50≤Q := by unfold Q; nlinarith
  have hsum:Ξ+Q≤Ψ := hΨsum
  have hΨ:1≤Ψ := by linarith
  have hΞΨ:Ξ≤Ψ := by linarith
  have hμ4:MemLp id 4 μ := comparisonChainLaw_finite_moments a h r σ vstar n z 4 (by norm_num)
  have hν4:MemLp id 4 ν := phaseOUKernel_memLp μ 4 (by norm_num) hμ4 r σ
  have hν2:MemLp id 2 ν := hν4.mono_exponent (by norm_num)
  have hF:MeasurableSet F := measurableSet_lt measurable_const (by unfold flightVelocity; fun_prop)
  have hp : α≤(10:ℝ)^(-20:ℤ)*(h/Ψ)^4 :=
    (proposition_6_1_cutoff_moments a a2 hstar hzero hh hL' hv hLH hscale hR hΨ N hN
      hΞΨ hd z hz n hn).1
  have hα:0≤α := measureReal_nonneg
  have hcap:=comparison_pre_density_with_log (gradient U) hg h vstar hh hmax z n N (by omega)
  change 0<C ∧ (∃f:E×E→ℝ≥0∞,Measurable f ∧ ν=((volume:Measure E).prod volume).withDensity f ∧
      ∀w,f w≤ENNReal.ofReal C) ∧
    max (Real.log C) 0+(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)≤_ at hcap
  refine ⟨hcap.2.1,small_exit_le_exp_neg_one hα hh hmax hΨ hp,?_⟩
  have htail:=a.cutoff_set_moments hstar hzero hL' ν hν4 F hF
  have hnorm:secondMomentNorm ν (modifiedEnergy U h)≤Ξ :=
    (a.lemma_5_11_moments a2 hstar hzero hL' hh hLH hscale z hz n N (by omega)).2
  have hprod:=mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg α)
  have ht:t≤(4.02:ℝ)*Ξ*Real.sqrt α := by
    have hb:=htail.1
    change t≤(4.02:ℝ)*secondMomentNorm ν (modifiedEnergy U h)*Real.sqrt α at hb
    nlinarith
  have he:e≤(6.1:ℝ)*Ξ*Real.sqrt α := by
    have hb:=htail.2
    change e≤(6.1:ℝ)*secondMomentNorm ν (modifiedEnergy U h)*Real.sqrt α at hb
    nlinarith
  have ht0:0≤t := integral_nonneg (fun w=>sq_nonneg ‖flightVelocity (gradient U) h w‖)
  have hmid:(∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂ν)≤(5.1:ℝ)*Q :=
    proposition_6_1_midpoint a a2 hstar hzero hh hL hv hLH hscale hR hΨ N hN hΞΨ hd z hz n (by omega)
  have hdQ:25*(Module.finrank ℝ E:ℝ)≤Q := by unfold Q; nlinarith
  have hW:W≤(2.5:ℝ)*Real.sqrt Q := a.midpoint_transport hstar hzero h Q (by linarith) hdQ ν hν2 hmid
  have hW0:0≤W := Real.sqrt_nonneg _
  have hK:max (Real.log C) 0+(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)≤Ψ :=
    hcap.2.2.trans hΨlog
  have hb:=comparison_remainder_arithmetic (A:=(13/4:ℝ)*(h^2*L)*
    (∫ w,‖flightVelocity (gradient U) h w‖^2 ∂ν)) hα hh hmax hΨ (by linarith) hΞ
    (by linarith) hp ht0 ht hW0 hW hK he
  change a.comparisonRemainder h vstar C ν≤_
  unfold A1.comparisonRemainder
  dsimp only
  convert hb using 1 <;> dsimp [α,t,e,W,F] <;> ring

end OBABOPath
end PersistencePays
#print axioms PersistencePays.OBABOPath.proposition_6_1_remainder
