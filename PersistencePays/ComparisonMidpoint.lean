import PersistencePays.ComparisonFlightBounds
import PersistencePays.QuadraticDistance
import PersistencePays.GibbsTransportEntropy
import PersistencePays.ConditionalOU

/-! Actual midpoint position moments and transport bounds for the comparison
chain. These use genuine finite-moment couplings, not a hypothesized Wasserstein
estimate. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace QuadraticTransport

theorem wassersteinTwo_le_second_moments (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) :
    wassersteinTwo μ ν ≤ Real.sqrt (∫ x, ‖x‖^2 ∂(μ : Measure E))+
      Real.sqrt (∫ x, ‖x‖^2 ∂(ν : Measure E)) := by
  let π := optimalPlan μ ν
  have hπ := optimalPlan_optimal μ ν
  have hf : (π : Measure (E×E)).map Prod.fst=(μ:Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p:Measure E)) hπ.1.1
  have hs : (π : Measure (E×E)).map Prod.snd=(ν:Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p:Measure E)) hπ.1.2
  have hfirst : MemLp (fun z:E×E => z.1) 2 (π:Measure (E×E)) := by
    rw [←hf] at hμ
    exact (memLp_map_measure_iff (by fun_prop) measurable_fst.aemeasurable).mp hμ
  have hsecond : MemLp (fun z:E×E => z.2) 2 (π:Measure (E×E)) := by
    rw [←hs] at hν
    exact (memLp_map_measure_iff (by fun_prop) measurable_snd.aemeasurable).mp hν
  have ht := sqrt_integral_norm_add_le hfirst hsecond.neg
  simp only [Pi.neg_apply,norm_neg,←sub_eq_add_neg] at ht
  have hfi : (∫ z:E×E,‖z.1‖^2 ∂(π:Measure (E×E))) = ∫ x,‖x‖^2 ∂(μ:Measure E) := by
    rw [←hf,integral_map measurable_fst.aemeasurable (by fun_prop)]
  have hsi : (∫ z:E×E,‖z.2‖^2 ∂(π:Measure (E×E))) = ∫ x,‖x‖^2 ∂(ν:Measure E) := by
    rw [←hs,integral_map measurable_snd.aemeasurable (by fun_prop)]
  rw [hfi,hsi] at ht
  unfold wassersteinTwo
  rw [←hπ.2,squaredCost_toReal μ ν π hπ.1 hμ hν]
  exact ht

end QuadraticTransport

def flightMidpoint (g:E→E) (h:ℝ) (w:E×E) : E :=
  w.1+(h/2)•flightVelocity g h w

theorem A1.flightMidpoint_memLp {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    {μ:Measure (E×E)} [IsFiniteMeasure μ] {p:ℝ≥0∞} (hμ:MemLp id p μ) (h:ℝ) :
    MemLp (flightMidpoint (gradient U) h) p μ :=
  hμ.fst.add ((a.kick_memLp hμ (h/2)).snd.const_smul (h/2))

theorem A1.midpoint_norm_square {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (h:ℝ) (w:E×E) :
    ‖flightMidpoint (gradient U) h w‖^2 ≤ 4*U w.1+(h^2/2)*‖flightVelocity (gradient U) h w‖^2 := by
  have hx := a.quadratic_lower_at_minimizer w.1
  rw [hstar,hzero,sub_zero] at hx
  have hn := norm_add_le w.1 ((h/2)•flightVelocity (gradient U) h w)
  have hnorm : 0≤‖w.1+(h/2)•flightVelocity (gradient U) h w‖ := norm_nonneg _
  have hsum : 0≤‖w.1‖+‖(h/2)•flightVelocity (gradient U) h w‖ := by positivity
  have hsq := (sq_le_sq₀ hnorm hsum).mpr hn
  have hdiff := sq_nonneg (‖w.1‖-‖(h/2)•flightVelocity (gradient U) h w‖)
  have hs : ‖(h/2)•flightVelocity (gradient U) h w‖^2 =
      (h^2/4)*‖flightVelocity (gradient U) h w‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    ring
  unfold flightMidpoint
  nlinarith

theorem A1.midpoint_integral_bound {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (h:ℝ)
    (ν:Measure (E×E)) [IsProbabilityMeasure ν] (hν:MemLp id 2 ν) :
    (∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂ν) ≤
      4*(∫ w,U w.1 ∂ν)+(h^2/2)*(∫ w,‖flightVelocity (gradient U) h w‖^2 ∂ν) := by
  have hmid : Integrable (fun w => ‖flightMidpoint (gradient U) h w‖^2) ν :=
    (a.flightMidpoint_memLp hν h).integrable_norm_pow'
  have hf : Integrable (fun w => ‖flightVelocity (gradient U) h w‖^2) ν :=
    (a.kick_memLp hν (h/2)).snd.integrable_norm_pow'
  have hu : Integrable (fun w:E×E=>U w.1) ν := a.potential_integrable hν.fst
  have ht := integral_mono hmid ((hu.const_mul 4).add (hf.const_mul (h^2/2)))
    (a.midpoint_norm_square hstar hzero h)
  change _ ≤ ∫ w,4*U w.1+(h^2/2)*‖flightVelocity (gradient U) h w‖^2 ∂ν at ht
  rwa [integral_add (hu.const_mul 4) (hf.const_mul (h^2/2)),integral_const_mul,
    integral_const_mul] at ht

theorem phaseOU_position_integral (f:E→ℝ) (hf:Measurable f) (r σ:ℝ)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] :
    (∫ w:E×E,f w.1 ∂phaseOUKernel r σ ∘ₘ μ) = ∫ z:E×E,f z.1 ∂μ := by
  calc
    _ = ∫ x,f x ∂(phaseOUKernel r σ ∘ₘ μ).fst :=
      (integral_map (μ:=phaseOUKernel r σ ∘ₘ μ) measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x,f x ∂μ.fst := by rw [phaseOUKernel_fst r σ μ]
    _ = _ := integral_map (μ:=μ) measurable_fst.aemeasurable hf.aestronglyMeasurable

theorem A1.midpoint_second_moment {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (h r σ:ℝ)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ) :
    (∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂phaseOUKernel r σ ∘ₘ μ) ≤
      4*(∫ z,phaseEnergy U z ∂μ)+(h^2/2)*
        (∫ w,‖flightVelocity (gradient U) h w‖^2 ∂phaseOUKernel r σ ∘ₘ μ) := by
  have ht := a.midpoint_integral_bound hstar hzero h (phaseOUKernel r σ ∘ₘ μ)
    (phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ)
  rw [phaseOU_position_integral U a.twice_contDiff.continuous.measurable] at ht
  have huμ : Integrable (fun w:E×E=>U w.1) μ := a.potential_integrable hμ.fst
  have hub : (∫ z:E×E,U z.1 ∂μ) ≤ ∫ z,phaseEnergy U z ∂μ :=
    integral_mono huμ (a.phaseEnergy_integrable hμ) (fun z => by
      unfold phaseEnergy; rw [real_inner_self_eq_norm_sq]; nlinarith [sq_nonneg ‖z.2‖])
  linarith

def midpointProbability (g:E→E) (hg:Measurable g) (h:ℝ)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] : ProbabilityMeasure E :=
  ProbabilityMeasure.map (⟨μ,inferInstance⟩ : ProbabilityMeasure (E×E))
    (show Measurable (flightMidpoint g h) by unfold flightMidpoint flightVelocity; fun_prop).aemeasurable

theorem midpointProbability_coe (g:E→E) (hg:Measurable g) (h:ℝ)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] :
    (midpointProbability g hg h μ : Measure E)=μ.map (flightMidpoint g h) := rfl

theorem A1.midpoint_transport {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (h Q:ℝ) (hQ:0≤Q)
    (hd:25*(Module.finrank ℝ E:ℝ)≤Q)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hb:(∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂μ)≤(5.1:ℝ)*Q) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    QuadraticTransport.wassersteinTwo (midpointProbability (gradient U) hg h μ)
      a.gibbsProbability ≤ (2.5:ℝ)*Real.sqrt Q := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := midpointProbability (gradient U) hg h μ
  have hm : Measurable (flightMidpoint (gradient U) h) := by
    unfold flightMidpoint flightVelocity; fun_prop
  have hν : MemLp id 2 (ν:Measure E) := by
    change MemLp id 2 (μ.map (flightMidpoint (gradient U) h))
    exact (memLp_map_measure_iff (by fun_prop) hm.aemeasurable).mpr (a.flightMidpoint_memLp hμ h)
  have hi : (∫ x,‖x‖^2 ∂(ν:Measure E))=∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂μ :=
    integral_map hm.aemeasurable (by fun_prop)
  have ht := QuadraticTransport.wassersteinTwo_le_second_moments ν a.gibbsProbability hν
    a.position_memLp_two
  change QuadraticTransport.wassersteinTwo ν a.gibbsProbability≤
    Real.sqrt (∫ x,‖x‖^2 ∂(ν:Measure E))+Real.sqrt (∫ x,‖x‖^2 ∂positionGibbs U) at ht
  rw [hi] at ht
  have h1 : Real.sqrt (∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂μ)≤(2.26:ℝ)*Real.sqrt Q := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have he:=Real.sq_sqrt hQ
    nlinarith
  have h2 : Real.sqrt (∫ x:E,‖x‖^2 ∂positionGibbs U)≤(0.2:ℝ)*Real.sqrt Q := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have he:=Real.sq_sqrt hQ
    have hb:=a.position_norm_square_le_dim hstar hzero
    nlinarith
  have hsq:=Real.sqrt_nonneg Q
  change QuadraticTransport.wassersteinTwo ν a.gibbsProbability≤_
  linarith

namespace OBABOPath

theorem proposition_6_1_midpoint
    {U:E→ℝ} {L LH h vstar R Ψ:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hstar:a.minimizer=0) (hzero:U 0=0)
    (hh:0<h) (hL:h^2*L≤1/1000)
    (hv:0≤vstar) (hLH:0≤LH) (hscale:LH*h^3/12*vstar≤(0.02:ℝ)*h)
    (hR:0≤R) (hΨ:1≤Ψ) (N:ℕ) (hN:0<N)
    (hΞΨ:comparisonXi R (Module.finrank ℝ E) h N≤Ψ)
    (hd:41*((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50+20*Real.log (2*(N:ℝ))+
      80*Real.log (Ψ/h)+922)≤vstar^2)
    (z:E×E) (hz:phaseEnergy U z≤R) (n:ℕ) (hn:n+1≤N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μ := comparisonChainLaw (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar n z
    let ν := phaseOUKernel (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ∘ₘ μ
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50
    (∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂ν)≤(5.1:ℝ)*Q := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let μ := comparisonChainLaw (gradient U) hg h (Real.exp (-h))
    (Real.sqrt (1-Real.exp (-2*h))) vstar n z
  let ν := phaseOUKernel (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ∘ₘ μ
  let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50
  have hL' : h^2*L≤1/64 := by linarith
  have hh2 : h^2≤1/1000 := by
    have ht := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  have hμ := comparisonChainLaw_finite_moments a h (Real.exp (-h))
    (Real.sqrt (1-Real.exp (-2*h))) vstar n z 2 (by norm_num)
  have hm := a.midpoint_second_moment hstar hzero h (Real.exp (-h))
    (Real.sqrt (1-Real.exp (-2*h))) μ hμ
  have he := proposition_6_1_comparison_energy a a2 hstar hzero hh hL' hv hLH hscale hR
    hΨ N hN hΞΨ hd z hz n hn
  have hf := (proposition_6_1_comparison_flight a a2 hstar hzero hh hL' hv hLH hscale hR
    hΨ N hN hΞΨ hd z hz n hn).1
  change (∫ w,phaseEnergy U w ∂μ)≤(1.27:ℝ)*Q at he
  change (∫ w,‖flightVelocity (gradient U) h w‖^2 ∂ν)≤(2.61:ℝ)*Q at hf
  have hQ : 0≤Q := by unfold Q; positivity
  have hmulf := mul_le_mul_of_nonneg_left hf (by positivity : 0≤h^2/2)
  have hmulq := mul_le_mul_of_nonneg_right hh2 hQ
  change (∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂ν)≤
    4*(∫ z,phaseEnergy U z ∂μ)+(h^2/2)*(∫ w,‖flightVelocity (gradient U) h w‖^2 ∂ν) at hm
  change (∫ w,‖flightMidpoint (gradient U) h w‖^2 ∂ν)≤(5.1:ℝ)*Q
  nlinarith

end OBABOPath
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.wassersteinTwo_le_second_moments
#print axioms PersistencePays.OBABOPath.proposition_6_1_midpoint
