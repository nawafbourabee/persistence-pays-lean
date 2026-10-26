import PersistencePays.SectionSixEntropy
import PersistencePays.EpochParameters
import PersistencePays.RejectionClosure

/-! The normalized explicit conditions of Proposition 6.1, with actual kernel
and rejection conclusions and no moment, density or entropy hypotheses. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

structure NormalizedEpochConditions (L LH h vstar R:ℝ) (d n:ℕ) : Prop where
  step_pos : 0<h
  radius_nonneg : 0≤R
  cutoff_nonneg : 0≤vstar
  hessian_nonneg : 0≤LH
  scale : LH*h^3/12*vstar≤(0.02:ℝ)*h
  condition_a : h^2*L*(comparisonQ R d+20*Real.log (100*((n+1:ℕ)+1:ℝ)))≤1/5000
  condition_b : LH*h^2*((6.6:ℝ)*comparisonQ R d)^(3/2:ℝ)*(1+((n+1:ℕ):ℝ)*h)≤1/1000
  condition_c : (Real.exp (-h))^2/(4*(16+Real.exp (-h)))*h*(n:ℝ)≥
    Real.log (227*((1.02:ℝ)*R+(d:ℝ)*Real.log (1/h^2)))
  condition_d : 41*(comparisonQ R d+20*Real.log (2*((n+1:ℕ):ℝ))+
    80*Real.log (comparisonPsi R d h (n+1)/h)+922)≤vstar^2

variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem proposition_6_1_local {U:E→ℝ} {L LH h vstar R:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hsm:GaussianSmoothedFreeTransportBound a) (hstar:a.minimizer=0) (hzero:U 0=0)
    (n:ℕ) (c:NormalizedEpochConditions L LH h vstar R (Module.finrank ℝ E) n)
    (z:E×E) (hz:phaseEnergy U z≤R) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let r:=Real.exp (-h)
    let σ:=Real.sqrt (1-Real.exp (-2*h))
    probabilityTV (unadjustedEpochKernel (gradient U) hg h r σ (n+1) z) (phaseGibbs U)≤ENNReal.ofReal (0.105:ℝ) ∧
      epochRejectionProbability U (gradient U) h r σ (n+1) z≤ENNReal.ofReal (0.0102:ℝ) := by
  let d:=Module.finrank ℝ E
  let Q:=comparisonQ R d
  let Ψ:=comparisonPsi R d h (n+1)
  have hh:=c.step_pos
  have hR:=c.radius_nonneg
  have hv:=c.cutoff_nonneg
  have hLH:=c.hessian_nonneg
  have hscale:=c.scale
  have hstep:=condition_a_step_bounds hR a.m_le_L hh d (n+1) c.condition_a
  have hmax:h≤1/8 := by linarith [hstep.2.1]
  have hL:h^2*L≤1/1000 := by linarith [hstep.1]
  have hQ:=comparisonQ_ge_fifty hR d
  have hΞ:=comparisonXi_nonneg hR hh.le d (n+1)
  have hlog:0≤Real.log (1/h^2) := Real.log_nonneg ((one_le_div (sq_pos_of_pos hh)).mpr (by nlinarith))
  have hlogTerm:0≤(d:ℝ)*Real.log (1/h^2)+2*(d:ℝ)*((n+1:ℕ):ℝ)*h := by positivity
  have hsum:comparisonXi R d h (n+1)+Q≤Ψ := by dsimp [Ψ,comparisonPsi,Q]; nlinarith
  have hlogΨ:(d:ℝ)*Real.log (1/h^2)+2*(d:ℝ)*((n+1:ℕ):ℝ)*h≤Ψ := by
    dsimp [Ψ,comparisonPsi,Q]; nlinarith
  have hΨ:1≤Ψ := by change comparisonXi R d h (n+1)+Q≤Ψ at hsum; linarith
  have hsmall:h/Ψ≤1 := (div_le_one (by linarith :0<Ψ)).mpr (by linarith)
  have hpow:(h/Ψ)^4≤1 := pow_le_one₀ (by positivity) hsmall
  have ha:h^2*L*Q≤1/5000 := by
    have hlogN:0≤Real.log (100*(((n+1:ℕ):ℝ)+1)) := Real.log_nonneg (by have hn:0≤((n+1:ℕ):ℝ):=Nat.cast_nonneg _; nlinarith)
    have hprod:0≤h^2*L*(20*Real.log (100*(((n+1:ℕ):ℝ)+1))) := by positivity [a.L_pos]
    have hb:=c.condition_a
    change h^2*L*(Q+20*Real.log (100*(((n+1:ℕ):ℝ)+1)))≤1/5000 at hb
    nlinarith
  have hb:LH*h^2*((6.6:ℝ)*Q)^(3/2:ℝ)≤1/1000 := by
    have hprod:0≤LH*h^2*((6.6:ℝ)*Q)^(3/2:ℝ)*(((n+1:ℕ):ℝ)*h) := by positivity
    have ht:=c.condition_b
    change LH*h^2*((6.6:ℝ)*Q)^(3/2:ℝ)*(1+((n+1:ℕ):ℝ)*h)≤1/1000 at ht
    nlinarith
  have hEntropy:=proposition_6_1_comparison_entropy a a2 hsm hstar hzero hh hL hv hLH hscale hR n
    hsum hlogΨ c.condition_d ha hb c.condition_c z hz
  have hTV:=proposition_6_1_TV_of_comparison_entropy a a2 hstar hzero hh hstep.2.2 hv hLH hscale hR
    (show h≤Ψ by linarith) n c.condition_d z hz hEntropy
  have hex:=proposition_6_1_exit a a2 hstar hzero hh hstep.2.2 hv hLH hscale hR
    (show h≤Ψ by linarith) (n+1) (by omega) c.condition_d z hz
  have hexit : gaussianBlock (n+1) (stoppedBlockEvent U (gradient U) h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar (n+1) z)ᶜ≤ENNReal.ofReal (1/100000:ℝ) := by
    apply hex.trans
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hpow])
  have hre:=proposition_6_1_rejection a a2 hstar hzero hh.le hstep.2.2 hv hLH hscale hR z hz
    (n+1) (by omega) c.condition_a c.condition_b hexit
  refine ⟨hTV,?_⟩
  rw [←ENNReal.ofReal_toReal (show epochRejectionProbability U (gradient U) h (Real.exp (-h))
    (Real.sqrt (1-Real.exp (-2*h))) (n+1) z≠∞ by unfold epochRejectionProbability; finiteness)]
  exact ENNReal.ofReal_le_ofReal hre

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_local
