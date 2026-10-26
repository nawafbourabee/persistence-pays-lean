import PersistencePays.ComparisonRemainder
import PersistencePays.AdjustedPairCoupling

/-! The final actual-law total-variation comparison, conditional only on the
stated entropy estimate whose derivation is handled by the corrector argument. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem proposition_6_1_TV_of_comparison_entropy
    {U:E→ℝ} {L LH h vstar R Ψ:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0<h) (hL:h^2*L≤1/64)
    (hv:0≤vstar) (hLH:0≤LH) (hscale:LH*h^3/12*vstar≤(0.02:ℝ)*h)
    (hR:0≤R) (hΨ:h≤Ψ) (n:ℕ)
    (hd:41*((1.2:ℝ)*R+27*(Module.finrank ℝ E:ℝ)+50+20*Real.log (2*((n+1:ℕ):ℝ))+
      80*Real.log (Ψ/h)+922)≤vstar^2)
    (z:E×E) (hz:phaseEnergy U z≤R)
    (hEntropy:
      let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      (klDiv (comparisonChainLaw (gradient U) hg h (Real.exp (-h))
        (Real.sqrt (1-Real.exp (-2*h))) vstar n z) (phaseGibbs U)).toReal≤(0.0218:ℝ)) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    probabilityTV (unadjustedEpochKernel (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) (n+1) z) (phaseGibbs U)≤ENNReal.ofReal (0.105:ℝ) := by
  dsimp only at hEntropy ⊢
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r:=Real.exp (-h)
  let σ:=Real.sqrt (1-Real.exp (-2*h))
  let ν:=comparisonChainLaw (gradient U) hg h r σ vstar n z
  let μ:=unadjustedEpochKernel (gradient U) hg h r σ (n+1) z
  letI:IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  letI:IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  have hc:=normalized_ou_coefficients h hh.le
  have hnorm:r^2+σ^2=1 := hc.2.2.2.1
  have hr:r^2≤1 := by nlinarith [sq_nonneg σ]
  have hσ:0<σ := by
    apply Real.sqrt_pos.mpr
    have he:Real.exp (-2*h)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hfinite:klDiv ν (phaseGibbs U)≠∞ :=
    comparisonChainLaw_entropy_finite a h r σ vstar hh hσ hnorm n z
  have hpin:=pinsker_probabilityTV ν (phaseGibbs U) hfinite
  have hcompare:=comparison_chain_TV_bound (σ:=σ) a hstar hzero hL hr hv n z
  have hexit:=proposition_6_1_exit a a2 hstar hzero hh hL hv hLH hscale hR hΨ
    (n+1) (by omega) hd z hz
  have hsmall:probabilityTV μ ν≤ENNReal.ofReal ((10:ℝ)^(-20:ℤ)) := by
    apply (hcompare.trans hexit).trans
    apply ENNReal.ofReal_le_ofReal
    have hp:0≤h/Ψ := div_nonneg hh.le (hh.trans_le hΨ).le
    have hp1:h/Ψ≤1 := (div_le_one (hh.trans_le hΨ)).mpr hΨ
    have hp4:(h/Ψ)^4≤1 := pow_le_one₀ hp hp1
    nlinarith [mul_le_mul_of_nonneg_left hp4 (by positivity :0≤(10:ℝ)^(-20:ℤ))]
  have hroot:Real.sqrt ((klDiv ν (phaseGibbs U)).toReal/2)≤(0.1045:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    change (klDiv ν (phaseGibbs U)).toReal≤(0.0218:ℝ) at hEntropy
    nlinarith
  have hpins:probabilityTV ν (phaseGibbs U)≤ENNReal.ofReal (0.1045:ℝ) :=
    hpin.trans (ENNReal.ofReal_le_ofReal hroot)
  calc
    _ ≤ probabilityTV μ ν+probabilityTV ν (phaseGibbs U) := probabilityTV_triangle _ _ _
    _ ≤ ENNReal.ofReal ((10:ℝ)^(-20:ℤ))+ENNReal.ofReal (0.1045:ℝ) := add_le_add hsmall hpins
    _ ≤ ENNReal.ofReal (0.105:ℝ) := by
      rw [←ENNReal.ofReal_add (by positivity) (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_TV_of_comparison_entropy
