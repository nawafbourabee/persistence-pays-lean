import PersistencePays.ComparisonEnergy
import PersistencePays.PrefixExit

/-! Uniform first moments of the actual comparison chain under condition (d). -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def comparisonXi (R : ℝ) (d : ℕ) (h : ℝ) (N : ℕ) : ℝ :=
  (1.01:ℝ)*Real.exp ((0.081:ℝ)*((N:ℝ)*h))*(R+2*((d:ℝ)+2)*((N:ℝ)*h+1))

theorem comparisonXi_nonneg {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (d N : ℕ) :
    0 ≤ comparisonXi R d h N := by unfold comparisonXi; positivity

theorem comparisonChainLaw_modifiedEnergy_uniform
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E × E) (hz : phaseEnergy U z ≤ R) (n N : ℕ) (hn : n+1 ≤ N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    secondMomentNorm (comparisonChainLaw (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar n z) (modifiedEnergy U h) ≤
        comparisonXi R (Module.finrank ℝ E) h N := by
  dsimp only
  have hb := (a.lemma_5_11_moments a2 hstar hzero hL hh hLH hscale z hz n N hn).1
  have hR : 0 ≤ R := (a.normalized_energy_nonnegative hstar hzero z).trans hz
  have hn' : (n:ℝ)+1 ≤ N := by exact_mod_cast hn
  apply hb.trans
  unfold comparisonXi
  gcongr <;> nlinarith

/-- The energy estimate used in Section 6, for the literal comparison law.
Ψ is an explicit upper bound on Ξ and at least one; the theorem proves the
required small exceptional probability from condition (d). -/
theorem proposition_6_1_comparison_energy
    {U : E → ℝ} {L LH h vstar R Ψ : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 < h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (hΨ : 1 ≤ Ψ) (N : ℕ) (hN : 0 < N)
    (hΞΨ : comparisonXi R (Module.finrank ℝ E) h N ≤ Ψ)
    (hd : 41*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50+20*Real.log (2*(N:ℝ))+
      80*Real.log (Ψ/h)+922) ≤ vstar^2)
    (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) (hn : n+1 ≤ N) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    (∫ w, phaseEnergy U w ∂comparisonChainLaw (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h))) vstar n z) ≤
        (1.27:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50) := by
  dsimp only
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
  let p := (gaussianBlock (n+1)).real (stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z)ᶜ
  let Ξ := comparisonXi R (Module.finrank ℝ E) h N
  have hhsq : h^2 ≤ 1/64 := by
    have ht := mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
    nlinarith
  have hhmax : h ≤ 1/8 := by nlinarith
  have hhΨ : h ≤ Ψ := by linarith
  have he := proposition_6_1_exit a a2 hstar hzero hh hL hv hLH hscale hR hhΨ N hN hd z hz
  have hp := (stopped_prefix_exit_le a h r σ vstar hn z).trans he
  have hp' : p ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    have hpos : 0 ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := by positivity
    rw [ENNReal.toReal_ofReal hpos] at ht
    exact ht
  have herr : Ξ*Real.sqrt p ≤ (10:ℝ)^(-10:ℤ)*h^2 := small_exit_weighted_sqrt
    (measureReal_nonneg : 0 ≤ p) hh hΨ (comparisonXi_nonneg hR hh.le _ _) hΞΨ hp'
  have hnorm := comparisonChainLaw_modifiedEnergy_uniform a a2 hstar hzero hh hL hLH hscale z hz n N hn
  have hmoment := comparison_energy_exceptional a a2 hstar hzero hh.le hL hv hLH hscale hR z hz n
  change secondMomentNorm μ (modifiedEnergy U h) ≤ Ξ at hnorm
  change (∫ w, phaseEnergy U w ∂μ) ≤ (1.266:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50)+
    (1.005:ℝ)*secondMomentNorm μ (modifiedEnergy U h)*Real.sqrt p at hmoment
  have hm := mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg p)
  norm_num at herr
  have hd0 := (Nat.cast_nonneg (Module.finrank ℝ E) : (0:ℝ) ≤ Module.finrank ℝ E)
  nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1_comparison_energy
