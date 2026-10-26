import PersistencePays.StartingEnergy

/-! The normalized actual cold-start entropy bound used in Proposition 6.1. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma starting_log_bound {h:ℝ} (hh:0<h) (hmax:h≤1/8) :
    Real.log ((2*Real.exp 1*h^2*(1-h))⁻¹)≤Real.log (1/h^2)-1 := by
  have hb:0<2*(1-h) := by linarith
  have hl:0≤Real.log (2*(1-h)) := Real.log_nonneg (by linarith)
  have he:2*Real.exp 1*h^2*(1-h)=(2*(1-h))*Real.exp 1*h^2 := by ring
  rw [he,Real.log_inv,Real.log_mul (by positivity) (by positivity),
    Real.log_mul hb.ne' (Real.exp_ne_zero _),Real.log_exp,
    Real.log_div one_ne_zero (by positivity),Real.log_one]
  linarith

theorem A1.proposition_6_1_start_entropy {U:E→ℝ} {L h R:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0<h) (hL:h^2*L≤1/64)
    (z:E×E) (hz:phaseEnergy U z≤R) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let K := OBABOPath.unadjustedStepKernel (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h)))
    klDiv (K z) (phaseGibbs U) ≠ ∞ ∧
      (klDiv (K z) (phaseGibbs U)).toReal ≤
        (1.02:ℝ)*R+(Module.finrank ℝ E:ℝ)*Real.log (1/h^2) := by
  dsimp only
  have hhsq:=mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
  have hmax:h≤1/8 := by nlinarith
  have he:=a.unadjusted_start_energy hstar hzero hh hL z hz
  have hst:Real.sqrt (1:ℝ)*h<1 := by simp only [Real.sqrt_one,one_mul]; linarith
  have hk:=a.lemma_4_14 h hh hst z
  simp only [Real.sqrt_one,one_mul,mul_one,hstar,hzero,sub_zero] at hk
  refine ⟨hk.1,?_⟩
  have hlog:=mul_le_mul_of_nonneg_left (starting_log_bound hh hmax)
    (Nat.cast_nonneg (Module.finrank ℝ E):(0:ℝ)≤_)
  have hb:=hk.2.1
  dsimp only at he
  have hd:0≤(Module.finrank ℝ E:ℝ) := by positivity
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.proposition_6_1_start_entropy
