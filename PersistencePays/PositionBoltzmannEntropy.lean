import PersistencePays.PhaseGibbsDensity
import PersistencePays.KickEntropy

/-! Genuine Lebesgue-density entropy, identified with the finite Gibbs KL formula. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Boltzmann entropy ∫ log(dν/dx) dν. All identities below explicitly
prove integrability of this logarithm before using its real integral. -/
def boltzmannEntropy (ν : Measure E) : ℝ :=
  ∫ x, Real.log ((ν.rnDeriv volume x).toReal) ∂ν

theorem gibbs_boltzmann_identity (U : E → ℝ)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hU : Integrable U ν) (hK : klDiv ν (positionGibbs U) ≠ ∞) :
    Integrable (fun x => Real.log ((ν.rnDeriv volume x).toReal)) ν ∧
    boltzmannEntropy ν = (klDiv ν (positionGibbs U)).toReal -
      (∫ x, U x ∂ν) - Real.log (∫ x, Real.exp (-U x)) := by
  let π := positionGibbs U
  letI : IsProbabilityMeasure π := isProbabilityMeasure_tilted hi
  have hνπ : ν ≪ π := (klDiv_ne_top_iff.mp hK).1
  have ha : ν ≪ (volume : Measure E) := hνπ.trans (tilted_absolutelyContinuous volume (-U))
  have hZ : 0 < ∫ x, Real.exp (-U x) := integral_exp_pos hi
  have hr := toReal_rnDeriv_tilted_right ν (volume : Measure E) hi
  have he : (fun x => Real.log ((ν.rnDeriv volume x).toReal)) =ᵐ[ν]
      fun x => llr ν π x - U x - Real.log (∫ y, Real.exp (-U y)) := by
    filter_upwards [ha.ae_le hr, Measure.rnDeriv_pos ha,
      ha.ae_le (Measure.rnDeriv_ne_top ν volume)] with x hx hpos hfin
    have hp : 0 < (ν.rnDeriv volume x).toReal := ENNReal.toReal_pos (ne_of_gt hpos) hfin
    simp only [neg_neg] at hx
    change (ν.rnDeriv π x).toReal = Real.exp (U x) * (∫ y, Real.exp (-U y)) *
      (ν.rnDeriv volume x).toReal at hx
    unfold llr
    rw [hx, Real.log_mul (mul_pos (Real.exp_pos _) hZ).ne' hp.ne',
      Real.log_mul (Real.exp_ne_zero _) hZ.ne', Real.log_exp]
    ring
  have hllr := (klDiv_ne_top_iff.mp hK).2
  have hint := ((hllr.sub hU).sub (integrable_const (Real.log (∫ y, Real.exp (-U y))))).congr he.symm
  refine ⟨hint, ?_⟩
  unfold boltzmannEntropy
  rw [integral_congr_ae he]
  have hisub : Integrable (fun x => llr ν π x-U x) ν := hllr.sub hU
  rw [integral_sub hisub (integrable_const _), integral_sub hllr hU]
  rw [toReal_klDiv_of_measure_eq hνπ (by simp)]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

/-- Gaussian-reference version used for entropy semicontinuity. -/
theorem gaussian_boltzmann_identity (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : MemLp id 2 ν) (hK : klDiv ν (stdGaussian E) ≠ ∞) :
    Integrable (fun x => Real.log ((ν.rnDeriv volume x).toReal)) ν ∧
    boltzmannEntropy ν = (klDiv ν (stdGaussian E)).toReal -
      (1/2:ℝ)*(∫ x, ‖x‖^2 ∂ν) -
      (Module.finrank ℝ E : ℝ)/2*Real.log (2*Real.pi) := by
  have hK' : klDiv ν (positionGibbs (kineticPotential : E → ℝ)) ≠ ∞ := by
    simpa only [positionGibbs, ← stdGaussian_eq_kinetic_tilted] using hK
  have hh := gibbs_boltzmann_identity (kineticPotential : E → ℝ) kinetic_gibbs_integrable ν
    (hν.norm.integrable_sq.div_const 2) hK'
  rw [positionGibbs, ← stdGaussian_eq_kinetic_tilted, kinetic_normalizer_real,
    Real.log_rpow (by positivity : 0 < 2*Real.pi)] at hh
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  unfold kineticPotential
  rw [integral_div]
  ring

end PersistencePays
#print axioms PersistencePays.gibbs_boltzmann_identity
#print axioms PersistencePays.gaussian_boltzmann_identity
