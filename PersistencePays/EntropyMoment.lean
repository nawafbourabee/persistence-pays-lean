import PersistencePays.Pinsker
import PersistencePays.GibbsPositionMoment

/-! Finite entropy transfers exponential reference moments to actual first
moments, without assuming integrability under the changed law. In particular,
finite Gibbs entropy implies a finite second moment for every A1 target. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

theorem integrable_of_exp_integrable_of_klDiv_finite
    {S : Type*} [MeasurableSpace S] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) {f : S → ℝ} (hf : Measurable f)
    (hf0 : ∀ x,0≤f x) (he : Integrable (fun x => Real.exp (f x)) ν) :
    Integrable f μ := by
  have hac := (klDiv_ne_top_iff.mp hD).1
  have hkl : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν :=
    (integrable_klFun_rnDeriv_iff hac).mpr (klDiv_ne_top_iff.mp hD).2
  have hp : Integrable (fun x => (μ.rnDeriv ν x).toReal*f x) ν := by
    apply ((hkl.add he).sub (integrable_const 1)).mono'
      (((Measure.measurable_rnDeriv μ ν).ennreal_toReal.mul hf).aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
    rw [Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hf0 x))]
    exact mul_le_klFun_add_exp ENNReal.toReal_nonneg (f x)
  exact (integrable_toReal_rnDeriv_mul_iff hac).mp hp

theorem integral_le_klDiv_add_log_exp_integral
    {S : Type*} [MeasurableSpace S] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : klDiv μ ν ≠ ∞) {f : S → ℝ} (hf : Measurable f)
    (hf0 : ∀ x,0≤f x) (he : Integrable (fun x => Real.exp (f x)) ν) :
    (∫ x,f x ∂μ) ≤ (klDiv μ ν).toReal + Real.log (∫ x,Real.exp (f x) ∂ν) := by
  have hi := integrable_of_exp_integrable_of_klDiv_finite μ ν hD hf hf0 he
  let Z := ∫ x,Real.exp (f x) ∂ν
  have hZ : 0<Z := integral_exp_pos he
  have htest : Integrable (fun x => Real.exp (f x-Real.log Z)) ν := by
    simpa only [Real.exp_sub,Real.exp_log hZ] using he.div_const Z
  have hnorm : (∫ x,Real.exp (f x-Real.log Z) ∂ν) ≤ 1 := by
    simp only [Real.exp_sub,Real.exp_log hZ,integral_div]
    change Z/Z≤1
    rw [div_self hZ.ne']
  have hh := integral_le_klDiv_of_exp_integral_le_one μ ν hD
    (fun x => f x-Real.log Z) (hi.sub (integrable_const _)) htest hnorm
  rw [integral_sub hi (integrable_const _)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  dsimp only [Z] at hh
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.entropy_energy_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hK : klDiv ν (positionGibbs U) ≠ ∞) :
    Integrable (fun x => (U x-U a.minimizer)/2) ν := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  exact integrable_of_exp_integrable_of_klDiv_finite ν (positionGibbs U) hK
    (by have hU := a.twice_contDiff.continuous; fun_prop)
    (fun x => by have h := a.minimizer_le x; linarith)
    a.position_energy_exp_integrable

theorem A1.entropy_energy_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hK : klDiv ν (positionGibbs U) ≠ ∞) :
    (∫ x,(U x-U a.minimizer)/2 ∂ν) ≤
      (klDiv ν (positionGibbs U)).toReal+(Module.finrank ℝ E : ℝ)*Real.log 2 := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hh := integral_le_klDiv_add_log_exp_integral ν (positionGibbs U) hK
    (f:=fun x => (U x-U a.minimizer)/2)
    (by have hU := a.twice_contDiff.continuous; fun_prop)
    (fun x => by have h := a.minimizer_le x; linarith)
    a.position_energy_exp_integrable
  have hb := Real.log_le_log (integral_exp_pos a.position_energy_exp_integrable)
    a.position_energy_mgf_bound
  rw [Real.log_pow] at hb
  linarith

theorem A1.memLp_two_of_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hK : klDiv ν (positionGibbs U) ≠ ∞) : MemLp id 2 ν := by
  have hm := a.m_pos
  have hi := (a.entropy_energy_integrable ν hK).const_mul (4/m)
  have hcent : Integrable (fun x:E => ‖x-a.minimizer‖^2) ν := by
    apply hi.mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb := a.quadratic_lower_at_minimizer x
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).mpr
    linarith
  have hc : MemLp (fun x:E => x-a.minimizer) 2 ν :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr hcent
  convert hc.add (memLp_const a.minimizer) using 1
  funext x
  simp

theorem A1.entropy_centered_second_moment {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hK : klDiv ν (positionGibbs U) ≠ ∞) :
    (∫ x:E,‖x-a.minimizer‖^2 ∂ν) ≤
      4/m*((klDiv ν (positionGibbs U)).toReal+(Module.finrank ℝ E : ℝ)*Real.log 2) := by
  have hm := a.m_pos
  have hnorm : Integrable (fun x:E => ‖x-a.minimizer‖^2) ν := by
    exact ((a.memLp_two_of_entropy_finite ν hK).sub (memLp_const a.minimizer)).integrable_norm_pow'
  have he := a.entropy_energy_integrable ν hK
  have hb := integral_mono hnorm (he.const_mul (4/m)) (fun x => by
    have hh := a.quadratic_lower_at_minimizer x
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).mpr
    linarith)
  rw [integral_const_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (a.entropy_energy_bound ν hK) (by positivity))

end PersistencePays
#print axioms PersistencePays.integrable_of_exp_integrable_of_klDiv_finite
#print axioms PersistencePays.A1.memLp_two_of_entropy_finite
#print axioms PersistencePays.A1.entropy_centered_second_moment
