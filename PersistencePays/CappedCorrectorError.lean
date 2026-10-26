import PersistencePays.CappedCorrector

/-! The comparison corrector remainder is precisely the manuscript's observable
formula and is nonnegative. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem cappedMidEntropyError_nonneg (U:E→ℝ) (hU:∀x,0≤U x)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (D vstar:ℝ) :
    0≤cappedMidEntropyError U μ D vstar := by
  let α := (μ (fastVelocitySet vstar)).toReal
  have ha : 0≤α := ENNReal.toReal_nonneg
  have ha1 : α≤1 := measureReal_le_one
  have hl : 0≤α*Real.log (1/α) := by
    by_cases hz:α=0
    · simp only [hz,zero_mul,le_refl]
    · have hp : 0<α := lt_of_le_of_ne ha (Ne.symm hz)
      exact mul_nonneg ha (Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using ha1)))
  have hi : 0≤∫z in fastVelocitySet vstar,(2*U z.1+‖z.2‖^2)∂μ :=
    integral_nonneg (fun z=>add_nonneg (mul_nonneg (by norm_num) (hU z.1)) (sq_nonneg _))
  have hp : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  unfold cappedMidEntropyError
  change 0≤3*α*Real.log (1/α)+2*α+α*max (Real.log D) 0+
    α*(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)+_
  nlinarith [mul_nonneg ha (le_max_right (Real.log D) 0),
    mul_nonneg (mul_nonneg ha (Nat.cast_nonneg (Module.finrank ℝ E))) hp]

theorem A1.comparisonCorrectorError_nonneg {U:E→ℝ} {L:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] {h:ℝ} (hh:0<h) (D vstar:ℝ) :
    0≤a.comparisonCorrectorError μ h D vstar := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let q := μ.map (kickEquiv (gradient U) hg (h/2))
  have he := cappedMidEntropyError_nonneg U (a.normalized_potential_nonnegative hstar hzero) q D vstar
  have hw : 0≤QuadraticTransport.wassersteinTwo ⟨(transportJoint q (h/2)).fst,inferInstance⟩ a.targetProbability :=
    Real.sqrt_nonneg _
  unfold A1.comparisonCorrectorError
  change 0≤(13/4:ℝ)*L*h^2*(∫z,‖z.2‖^2∂q)+(13/2:ℝ)*(∫z in fastVelocitySet vstar,‖z.2‖^2∂q)+
    (2/h)*Real.sqrt (∫z in fastVelocitySet vstar,‖z.2‖^2∂q)*
      QuadraticTransport.wassersteinTwo ⟨(transportJoint q (h/2)).fst,inferInstance⟩ a.targetProbability+
    7*cappedMidEntropyError U q D vstar
  positivity [a.L_pos]

/-- Pushback of every exceptional observable through the first kick. -/
theorem kick_fast_setIntegral (g:E→E) (hg:Measurable g) (μ:Measure (E×E)) (h vstar:ℝ)
    (f:E×E→ℝ) (hf:Measurable f) :
    (∫z in fastVelocitySet vstar,f z∂μ.map (kickEquiv g hg (h/2)))=
      ∫z in {z|vstar<‖flightVelocity g h z‖},f (kick g (h/2) z)∂μ := by
  have hA := fastVelocitySet_measurable (E:=E) vstar
  have hB : MeasurableSet {z|vstar<‖flightVelocity g h z‖} :=
    measurableSet_lt measurable_const ((measurable_snd.comp (kickEquiv g hg (h/2)).measurable).norm)
  rw [←integral_indicator hA,←integral_indicator hB,
    integral_map (kickEquiv g hg (h/2)).measurable.aemeasurable (hf.indicator hA).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz:vstar<‖flightVelocity g h z‖
  · simp only [indicator_of_mem (show kickEquiv g hg (h/2) z∈fastVelocitySet vstar from hz),
      indicator_of_mem (show z∈{z|vstar<‖flightVelocity g h z‖} from hz)]
    rfl
  · simp only [indicator_of_notMem (show kickEquiv g hg (h/2) z∉fastVelocitySet vstar from hz),
      indicator_of_notMem (show z∉{z|vstar<‖flightVelocity g h z‖} from hz)]

end PersistencePays
#print axioms PersistencePays.A1.comparisonCorrectorError_nonneg
