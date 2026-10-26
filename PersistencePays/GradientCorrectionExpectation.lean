import PersistencePays.SandwichEntropy

/-! The signed gradient correction telescopes through an actual sandwich
step, because its Ornstein--Uhlenbeck stages preserve positions. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def expectedGradientCorrection (U : E → ℝ) (h : ℝ) (μ : Measure (E×E)) : ℝ :=
  ∫ z,gradientCorrection (gradient U) h z.1 ∂μ

def expectedVerletRemainder (U : E → ℝ) (h : ℝ) (μ : Measure (E×E)) : ℝ :=
  ∫ z,trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h z).1 ∂μ

theorem A1.gradientCorrection_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ] {f : S → E}
    (hf : MemLp f 2 μ) (h : ℝ) : Integrable (fun z => gradientCorrection (gradient U) h (f z)) μ := by
  simp_rw [gradientCorrection_eq_norm]
  exact (a.gradient_memLp hf).integrable_norm_pow'.const_mul (h^2/8)

theorem A1.verletRemainder_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    Integrable (fun z => trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h z).1) μ := by
  have hi : Integrable (fun z => L*h^2/8*‖flightVelocity (gradient U) h z‖^2) μ :=
    ((a.kick_memLp hμ (h/2)).snd.integrable_norm_pow').const_mul _
  apply hi.mono' _ (Filter.Eventually.of_forall (fun z => ?_))
  · have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous
    have hU := a.twice_contDiff.continuous
    unfold trapezoidDefect verlet kick drift
    fun_prop
  · rw [Real.norm_eq_abs]
    exact (lemma_2_1_A1 a z).2.1

theorem position_integral_ou (G : E → ℝ) (hG : Measurable G)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (r σ : ℝ) :
    (∫ z,G z.1 ∂phaseOUKernel r σ ∘ₘ μ) = ∫ z,G z.1 ∂μ := by
  have he (ν : Measure (E×E)) : (∫ z,G z.1 ∂ν) = ∫ x,G x ∂ν.fst :=
    (integral_map measurable_fst.aemeasurable hG.aestronglyMeasurable).symm
  rw [he,he,phaseOUKernel_fst]

theorem A1.expectedGradientCorrection_ou {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (h r σ : ℝ) :
    expectedGradientCorrection U h (phaseOUKernel r σ ∘ₘ μ) = expectedGradientCorrection U h μ :=
  position_integral_ou _ (by
    change Measurable (fun x : E => gradientCorrection (gradient U) h x)
    simp_rw [gradientCorrection_eq_norm]
    exact ((contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable.norm.pow_const 2).const_mul _)
    μ r σ

theorem A1.expectedGradientCorrection_bounds {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    0 ≤ expectedGradientCorrection U h μ ∧
    expectedGradientCorrection U h μ ≤ h^2*L/4*(∫ z,U z.1-U a.minimizer ∂μ) := by
  constructor
  · exact integral_nonneg (fun z => (lemma_2_1_A1 a z).2.2.1)
  · have hi := integral_mono (a.gradientCorrection_integrable hμ.fst h)
      (((a.potential_integrable hμ.fst).sub (integrable_const _)).const_mul (h^2*L/4))
      (fun z => (lemma_2_1_A1 a z).2.2.2)
    simpa only [integral_const_mul,id_eq,Pi.sub_apply,expectedGradientCorrection] using hi

theorem A1.expectedVerletRemainder_bound {U : E → ℝ} {m L LH : ℝ} (a : A1 U m L)
    (a2 : A2 U LH) (μ : Measure (E×E)) [IsFiniteMeasure μ] (hμ : MemLp id 3 μ)
    (h : ℝ) (hh : 0 ≤ h) :
    expectedVerletRemainder U h μ ≤ LH/12*h^3*(∫ z,‖flightVelocity (gradient U) h z‖^3 ∂μ) := by
  have hi : Integrable (fun z => LH/12*h^3*‖flightVelocity (gradient U) h z‖^3) μ :=
    ((a.kick_memLp hμ (h/2)).snd.integrable_norm_pow').const_mul _
  have hb := integral_mono (a.verletRemainder_integrable μ (hμ.mono_exponent (by norm_num)) h) hi
    (fun z => (le_abs_self _).trans (lemma_2_1 a a2 hh z).2.2.1)
  simpa only [integral_const_mul,expectedVerletRemainder] using hb

theorem A1.verlet_sandwich_energy_telescope {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h r σ : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := verletEquiv (gradient U) hg h
    (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂phaseOUKernel r σ ∘ₘ μ) =
      expectedGradientCorrection U h (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ)-
        expectedGradientCorrection U h μ+expectedVerletRemainder U h (phaseOUKernel r σ ∘ₘ μ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let e := verletEquiv (gradient U) hg h
  let ν := phaseOUKernel r σ ∘ₘ μ
  have hν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  letI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have hi0 : Integrable (fun z : E×E => gradientCorrection (gradient U) h z.1) ν :=
    a.gradientCorrection_integrable hν.fst h
  have hi1 : Integrable (fun z : E×E => gradientCorrection (gradient U) h (e z).1) ν :=
    a.gradientCorrection_integrable (a.verlet_memLp hν h).fst h
  have hit : Integrable (fun z => trapezoidDefect U (gradient U) z.1 (e z).1) ν :=
    a.verletRemainder_integrable ν hν h
  have hisub : Integrable (fun z => gradientCorrection (gradient U) h (e z).1-
      gradientCorrection (gradient U) h z.1) ν := hi1.sub hi0
  have hG : Measurable (fun z : E×E => gradientCorrection (gradient U) h z.1) := by
    simp_rw [gradientCorrection_eq_norm]
    exact (((contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable.comp measurable_fst).norm.pow_const 2).const_mul _
  have heq : (fun z => phaseEnergy U (e z)-phaseEnergy U z) =
      fun z => gradientCorrection (gradient U) h (e z).1-gradientCorrection (gradient U) h z.1+
        trapezoidDefect U (gradient U) z.1 (e z).1 := by
    funext z
    exact verlet_energy_identity U (gradient U) h z
  dsimp only
  change (∫ z,phaseEnergy U (e z)-phaseEnergy U z ∂ν) = _
  rw [heq,integral_add hisub hit,integral_sub hi1 hi0]
  rw [gaussianSandwichKernel_comp,a.expectedGradientCorrection_ou]
  have hpost : expectedGradientCorrection U h (ν.map e) =
      ∫ z,gradientCorrection (gradient U) h (e z).1 ∂ν :=
    integral_map e.measurable.aemeasurable hG.aestronglyMeasurable
  rw [hpost,← a.expectedGradientCorrection_ou μ h r σ]
  rfl

end PersistencePays
#print axioms PersistencePays.A1.verlet_sandwich_energy_telescope
