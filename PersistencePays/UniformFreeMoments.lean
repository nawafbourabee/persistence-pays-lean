import PersistencePays.FreeTransportCorrectorContinuity
import PersistencePays.MeanFlowCorrector
import PersistencePays.ComparisonMidpoint

/-! Uniform polynomial moments of the actual freely transported position law,
with a common source-measure envelope on every bounded time interval. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def freeMomentEnvelope (T:ℝ) (n:ℕ) (z:E×E):ℝ := (1+(1+|T|)*‖z‖)^n

theorem freeMomentEnvelope_integrable (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (n:ℕ) (hμ:MemLp id (n:ℝ≥0∞) μ) (T:ℝ) :
    Integrable (freeMomentEnvelope (E:=E) T n) μ := by
  have hi:=((memLp_const (1:ℝ)).add (hμ.norm.const_mul (1+|T|))).integrable_norm_pow'
  apply hi.congr
  filter_upwards with z
  simp only [freeMomentEnvelope,Pi.add_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1+(1+|T|)*‖z‖)]

theorem transportPosition_memLp (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {p:ℝ≥0∞} (hμ:MemLp id p μ) (s:ℝ) : MemLp id p (transportPosition μ s) :=
  (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr
    (transportProbability_memLp μ hμ s).fst

theorem polynomialEnvelope_integrable (ν:Measure E) [IsProbabilityMeasure ν]
    (n:ℕ) (hν:MemLp id (n:ℝ≥0∞) ν) : Integrable (fun x:E=>(1+‖x‖)^n) ν := by
  have hi:=((memLp_const (1:ℝ)).add hν.norm).integrable_norm_pow'
  apply hi.congr
  filter_upwards with x
  simp only [Pi.add_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1+‖x‖)]

theorem freePosition_polynomial_moment (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (n:ℕ) (hμ:MemLp id (n:ℝ≥0∞) μ) (T s:ℝ) (hs:|s|≤|T|) :
    (∫x,(1+‖x‖)^n ∂transportPosition μ s)≤∫z,freeMomentEnvelope T n z ∂μ := by
  have hi:=polynomialEnvelope_integrable _ n (transportPosition_memLp μ hμ s)
  rw [transportPosition,Measure.fst,transportJoint,
    Measure.map_map measurable_fst (measurable_freeTransport s),
    integral_map (by fun_prop) (by fun_prop)]
  apply integral_mono
  · rw [transportPosition,Measure.fst,transportJoint,
      Measure.map_map measurable_fst (measurable_freeTransport s)] at hi
    exact (integrable_map_measure
      (show AEStronglyMeasurable (fun x:E=>(1+‖x‖)^n) _ from by fun_prop)
      ((measurable_fst.comp (measurable_freeTransport s)).aemeasurable)).mp hi
  · exact freeMomentEnvelope_integrable μ n hμ T
  · intro z
    have hn:‖(freeTransport s z).1‖≤(1+|T|)*‖z‖ :=
      (norm_fst_le _).trans ((freeTransport_norm_le s z).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)))
    exact pow_le_pow_left₀ (by positivity) (by dsimp only [Function.comp_apply]; linarith) n

theorem polynomialEnvelope_memLp_two (ν:Measure E) [IsProbabilityMeasure ν]
    (n:ℕ) (hν:MemLp id ((2*n:ℕ):ℝ≥0∞) ν) :
    MemLp (fun x:E=>(1+‖x‖)^n) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  have hi:=polynomialEnvelope_integrable ν (2*n) hν
  convert hi using 1
  funext x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),←pow_mul]
  congr 1
  omega

theorem freePosition_polynomial_L2 (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (n:ℕ) (hμ:MemLp id ((2*n:ℕ):ℝ≥0∞) μ) (T s C:ℝ)
    (hC:0≤C) (hs:|s|≤|T|) (f:E→E) (hf:Measurable f)
    (hb:∀x,‖f x‖≤C*(1+‖x‖)^n) :
    MemLp f 2 (transportPosition μ s) ∧
    (∫x,‖f x‖^2 ∂transportPosition μ s)≤
      C^2*(∫z,freeMomentEnvelope T (2*n) z ∂μ) := by
  have henv:=polynomialEnvelope_memLp_two _ n (transportPosition_memLp μ hμ s)
  have hmem : MemLp f 2 (transportPosition μ s) :=
    (henv.const_mul C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hmem,?_⟩
  calc
    _≤∫x,C^2*(1+‖x‖)^(2*n) ∂transportPosition μ s:=by
      apply integral_mono hmem.integrable_norm_pow'
        ((polynomialEnvelope_integrable _ (2*n) (transportPosition_memLp μ hμ s)).const_mul (C^2))
      intro x
      have hsq:‖f x‖^2≤(C*(1+‖x‖)^n)^2:=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hb x)
      simpa only [mul_pow,←pow_mul,show n*2=2*n from Nat.mul_comm n 2] using hsq
    _=C^2*(∫x,(1+‖x‖)^(2*n) ∂transportPosition μ s):=integral_const_mul _ _
    _≤_:=mul_le_mul_of_nonneg_left (freePosition_polynomial_moment μ (2*n) hμ T s hs) (sq_nonneg C)

/-- Uniform actual squared transport cost to any finite-second-moment target. -/
theorem freePosition_cost_uniform (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ:MemLp id 2 μ) (ν:ProbabilityMeasure E) (hν:MemLp id 2 (ν:Measure E)) (T:ℝ) :
    ∃B:ℝ,0≤B ∧ ∀s:ℝ,|s|≤|T|→
      (QuadraticTransport.cost (freePositionProbability μ s) ν).toReal≤B^2 := by
  let M:=∫z,freeMomentEnvelope T 2 z ∂μ
  let B:=Real.sqrt M+Real.sqrt (∫x,‖x‖^2 ∂(ν:Measure E))
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro s hs
  have hμs:=transportPosition_memLp μ hμ s
  have hi:=polynomialEnvelope_integrable _ 2 hμs
  have hmoment : (∫x,‖x‖^2 ∂transportPosition μ s)≤M := by
    apply (integral_mono hμs.integrable_norm_pow' hi (fun x=>by
      simp only [id_eq]
      nlinarith [norm_nonneg x])).trans
    exact freePosition_polynomial_moment μ 2 hμ T s hs
  have hw:=QuadraticTransport.wassersteinTwo_le_second_moments
    (freePositionProbability μ s) ν hμs hν
  have hwB : QuadraticTransport.wassersteinTwo (freePositionProbability μ s) ν≤B := by
    apply hw.trans
    exact add_le_add (Real.sqrt_le_sqrt hmoment) le_rfl
  have hb:0≤B:=by dsimp [B]; positivity
  have hsq: (QuadraticTransport.wassersteinTwo (freePositionProbability μ s) ν)^2≤B^2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mpr hwB
  simpa only [QuadraticTransport.wassersteinTwo,Real.sq_sqrt ENNReal.toReal_nonneg] using hsq

end PersistencePays
#print axioms PersistencePays.freePosition_polynomial_L2

#print axioms PersistencePays.freePosition_cost_uniform
