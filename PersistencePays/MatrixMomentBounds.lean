import PersistencePays.DensityWeights
import PersistencePays.CompactMatrixIBP

/-! The pointwise density bounds in Appendix A imply every boundary/divergence
integrability hypothesis used to remove the matrix cutoffs. -/
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def operatorTraceCLM : (E→L[ℝ]E) →L[ℝ] ℝ :=
  ∑ i,quadraticEvaluation (stdOrthonormalBasis ℝ E i)

@[simp] theorem operatorTraceCLM_apply (A:E→L[ℝ]E) :
    operatorTraceCLM A=A.toLinearMap.trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  simp only [operatorTraceCLM,sum_apply,quadraticEvaluation_apply]
  rfl

theorem matrix_density_moment_integrability (ν:ProbabilityMeasure E)
    {n:E→ℝ} (hn:Measurable n) (hn0:∀ x,0≤n x)
    (hν:(ν:Measure E)=volume.withDensity (fun x => ENNReal.ofReal (n x)))
    (hx:MemLp id 2 (ν:Measure E)) {T:E→E} (hTm:Measurable T)
    (hT:MemLp T 2 (ν:Measure E))
    {S:E→E→L[ℝ]E} (hS:ContDiff ℝ 1 S) {C:ℝ}
    (hSb:∀ x,‖S x‖≤C*n x)
    (hdb:∀ x,‖matrixDivergence S x‖≤C*(1+‖x‖)*n x) :
    Integrable (fun x => S x (T x)) volume ∧
    Integrable (fun x => ⟪matrixDivergence S x,T x⟫) volume ∧
    Integrable (fun x => (S x).toLinearMap.trace ℝ E) volume := by
  have hnI : Integrable n volume := by
    have hh := (real_density_integrable_iff (ν:Measure E) hn hn0 hν (fun _ : E => (1:ℝ))).mp
      (integrable_const 1)
    simpa only [smul_eq_mul,mul_one] using hh
  have hSi : Integrable S volume := by
    apply (hnI.const_mul C).mono' hS.continuous.aestronglyMeasurable
    exact .of_forall hSb
  have hiT : Integrable (fun x => n x*‖T x‖) volume := by
    simpa only [smul_eq_mul] using
      (real_density_integrable_iff (ν:Measure E) hn hn0 hν (fun x => ‖T x‖)).mp
        (hT.integrable (by norm_num)).norm
  have hiXT : Integrable (fun x => (1+‖x‖)*‖T x‖) (ν:Measure E) := by
    have hh := (hT.integrable (by norm_num)).norm.add (hx.norm.integrable_mul hT.norm)
    change Integrable (fun x => ‖T x‖+‖x‖*‖T x‖) (ν:Measure E) at hh
    simpa only [add_mul,one_mul] using hh
  have hiXT' : Integrable (fun x => n x*((1+‖x‖)*‖T x‖)) volume := by
    simpa only [smul_eq_mul] using
      (real_density_integrable_iff (ν:Measure E) hn hn0 hν _).mp hiXT
  refine ⟨?_,?_,?_⟩
  · apply (hiT.const_mul C).mono'
      (((continuous_fst.clm_apply continuous_snd).measurable.comp
        (hS.continuous.measurable.prodMk hTm)).aestronglyMeasurable)
    filter_upwards with x
    calc
      ‖S x (T x)‖ ≤ ‖S x‖*‖T x‖ := (S x).le_opNorm _
      _ ≤ (C*n x)*‖T x‖ := mul_le_mul_of_nonneg_right (hSb x) (norm_nonneg _)
      _ = C*(n x*‖T x‖) := by ring
  · have hm : Measurable (fun x => ⟪matrixDivergence S x,T x⟫) :=
      (continuous_fst.inner continuous_snd).measurable.comp
        ((matrixDivergence_continuous hS).measurable.prodMk hTm)
    apply (hiXT'.const_mul C).mono' hm.aestronglyMeasurable
    filter_upwards with x
    calc
      ‖⟪matrixDivergence S x,T x⟫‖ ≤ ‖matrixDivergence S x‖*‖T x‖ := norm_inner_le_norm _ _
      _ ≤ (C*(1+‖x‖)*n x)*‖T x‖ := mul_le_mul_of_nonneg_right (hdb x) (norm_nonneg _)
      _ = C*(n x*((1+‖x‖)*‖T x‖)) := by ring
  · simpa only [Function.comp_def,operatorTraceCLM_apply] using
      (operatorTraceCLM (E:=E)).integrable_comp hSi

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.matrix_density_moment_integrability
