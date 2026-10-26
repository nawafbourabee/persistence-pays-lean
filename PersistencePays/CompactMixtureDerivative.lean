import PersistencePays.CompactMixtureSmooth
import PersistencePays.RankOneDivergence

/-! Exact differentiation under compact mixtures, including divergence. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped RealInnerProductSpace
variable {P Y Z V:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

lemma compact_partial_fderiv_continuous {F:P×Y→V} (hF:ContDiff ℝ 1 F) :
    Continuous (fun q:P×Y=>fderiv ℝ (fun x=>F (x,q.2)) q.1) := by
  have he (q:P×Y):fderiv ℝ (fun x=>F (x,q.2)) q.1=
      (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ P Y) := by
    exact ((hF.differentiable one_ne_zero q).hasFDerivAt.comp q.1
      ((hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1))).fderiv
  simp_rw [he]
  exact (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const

lemma compact_mixture_fderiv (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→Y) (hg:Continuous g) {F:P×Y→V} (hF:ContDiff ℝ 1 F) (x:P) :
    fderiv ℝ (fun x=>∫z,F (x,g z) ∂μ) x=
      ∫z,fderiv ℝ (fun x=>F (x,g z)) x ∂μ := by
  apply HasFDerivAt.fderiv
  apply compact_parameter_integral_hasFDerivAt μ
    (F:=fun x z=>F (x,g z)) (F':=fun x z=>fderiv ℝ (fun x=>F (x,g z)) x)
  · exact hF.continuous.comp (continuous_fst.prodMk (hg.comp continuous_snd))
  · exact (compact_partial_fderiv_continuous hF).comp
      (continuous_fst.prodMk (hg.comp continuous_snd))
  · intro q z
    exact ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero q).hasFDerivAt

lemma compact_mixture_fderiv_apply (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→Y) (hg:Continuous g) {F:P×Y→V} (hF:ContDiff ℝ 1 F) (x v:P) :
    fderiv ℝ (fun x=>∫z,F (x,g z) ∂μ) x v=
      ∫z,fderiv ℝ (fun x=>F (x,g z)) x v ∂μ := by
  rw [compact_mixture_fderiv μ g hg hF]
  exact (ContinuousLinearMap.integral_apply
    (((compact_partial_fderiv_continuous hF).comp ((continuous_const (y:=x)).prodMk hg)).integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)) v)

lemma compact_mixture_deriv (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→Y) (hg:Continuous g) {F:ℝ×Y→V} (hF:ContDiff ℝ 1 F) (t:ℝ) :
    deriv (fun t=>∫z,F (t,g z) ∂μ) t=
      ∫z,deriv (fun t=>F (t,g z)) t ∂μ := by
  simpa only [deriv] using compact_mixture_fderiv_apply μ g hg hF t 1

variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma compact_mixture_vectorDivergence (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→Y) (hg:Continuous g) {F:E×Y→E} (hF:ContDiff ℝ 1 F) (x:E) :
    vectorDivergence (fun x=>∫z,F (x,g z) ∂μ) x=
      ∫z,vectorDivergence (fun x=>F (x,g z)) x ∂μ := by
  classical
  unfold vectorDivergence
  simp_rw [compact_mixture_fderiv_apply μ g hg hF]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    have hi:=(((compact_partial_fderiv_continuous hF).comp
      ((continuous_const (y:=x)).prodMk hg)).clm_apply (continuous_const (y:=stdOrthonormalBasis ℝ E i))).integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)
    simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm] using
      ((innerSL ℝ (stdOrthonormalBasis ℝ E i)).integral_comp_comm hi).symm
  · intro i _
    exact ((((compact_partial_fderiv_continuous hF).comp
      ((continuous_const (y:=x)).prodMk hg)).clm_apply continuous_const).inner continuous_const).integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)

lemma compact_mixture_matrixDivergence (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→Y) (hg:Continuous g) {F:E×Y→E→L[ℝ]E} (hF:ContDiff ℝ 1 F) (x:E) :
    matrixDivergence (fun x=>∫z,F (x,g z) ∂μ) x=
      ∫z,matrixDivergence (fun x=>F (x,g z)) x ∂μ := by
  classical
  unfold matrixDivergence
  simp_rw [compact_mixture_fderiv_apply μ g hg hF]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.integral_apply
      ((((compact_partial_fderiv_continuous hF).comp
        ((continuous_const (y:=x)).prodMk hg)).clm_apply continuous_const).integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)) _)
  · intro i _
    exact (((((compact_partial_fderiv_continuous hF).comp
      ((continuous_const (y:=x)).prodMk hg)).clm_apply continuous_const).clm_apply continuous_const).integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _))

end PersistencePays
#print axioms PersistencePays.compact_mixture_deriv
#print axioms PersistencePays.compact_mixture_vectorDivergence
#print axioms PersistencePays.compact_mixture_matrixDivergence
