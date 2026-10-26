import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Compact smooth matrix integration by parts, with all integrability derived. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixDivergence (S : E → E →L[ℝ] E) (x : E) : E :=
  ∑ i, (fderiv ℝ S x (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i)

theorem matrixDivergence_continuous {S : E → E →L[ℝ] E} (hS : ContDiff ℝ 1 S) :
    Continuous (matrixDivergence S) := by
  unfold matrixDivergence
  apply continuous_finsetSum
  intro i _
  exact ((hS.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const

theorem matrixDivergence_compact {S : E → E →L[ℝ] E} (hc : HasCompactSupport S) :
    HasCompactSupport (matrixDivergence S) := by
  exact (hc.fderiv ℝ).comp_left
    (g:=fun A : E →L[ℝ] (E →L[ℝ] E) =>
      ∑ i, A (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) (by simp)

theorem compact_inner_integrable {F G : E → E} (hF : Continuous F)
    (hc : HasCompactSupport F) (hG : Continuous G) :
    Integrable (fun x => ⟪F x,G x⟫_ℝ) volume := by
  have hs : HasCompactSupport (fun x => ⟪F x,G x⟫_ℝ) := hc.mono' (fun x hx => by
    contrapose! hx
    simp only [Function.mem_support,not_not]
    rw [image_eq_zero_of_notMem_tsupport hx,inner_zero_left])
  exact (hF.inner hG).integrable_of_hasCompactSupport hs

theorem matrix_column_fderiv {S : E → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (x v w : E) :
    fderiv ℝ (fun y => S y v) x w = (fderiv ℝ S x w) v := by
  have hd := ((hS.differentiable one_ne_zero x).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  rw [hd.fderiv]
  simp

theorem compact_matrix_column_integrals {S : E → E →L[ℝ] E} {T : E → E}
    (hS : ContDiff ℝ 1 S) (hc : HasCompactSupport S) (hT : ContDiff ℝ 1 T)
    (v : E) :
    Integrable (fun x => ⟪(fderiv ℝ S x v) v,T x⟫_ℝ) volume ∧
    Integrable (fun x => ⟪S x v,fderiv ℝ T x v⟫_ℝ) volume ∧
    Integrable (fun x => ⟪S x v,T x⟫_ℝ) volume := by
  have hcol : HasCompactSupport (fun x => S x v) := hc.comp_left (g:=fun A : E →L[ℝ] E => A v) rfl
  have hdcol : HasCompactSupport (fun x => (fderiv ℝ S x v) v) :=
    ((hc.fderiv ℝ).comp_left (g:=fun A : E →L[ℝ] (E →L[ℝ] E) => A v v) rfl)
  refine ⟨compact_inner_integrable ?_ hdcol hT.continuous,
    compact_inner_integrable (hS.continuous.clm_apply continuous_const) hcol ?_,
    compact_inner_integrable (hS.continuous.clm_apply continuous_const) hcol hT.continuous⟩
  · exact ((hS.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const
  · exact (hT.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem compact_matrix_column_ibp {S : E → E →L[ℝ] E} {T : E → E}
    (hS : ContDiff ℝ 1 S) (hc : HasCompactSupport S) (hT : ContDiff ℝ 1 T)
    (v : E) :
    (∫ x, ⟪S x v,fderiv ℝ T x v⟫_ℝ) = -∫ x, ⟪(fderiv ℝ S x v) v,T x⟫_ℝ := by
  have hi := compact_matrix_column_integrals hS hc hT v
  have hb := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure E)) (B:=innerSL ℝ) (f:=fun x => S x v) (g:=T) (v:=v)
    (by
      change Integrable (fun x => ⟪fderiv ℝ (fun y => S y v) x v,T x⟫_ℝ) volume
      simpa only [matrix_column_fderiv hS] using hi.1)
    hi.2.1 hi.2.2
    (fun x _ => ((hS.differentiable one_ne_zero).clm_apply (differentiable_const v)) x)
    (fun x _ => hT.differentiable one_ne_zero x)
  change (∫ x, ⟪S x v,fderiv ℝ T x v⟫_ℝ) =
    -∫ x, ⟪fderiv ℝ (fun y => S y v) x v,T x⟫_ℝ at hb
  simpa only [matrix_column_fderiv hS] using hb

theorem trace_symmetric_comp {S A : E →L[ℝ] E} (hS : S.toLinearMap.IsSymmetric) :
    (S.comp A).toLinearMap.trace ℝ E =
      ∑ i, ⟪S (stdOrthonormalBasis ℝ E i),A (stdOrthonormalBasis ℝ E i)⟫_ℝ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  apply Finset.sum_congr rfl
  intro i _
  exact (hS _ _).symm

theorem compact_matrix_ibp {S : E → E →L[ℝ] E} {T : E → E}
    (hS : ContDiff ℝ 1 S) (hc : HasCompactSupport S) (hT : ContDiff ℝ 1 T)
    (hsym : ∀ x, (S x).toLinearMap.IsSymmetric) :
    Integrable (fun x => ((S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E) volume ∧
    Integrable (fun x => ⟪matrixDivergence S x,T x⟫_ℝ) volume ∧
    (∫ x, ((S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E) =
      -∫ x, ⟪matrixDivergence S x,T x⟫_ℝ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hi := fun i => compact_matrix_column_integrals hS hc hT (b i)
  have he (x:E) : ⟪matrixDivergence S x,T x⟫_ℝ =
      ∑ i,⟪(fderiv ℝ S x (b i)) (b i),T x⟫_ℝ := by
    simp only [matrixDivergence,sum_inner,b]
  have ht (x:E) := trace_symmetric_comp (A:=fderiv ℝ T x) (hsym x)
  refine ⟨?_,?_,?_⟩
  · simp_rw [ht]
    exact integrable_finsetSum _ (fun i _ => (hi i).2.1)
  · simp_rw [he]
    exact integrable_finsetSum _ (fun i _ => (hi i).1)
  · simp_rw [ht,he]
    rw [integral_finsetSum _ (fun i _ => (hi i).2.1),
      integral_finsetSum _ (fun i _ => (hi i).1)]
    simp_rw [compact_matrix_column_ibp hS hc hT,Finset.sum_neg_distrib]

end PersistencePays
#print axioms PersistencePays.compact_matrix_ibp
