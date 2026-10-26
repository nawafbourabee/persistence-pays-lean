import PersistencePays.ConvexMatrixDivergence
import PersistencePays.MatrixDivergenceProduct
import PersistencePays.RadialCutoff

/-! Removing the matrix cutoff, retaining the singular-Hessian sign.
Only integrability of the ordinary boundary and divergence pairings is used;
integrability of the Hessian contraction is a conclusion. -/
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology RealInnerProductSpace ContDiff
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma matrixDivergence_smul_pairing {χ : E → ℝ} {S : E → E →L[ℝ] E}
    (hχ : ContDiff ℝ 1 χ) (hS : ContDiff ℝ 1 S)
    (hsym : ∀ x,(S x).toLinearMap.IsSymmetric) (x v:E) :
    ⟪matrixDivergence (fun y => χ y • S y) x,v⟫ =
      χ x*⟪matrixDivergence S x,v⟫+(fderiv ℝ χ x) (S x v) := by
  rw [matrixDivergence_smul hχ hS,inner_add_left,inner_smul_left]
  simp only [conj_trivial]
  have hh := hsym x (gradient χ x) v
  change ⟪S x (gradient χ x),v⟫=⟪gradient χ x,S x v⟫ at hh
  rw [hh,inner_gradient_left]

theorem weighted_convex_matrix_divergence
    {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {T : E → E} (he : T =ᵐ[volume] gradient φ)
    {G : E → E →L[ℝ] E} {s : Set E}
    (hs : volume sᶜ=0) (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,(G x).toLinearMap.IsPositive)
    {S : E → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (hSp : ∀ x,(S x).toLinearMap.IsPositive)
    (hST : Integrable (fun x => S x (T x)) volume)
    (hdiv : Integrable (fun x => ⟪matrixDivergence S x,T x⟫) volume) :
    Integrable (fun x => ((S x).comp (G x)).toLinearMap.trace ℝ E) volume ∧
    (∫ x,((S x).comp (G x)).toLinearMap.trace ℝ E) ≤
      -∫ x,⟪matrixDivergence S x,T x⟫ := by
  let q : E → ℝ := fun x => ((S x).comp (G x)).toLinearMap.trace ℝ E
  have hq : Measurable q := continuous_clm_trace.measurable.comp
    ((continuous_fst.clm_comp continuous_snd).measurable.comp (hS.continuous.measurable.prodMk hG))
  have hq0 : ∀ᵐ x ∂volume,0≤q x := hpos.mono (fun x hx =>
    positive_trace_comp_nonneg (S x).toLinearMap (G x).toLinearMap (hSp x) hx.re_inner_nonneg_right)
  have hc (n:ℕ) := compact_convex_matrix_divergence hφ he hs hG hd hpos
    (((radialCutoff_contDiff n).of_le (by norm_num)).smul hS)
    ((radialCutoff_compact n).smul_right)
    (fun x => (hSp x).smul_of_nonneg (radialCutoff_mem_Icc n x).1)
  have heq (n:ℕ) (x:E) :
      (((radialCutoff n x • S x).comp (G x)).toLinearMap.trace ℝ E)=radialCutoff n x*q x := by
    simp only [smul_comp,toLinearMap_smul,map_smul,smul_eq_mul,q]
  have hi (n:ℕ) : Integrable (fun x => radialCutoff n x*q x) volume := by
    have hh : Integrable (fun x => ((radialCutoff n x • S x).comp (G x)).toLinearMap.trace ℝ E) volume := (hc n).1
    simpa only [heq] using hh
  have hloc (n:ℕ) : (∫ x,radialCutoff n x*q x) ≤
      (∫ x,radialCutoff n x*(-⟪matrixDivergence S x,T x⟫))+
        (-(∫ x,(fderiv ℝ (radialCutoff n) x) (S x (T x)))) := by
    have hdi := radialCutoff_mul_integrable hdiv n
    have hei := radialCutoff_derivative_integrable hST n
    have hh := (hc n).2
    change (∫ x,((radialCutoff n x • S x).comp (G x)).toLinearMap.trace ℝ E) ≤
      -∫ x,⟪matrixDivergence (fun y => radialCutoff n y • S y) x,T x⟫ at hh
    simp only [heq,matrixDivergence_smul_pairing
      ((radialCutoff_contDiff n).of_le (by norm_num)) hS (fun x => (hSp x).isSymmetric)] at hh
    rw [integral_add hdi hei] at hh
    simpa only [mul_neg,integral_neg,neg_add_rev,add_comm] using hh
  have hout := integral_bound_of_cutoffs hq.aestronglyMeasurable hq0 hdiv.neg
    (fun n => (radialCutoff_contDiff n).continuous.aestronglyMeasurable)
    (fun n => .of_forall (radialCutoff_mem_Icc n))
    (.of_forall radialCutoff_tendsto) hi (by simpa only [neg_zero] using (radialCutoff_derivative_error hST).neg) hloc
  simpa only [q,Pi.neg_apply,integral_neg] using hout

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.weighted_convex_matrix_divergence
