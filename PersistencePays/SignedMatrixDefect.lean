import PersistencePays.MatrixGlobalIBP

/-! The actual combined signed matrix defect in Appendix A, equation (A.2).
The unfavorable splitting into identity and covariance fluctuation is avoided.
The favorable singular-Hessian contribution was proved in MatrixCutoff. -/
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology RealInnerProductSpace ContDiff
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem signed_matrix_defect
    {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {T : E → E} (he : T =ᵐ[volume] gradient φ)
    {G : E → E →L[ℝ] E} {s : Set E}
    (hs : volume sᶜ=0) (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,(G x).toLinearMap.IsPositive)
    {S : E → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (hSp : ∀ x,(S x).toLinearMap.IsPositive)
    (hST : Integrable (fun x => S x (T x)) volume)
    (hSx : Integrable (fun x => S x x) volume)
    (hdivT : Integrable (fun x => ⟪matrixDivergence S x,T x⟫) volume)
    (hdivx : Integrable (fun x => ⟪matrixDivergence S x,x⟫) volume)
    (htrace : Integrable (fun x => (S x).toLinearMap.trace ℝ E) volume) :
    Integrable (fun x => ((S x).comp (ContinuousLinearMap.id ℝ E-G x)).toLinearMap.trace ℝ E) volume ∧
    -(∫ x,⟪x-T x,matrixDivergence S x⟫) ≤
      ∫ x,((S x).comp (ContinuousLinearMap.id ℝ E-G x)).toLinearMap.trace ℝ E := by
  have hh := weighted_convex_matrix_divergence hφ he hs hG hd hpos hS hSp hST hdivT
  have heq (x:E) : ((S x).comp (ContinuousLinearMap.id ℝ E-G x)).toLinearMap.trace ℝ E =
      (S x).toLinearMap.trace ℝ E-((S x).comp (G x)).toLinearMap.trace ℝ E := by
    simp only [comp_sub,comp_id,toLinearMap_sub,map_sub]
  have hi : Integrable (fun x => ((S x).comp (ContinuousLinearMap.id ℝ E-G x)).toLinearMap.trace ℝ E) volume := by
    simp_rw [heq]
    exact htrace.sub hh.1
  refine ⟨hi,?_⟩
  have hidentity := identity_matrix_ibp hS (fun x => (hSp x).isSymmetric) hSx hdivx htrace
  have hl : (∫ x,⟪x-T x,matrixDivergence S x⟫)=
      (∫ x,⟪matrixDivergence S x,x⟫)-(∫ x,⟪matrixDivergence S x,T x⟫) := by
    rw [← integral_sub hdivx hdivT]
    apply integral_congr_ae
    filter_upwards with x
    rw [real_inner_comm,inner_sub_right]
  simp_rw [heq]
  rw [integral_sub htrace hh.1,hl]
  linarith [hh.2]

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.signed_matrix_defect
